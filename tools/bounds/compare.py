"""Comparison of snapshots of complexity bounds.

usage: compare.py [options] RUN...

  RUN                   names of runs of bounds/runs.json, in column order
  --base RUN            the run of the last column's comparison (default: the first)
  --format md|csv|html  output format (default: md)
  --cells vector|formula
                        cells: the constants of the template of the row
                        (default), or the bound itself
  --changed-only        only the rows that differ between the runs
  --header FILE         text put before the tables (md and html)
  -o FILE               output file (default: standard output)

Each row is a bound. Its template (the bound with its constants numbered
①, ②, ...) is shown once; each run gives the values of the constants. A run
whose bound has another shape gives the bound itself, marked "(shape)". The
last column compares the base run with the last one: ↓ every constant
lower or equal, ↑ every constant higher or equal, ↕ mixed, = unchanged. In
md and html, a cell that differs from the previous run is in bold.

The long format (csv) has one line per run, bound and constant, for
spreadsheets.
"""
import csv, html, io, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
CONFIG = json.load(open(os.path.join(HERE, 'config.json')))
RUNS_DIR = os.path.join(REPO, 'bounds')

def load_manifest():
    return {r['name']: r for r in json.load(open(os.path.join(RUNS_DIR, 'runs.json')))}

def load_run(name):
    with open(os.path.join(RUNS_DIR, 'runs', name + '.jsonl')) as f:
        return {e['id']: e for e in map(json.loads, f)}

# ---------------------------------------------------------------- display

CIRCLED = '①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳'

def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        d = 0
        for i, c in enumerate(s):
            if c == '(': d += 1
            elif c == ')':
                d -= 1
                if d == 0 and i != len(s) - 1: return s
        s = s[1:-1].strip()
    return s

SHORT = [
    (r'let r := match q with xH => a \| xO q\' \| xI q\' => rec_pos a F h q\' end in '
     r'cost \(pF \(Npos q ⋊ tt\)\) \+ cost \(res \(pF \(Npos q ⋊ tt\)\) \(r ⋊ tt\)\) \+ cost \(ph \(Npos q ⋊ tt\)\) ',
     'costs of F, h '),
    (r'Nat\.min \(N\.size_nat \(F \(Npos q\) r\)\) \(N\.size_nat \(h \(Npos q\)\)\)', 'min |F q r| |h q|'),
    (r'match q with xH => (\{\d+\}) \| xO q\' \| xI q\' => (\{\d+\}) \+ rec_cost a F h pF ph q\' end',
     r'(\1 on the last bit | \2 + rec_cost … q′)'),
    (r'^bF n \(Nat\.max \(N\.size_nat a\) \(lh n\)\) \+ bh n', 'bF … + bh n'),
    (r'cost \(pF \(C x ⋊ C_pot x\)\) \+ cost \(pF \(zero ⋊ zero_pot\)\)', 'costs of F'),
    (r'\(F \(C x\) =\? F zero\)%N', 'F (C x) = F zero'),
    (r'N\.size_nat \(val cy\)', '|y|'),
    (r'N\.size_nat \(F \(C x\)\)', '|F (C x)|'),
]

def simplify(b):
    """A bound, as in the comparison table: values [val cn] as [n], lengths
    as [|x|], sizes as [#|x|]."""
    b = re.sub(r'\s*\|\s*0\s*$', '', b.strip())            # instance priority
    for a, c in SHORT:
        b = re.sub(a, c, b)
    b = strip_parens(b)
    b = re.sub(r'\bval c(\w+)', r'\1', b)
    b = re.sub(r'\bpot c(\w+)', r'pot \1', b)
    b = re.sub(r'\bfun \(c(\w+) : ℂI (?:\([^()]*\)|\S+) _\) =>', r'fun c\1 =>', b)   # typed binders
    b = re.sub(r'\bfun lc =>', r'λl.', b)
    b = re.sub(r'\bfun c(\w+) =>', r'λ\1.', b)
    b = re.sub(r'\bfun (\w+) =>', r'λ\1.', b)
    b = re.sub(r'λ (\w+(?: \w+)*),', lambda m: 'λ' + m.group(1).replace(' ', ' λ') + '.', b)
    for _ in range(3):
        b = re.sub(r'\((\w+)\)', r'\1', b)
        b = re.sub(r'\b(?:N|Pos)\.size_nat (\w+)\b', r'|\1|', b)
        b = re.sub(r'\blength (\w+)\b', r'|\1|', b)
    b = re.sub(r'\s*⋉ tt\b', '', b)
    b = b.replace('List.nth 0 ss 0', 's₀').replace('List.nth 1 ss 0', 's₁')
    b = re.sub(r'(\{\d+\}|\d+) \* ', r'\1·', b)
    b = re.sub(r'(\|\w+\|) \* ', r'\1·', b)
    return b

def show_template(t):
    return re.sub(r'\{(\d+)\}', lambda m: CIRCLED[int(m.group(1))] if int(m.group(1)) < 20
                  else '{%s}' % m.group(1), simplify(t))

def instantiate(t, vals):
    return simplify(re.sub(r'\{(\d+)\}', lambda m: str(vals[int(m.group(1))]), t))

def fun_name(e):
    name = e['id'].split('#')[1]
    name = re.sub(r'_size_complexity$', '_complexity', name)
    if name in CONFIG['names']: return CONFIG['names'][name]
    f = strip_parens(e['function'])
    f = re.sub(r'^@(\S+)(?: \w+)*$', r'\1', f)
    return name if len(f) > 28 else f

def renumber(t):
    """[t] with its placeholders numbered in order."""
    k = iter(range(1000))
    return re.sub(r'\{\d+\}', lambda m: '{%d}' % next(k), t)

def align(big, small):
    """The constants of [small] in the positions of [big], when [small] is
    [big] with constants 0: a [+ {k}] removed, or a placeholder written 0.
    None if the shapes differ otherwise."""
    tb, ts = big['template'], small['template']
    ks = [int(x) for x in re.findall(r'\{(\d+)\}', tb)]
    n = len(ks) - len(re.findall(r'\{\d+\}', ts))
    if n <= 0 or n > 2: return None
    import itertools
    for drop in itertools.combinations(range(len(ks)), n):
        for forms in itertools.product([' + {%d}', '{%d}'], repeat=n):
            t = tb
            for k, form in zip(drop, forms):
                t = t.replace(form % k, '' if form.startswith(' +') else '0', 1)
            if renumber(t) == renumber(ts):
                it = iter(small['constants'])
                return [0 if k in drop else next(it) for k in range(len(ks))]
    return None

def comparable(a, b):
    """The constants of [a] and [b] in the same positions, or None."""
    if a['template'] == b['template']: return a['constants'], b['constants']
    x = align(a, b)
    if x is not None: return a['constants'], x
    y = align(b, a)
    if y is not None: return y, b['constants']
    return None

def direction(a, b):
    if a is None or b is None: return ''
    c = comparable(a, b)
    if c is None: return ''
    x, y = c
    neg = set(b.get('negative', [])) if a['template'] == b['template'] else set()
    x = [-v if k in neg else v for k, v in enumerate(x)]
    y = [-v if k in neg else v for k, v in enumerate(y)]
    if x == y: return '='
    if all(p >= q for p, q in zip(x, y)): return '↓'
    if all(p <= q for p, q in zip(x, y)): return '↑'
    return '↕'

# ---------------------------------------------------------------- rows

def rows_of(runs, data, changed_only):
    ids = []
    for r in runs:
        for i in data[r]:
            if i not in ids: ids.append(i)
    rows = []
    for i in ids:
        es = [data[r].get(i) for r in runs]
        present = [e for e in es if e is not None]
        last = present[-1]
        # the most general shape: the others are it with constants 0
        ref = max(reversed(present), key=lambda e: (len(e['constants'])
                  if e is last or comparable(e, last) is not None else -1))
        if changed_only and all(e is not None and e['template'] == ref['template']
                                and e['constants'] == ref['constants'] for e in es):
            continue
        rows.append((i, ref, es))
    return rows

def cell(e, ref, mode):
    if e is None: return '—'
    if mode == 'formula': return instantiate(e['template'], e['constants'])
    vals = e['constants']
    if e['template'] != ref['template']:
        c = comparable(ref, e)
        if c is None or len(c[1]) != len(ref['constants']):
            return instantiate(e['template'], e['constants']) + ' (shape)'
        vals = c[1]
    return ', '.join(map(str, vals)) if vals else '·'

def label(i, e):
    name = fun_name(e)
    key = i.split('#')[1]
    extra = []
    if e['kind'] == 'FirstOrderBound' or key.endswith('_size_complexity'): extra.append('in the sizes')
    if e['kind'] in ('Definition', 'Majorant'): extra.append(e['kind'].lower())
    if e['model'] == 'Space': extra.append('space')
    if '_tz_' in key: extra.append('amortised, in the trailing zeros')
    elif key.endswith('_linear_complexity'): extra.append('amortised')
    if key in CONFIG['notes']: extra.append(CONFIG['notes'][key])
    return name, extra

def sections(rows):
    out = []
    for title, prefix in CONFIG['sections']:
        rs = [r for r in rows if r[0].startswith(prefix)]
        if rs: out.append((title, rs))
    return out

# ---------------------------------------------------------------- formats

def md(runs, man, rows, base, mode, header):
    bi = runs.index(base)
    out = [header] if header else []
    head = '| Function | Bound | ' + ' | '.join(man[r].get('title', r) for r in runs) + f' | {base} → {runs[-1]} |'
    sep = '|---|---|' + '---|' * len(runs) + '---|'
    for title, rs in sections(rows):
        out.append(f'\n## {title}\n')
        cur = None
        for i, ref, es in rs:
            f = i.split('#')[0]
            if f != cur:
                cur = f
                out.append(f'\n### [{f.split("/")[-1]}](theories/{f})\n')
                out.append(head); out.append(sep)
            name, extra = label(i, ref)
            cells, prev = [], None
            for e in es:
                c = cell(e, ref, mode)
                txt = '`' + c.replace('|', '\\|') + '`' if c not in ('—', '·') else c
                if prev is not None and e is not None and prev is not None and \
                        (e['template'], e['constants']) != (prev['template'], prev['constants']):
                    txt = '**' + txt + '**'
                cells.append(txt); prev = e if e is not None else prev
            n = '`' + name.replace('|', '\\|') + '`' + (' (' + '; '.join(extra) + ')' if extra else '')
            out.append(f'| {n} | `{show_template(ref["template"]).replace("|", chr(92) + "|")}` | '
                       + ' | '.join(cells) + f' | {direction(es[bi], es[-1])} |')
    return '\n'.join(out) + '\n'

def long_csv(runs, rows):
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(['id', 'run', 'kind', 'model', 'function', 'template', 'index', 'value'])
    for i, ref, es in rows:
        for r, e in zip(runs, es):
            if e is None: continue
            for k, v in enumerate(e['constants']):
                w.writerow([i, r, e['kind'], e['model'], e['function'], e['template'], k, v])
    return buf.getvalue()

def page(runs, man, rows, base, mode, header):
    bi = runs.index(base)
    h = html.escape
    out = ['<!DOCTYPE html><html><head><meta charset="utf-8"><title>Complexity bounds</title><style>',
           'body{font-family:sans-serif;margin:1em} table{border-collapse:collapse;font-size:13px}',
           'th,td{border:1px solid #ccc;padding:2px 6px;white-space:nowrap} th{position:sticky;top:0;background:#eee}',
           'td:first-child,th:first-child{position:sticky;left:0;background:#fafafa}',
           'code{font-family:monospace} .dn{background:#dfd} .up{background:#fdd} .mx{background:#ffd}',
           '</style></head><body>']
    if header: out.append('<pre>' + h(header) + '</pre>')
    out.append('<p>Filter: <input id="q" oninput="f()"></p>')
    out.append('<table id="t"><tr><th>Function</th><th>Bound</th>' + ''.join(
        f'<th title="{h(man[r].get("description", ""))}">{h(man[r].get("title", r))}</th>' for r in runs)
        + f'<th>{h(base)} → {h(runs[-1])}</th></tr>')
    for title, rs in sections(rows):
        out.append(f'<tr><th colspan="{len(runs) + 3}" style="text-align:left">{h(title)}</th></tr>')
        for i, ref, es in rs:
            name, extra = label(i, ref)
            tds, prev = [], None
            for e in es:
                d = direction(prev, e) if prev is not None else ''
                cls = {'↓': 'dn', '↑': 'up', '↕': 'mx'}.get(d, '')
                tds.append(f'<td class="{cls}"><code>{h(cell(e, ref, mode))}</code></td>')
                prev = e if e is not None else prev
            out.append(f'<tr><td title="{h(i)}"><code>{h(name)}</code> {h("; ".join(extra))}</td>'
                       f'<td><code>{h(show_template(ref["template"]))}</code></td>' + ''.join(tds)
                       + f'<td>{direction(es[bi], es[-1])}</td></tr>')
    out.append('</table><script>function f(){var q=document.getElementById("q").value.toLowerCase();'
               'for(var r of document.querySelectorAll("#t tr"))if(r.querySelector("td"))'
               'r.style.display=r.textContent.toLowerCase().includes(q)?"":"none"}</script></body></html>')
    return '\n'.join(out)

def main(argv):
    args = list(argv); opts = {'format': 'md', 'cells': 'vector', 'base': None, 'header': None, 'o': None,
                               'changed': False}
    runs = []
    while args:
        a = args.pop(0)
        if a == '--format': opts['format'] = args.pop(0)
        elif a == '--cells': opts['cells'] = args.pop(0)
        elif a == '--base': opts['base'] = args.pop(0)
        elif a == '--header': opts['header'] = args.pop(0)
        elif a == '--changed-only': opts['changed'] = True
        elif a == '-o': opts['o'] = args.pop(0)
        elif a.startswith('-'): raise SystemExit(__doc__)
        else: runs.append(a)
    if not runs: raise SystemExit(__doc__)
    man = load_manifest()
    for r in runs:
        if r not in man: raise SystemExit(f'unknown run {r}: see bounds/runs.json')
    data = {r: load_run(r) for r in runs}
    base = opts['base'] or runs[0]
    rows = rows_of(runs, data, opts['changed'])
    header = open(opts['header']).read() if opts['header'] else ''
    if opts['format'] == 'md': out = md(runs, man, rows, base, opts['cells'], header)
    elif opts['format'] == 'csv': out = long_csv(runs, rows)
    elif opts['format'] == 'html': out = page(runs, man, rows, base, opts['cells'], header)
    else: raise SystemExit(__doc__)
    if opts['o']: open(opts['o'], 'w').write(out)
    else: sys.stdout.write(out)

if __name__ == '__main__':
    main(sys.argv[1:])
