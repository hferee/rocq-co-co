"""Snapshot of the complexity bounds of a source tree.

usage: extract.py [--root DIR] [--rev REV] OUT.jsonl

Reads the .v files under DIR/theories (default: the repository), or under
theories/ at the git revision REV, and writes one JSON object per bound:

  id         file (relative to theories/) and name: "stdlib/NatComplexity.v#Nat_add_complexity"
  kind       ComplexityBound, FirstOrderBound, Definition (cost functions) or Majorant
  model      Time, Space, or "" (generic)
  function   the function bounded
  template   the bound, its tunable literals replaced by {0}, {1}, ...
  constants  the values of these literals
  hyps       the premises of the statement, if any
  proof      "script", "term" or "none" (no proof: Abort)

The tunable literals are those of the minimiser (coqsrc.literal_positions):
the constants of a bound in two snapshots with the same template are
compared position by position.
"""
import json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coqsrc

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
CONFIG = json.load(open(os.path.join(HERE, 'config.json')))

def bounds_of(path, s):
    out = []
    m = coqsrc.mask_comments(s)
    for d in coqsrc.find_decls(s):
        fun, a, b = coqsrc.bound_span(s, d)
        pn = coqsrc.literal_positions(m, a, b, subtracted=True)
        tmpl, vals = coqsrc.template(m, a, b, [p for p, _ in pn])
        neg = [k for k, (_, n) in enumerate(pn) if n]
        hyps = ' '.join(m[d['start']:d['concl']].split())
        hyps = re.sub(r'^.*?\b(Instance|Lemma|Corollary|Theorem|Example)\s+[\w\']+\s*', '', hyps)
        out.append({'id': f'{path}#{d["name"]}', 'kind': d['bound_kind'], 'model': d['model'],
                    'function': fun, 'template': tmpl, 'constants': vals,
                    'hyps': hyps.rstrip(': ').strip(), 'proof': {'proof': 'script'}.get(d['kind'], d['kind']),
                    **({'negative': neg} if neg else {})})
    return out

def definitions_of(path, s):
    out = []
    m = coqsrc.mask_comments(s)
    for name in CONFIG['definitions'].get(path, []):
        for d in re.finditer(r'^[ \t]*(?:Fixpoint|Definition)[ \t]+%s\b' % re.escape(name), m, re.M):
            e = coqsrc.sentence_end(m, d.end())
            k = coqsrc.top_assign(m[d.end():e])
            a = d.end() + (k + 2 if k is not None else 0)
            pos = coqsrc.literal_positions(m, a, e - 1)
            tmpl, vals = coqsrc.template(m, a, e - 1, pos)
            out.append({'id': f'{path}#{name}', 'kind': 'Definition', 'model': '', 'function': name,
                        'template': tmpl, 'constants': vals, 'hyps': '', 'proof': 'term'})
    return out

def majorants_of(path, s):
    spec = CONFIG['majorants'].get(path)
    if not spec: return []
    out = []
    m = coqsrc.mask_comments(s)
    for x in re.finditer(spec, m, re.S):
        a, b = x.start(2), x.end(2)
        pos = coqsrc.literal_positions(m, a, b)
        tmpl, vals = coqsrc.template(m, a, b, pos)
        out.append({'id': f'{path}#{x.group(1)}', 'kind': 'Majorant', 'model': 'Time',
                    'function': x.group(1), 'template': tmpl, 'constants': vals, 'hyps': '',
                    'proof': 'script'})
    return out

def sources(root=None, rev=None):
    """(path relative to theories/, contents) of the .v files."""
    if rev is not None:
        files = subprocess.run(['git', 'ls-tree', '-r', '--name-only', rev, 'theories'], cwd=REPO,
                               capture_output=True, text=True, check=True).stdout.split()
        for f in sorted(files):
            if f.endswith('.v'):
                s = subprocess.run(['git', 'show', f'{rev}:{f}'], cwd=REPO, capture_output=True,
                                   text=True, check=True).stdout
                yield os.path.relpath(f, 'theories'), s
    else:
        base = os.path.join(root or REPO, 'theories')
        for dp, _, fs in sorted(os.walk(base)):
            for f in sorted(fs):
                if f.endswith('.v'):
                    p = os.path.join(dp, f)
                    yield os.path.relpath(p, base), open(p).read()

ABBREV = re.compile(r'^[ \t]*Abbreviation[ \t]+(\w+)[ \t]*:=[ \t]*(\d+)[ \t]*\(only parsing\)\.', re.M)

def expand_abbreviations(files):
    """The files with their numeric abbreviations ([Abbreviation c := 26 (only
    parsing)], constants shared by several bounds) replaced by their values:
    the templates are those of the numbers."""
    ab = {}
    for _, s in files:
        for m in ABBREV.finditer(s): ab[m.group(1)] = m.group(2)
    if not ab: return files
    pat = re.compile(r'(?<![\w.\'])(%s)(?![\w\'])' % '|'.join(map(re.escape, ab)))
    out = []
    for path, s in files:
        lines = s.split('\n')
        def expand(l):
            if ABBREV.match(l) or not pat.search(l): return l
            l = pat.sub(lambda m: ab[m.group(1)], l)
            return re.sub(r'\((\d+) \+ (\d+)\)', lambda m: str(int(m.group(1)) + int(m.group(2))), l)
        lines = [expand(l) for l in lines]
        out.append((path, '\n'.join(lines)))
    return out

def snapshot(root=None, rev=None):
    entries = []
    # older trees write [⋉] for [+>] and [c +> tt] for [c >|]
    files = [(p, coqsrc.normalise(s)) for p, s in sources(root, rev)]
    for path, s in expand_abbreviations(files):
        if any(path.startswith(x) for x in CONFIG['exclude']): continue
        entries += bounds_of(path, s) + definitions_of(path, s) + majorants_of(path, s)
    return entries

def main(argv):
    root = rev = None
    args = list(argv)
    while args and args[0].startswith('--'):
        o = args.pop(0)
        if o == '--root': root = args.pop(0)
        elif o == '--rev': rev = args.pop(0)
        else: raise SystemExit(__doc__)
    if len(args) != 1: raise SystemExit(__doc__)
    entries = snapshot(root, rev)
    with open(args[0], 'w') as f:
        for e in entries:
            f.write(json.dumps(e, ensure_ascii=False) + '\n')
    print(f'{len(entries)} bounds -> {args[0]}')

if __name__ == '__main__':
    main(sys.argv[1:])
