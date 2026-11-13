"""Minimise the constants of the complexity bounds of a Rocq file.

usage: minimise.py [--screen] [--start NAME] FILE [NAME...]

For each declaration of a bound of FILE (a path under theories/), in file
order, or only those named, the tunable literals of the bound
(coqsrc.literal_positions) are found from the inequalities that the proof
leaves when they are variables (goals.py): one compilation in export mode,
then one round that checks them, and that lowers each one by one. If this
does not conclude, or if a constant can still be lowered, they are scaled up
until the proof goes through, then lowered one at a time by a parallel
binary search, until none can be lowered. A candidate is checked by compiling the file up to the
declaration, with the candidate declaration. The proof script of the file is
kept when it works; otherwise variants of [cbound] are tried. The file is
rewritten with the constants found, and a report (JSON) is written in the
scratch directory.

--screen      a bound that holds, and in which no constant can be lowered by
              one, is kept as it is (fast, after a change of the compiler
              that only lowers costs)
--start NAME  start at the declaration NAME (after a failure fixed by hand)

The minimiser stops at the first declaration that it cannot prove: a later
declaration may depend on it. Declarations that copy the constants of
another one (e.g. derived by [exact]) must be updated by hand, or better,
refer to named constants. Only the file up to each declaration is checked:
build the whole file afterwards.

Environment: JOBS (parallel compilations, default 8), TIMEOUT (seconds per
compilation, default 150), ROCQ (the compiler, default rocq), BOUNDS_TMP
(scratch directory).
"""
import concurrent.futures as cf, itertools, json, os, re, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coqsrc, goals

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
JOBS = int(os.environ.get('JOBS', '8'))
TIMEOUT = int(os.environ.get('TIMEOUT', '150'))
ROCQ = os.environ.get('ROCQ', 'rocq')
SCRATCH = os.environ.get('BOUNDS_TMP', os.path.join(tempfile.gettempdir(), 'rocq-bounds'))
os.makedirs(SCRATCH, exist_ok=True)

COUNTER = itertools.count()

def compile_ok(src):
    """Whether [src] compiles against the built library."""
    i = next(COUNTER)
    base = os.path.join(SCRATCH, f'T{os.getpid()}_{i}')
    open(base + '.v', 'w').write(src)
    try:
        r = subprocess.run([ROCQ, 'compile', '-R', os.path.join(REPO, 'theories'), 'Complexity', base + '.v'],
                           cwd=SCRATCH, capture_output=True, text=True, timeout=TIMEOUT)
        ok, out = r.returncode == 0, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        ok, out = False, 'TIMEOUT'
    for ext in ['.v', '.vo', '.vok', '.vos', '.glob']:
        try: os.remove(base + ext)
        except FileNotFoundError: pass
    try: os.remove(os.path.join(SCRATCH, f'.T{os.getpid()}_{i}.aux'))
    except FileNotFoundError: pass
    return ok, out

ALT_SCRIPTS = ['Proof. cbound. Qed.',
               'Proof. cbound. all: try (lia || nia). Qed.',
               'Proof. intros. cbound. all: try (lia || nia). Qed.']

def instantiate(text, rel_pos, values):
    out = []; last = 0
    for (a, b), v in zip(rel_pos, values):
        out.append(text[last:a]); out.append(str(v)); last = b
    out.append(text[last:])
    return ''.join(out)

def search(feasible, vals):
    """Lower each constant of [vals] (feasible) by parallel binary search,
    until none can be lowered."""
    vals = list(vals)
    changed = True
    while changed:
        changed = False
        for i in range(len(vals)):
            lo, hi = 0, vals[i]
            while hi > lo:
                k = min(JOBS, hi - lo)
                pts = sorted(set(lo + (hi - lo) * j // (k + 1) for j in range(1, k + 1)) | {lo})
                pts = [p for p in pts if lo <= p < hi]
                res = feasible([vals[:i] + [p] + vals[i + 1:] for p in pts])
                good = [p for p, ok in zip(pts, res) if ok]
                bad = [p for p, ok in zip(pts, res) if not ok]
                if good:
                    nh = min(good)
                    below = [p for p in bad if p < nh]
                    lo = max(below) + 1 if below else lo
                    hi = nh
                else:
                    lo = max(pts) + 1
            if hi < vals[i]:
                vals[i] = hi; changed = True
    return vals

HEAD = re.compile(r"\s*(?:#\[[^\]]*\]\s*)?(?:Global\s+|Local\s+)?"
                  r"(?:Instance|Lemma|Corollary|Theorem|Example)\s+[\w']+")

ANALYSIS = re.compile(r'\b(?:cbound|cbound_core|cfinish|csize|csize_using|cproject|cweaken)\b')

def goal_values(prefix, decl, d, pos, close, vals0):
    """The constants from the inequalities that the proof leaves when they are
    variables (goals.py), or [None]."""
    names = [goals.KAPPA + str(i) for i in range(len(pos))]
    t = instantiate(decl, pos, names)
    m = HEAD.match(t)
    if not m: return None
    t = t[:m.end()] + ' (' + ' '.join(names) + ' : nat)' + t[m.end():]
    mm = coqsrc.mask_comments(t)
    e = coqsrc.sentence_end(mm, 0)
    head, rest = t[:e], t[e:]
    if d['kind'] == 'term':
        head = head[:coqsrc.top_assign(head)].rstrip() + '.'
        body = 'Proof. cbound_core.'
    else:
        body = re.sub(r'\b(Qed|Defined)\s*\.\s*$', '', rest.rstrip())
        # up to the analysis, which exports and admits the goals: what
        # follows it has nothing to work on
        a = ANALYSIS.search(coqsrc.mask_comments(body))
        if a:
            body = body[:coqsrc.sentence_end(coqsrc.mask_comments(body), a.end())]
    src = (prefix + 'Ltac2 Set cexport := Init.true.\nSet Printing Width 10000.\n' + head + '\n'
           + body + '\nAbort.\nLtac2 Set cexport := Init.false.\n' + close + '\n')
    ok, out = compile_ok(src)
    if not ok: return None
    return goals.solve(out, vals0)

def minimise_decl(s, d, screen):
    prefix = s[:d['start']]
    decl = s[d['start']:d['end']]
    close = coqsrc.closers(prefix)
    pos = [(a - d['start'], b - d['start']) for (a, b) in coqsrc.tunables(s, d)]
    vals0 = [int(decl[a:b]) for (a, b) in pos]
    scripts = [None] + ALT_SCRIPTS

    def make(values, script):
        t = instantiate(decl, pos, values)
        if script is not None:
            m = coqsrc.mask_comments(t)
            head = t[:coqsrc.sentence_end(m, 0)]
            if d['kind'] == 'term':
                head = head[:coqsrc.top_assign(head)].rstrip() + '.'
            t = head + '\n' + script
        return prefix + t + close + '\n'

    def feasible_with(script):
        def f(cands):
            with cf.ThreadPoolExecutor(JOBS) as ex:
                return list(ex.map(lambda vs: compile_ok(make(vs, script))[0], cands))
        return f

    entry = {'name': d['name'], 'before': vals0}
    if pos and not screen:
        g = goal_values(prefix, decl, d, pos, close, vals0)
        if g is not None:
            res = feasible_with(None)([g] + [g[:i] + [g[i] - 1] + g[i + 1:]
                                            for i in range(len(g)) if g[i] > 0])
            if res[0]:
                vals = g if not any(res[1:]) else search(feasible_with(None), g)
                new_decl = make(vals, None)[len(prefix):-len(close) - 1]
                return (s[:d['start']] + new_decl + s[d['end']:],
                        dict(entry, status='ok', after=vals, script=None, method='goals'))
    if screen and pos:
        res = feasible_with(None)([vals0] + [vals0[:i] + [vals0[i] - 1] + vals0[i + 1:]
                                             for i in range(len(vals0)) if vals0[i] > 0])
        if res[0] and not any(res[1:]):
            return s, dict(entry, status='ok', after=vals0, script=None, screened=True)
    for script in scripts:
        trials = [vals0]
        for _ in range(4): trials.append([2 * x + 4 for x in trials[-1]])
        res = feasible_with(script)(trials)
        found = next((t for t, ok in zip(trials, res) if ok), None)
        if found is not None: break
    else:
        return s, dict(entry, status='FAILED')
    vals = search(feasible_with(script), found) if pos else found
    new_decl = make(vals, script)[len(prefix):-len(close) - 1]
    return s[:d['start']] + new_decl + s[d['end']:], dict(entry, status='ok', after=vals, script=script)

def main(argv):
    args = list(argv); screen = False; start = None
    while args and args[0].startswith('--'):
        o = args.pop(0)
        if o == '--screen': screen = True
        elif o == '--start': start = args.pop(0)
        else: raise SystemExit(__doc__)
    if not args: raise SystemExit(__doc__)
    path, only = args[0], set(args[1:])
    full = os.path.join(REPO, 'theories', path) if not path.startswith('theories/') else os.path.join(REPO, path)
    s = open(full).read()
    rep = os.path.join(SCRATCH, os.path.basename(path) + '.report.json')
    old = json.load(open(rep)) if os.path.exists(rep) else []
    log = []
    idx = 0
    while True:
        decls = [d for d in coqsrc.find_decls(s) if d['kind'] != 'none']
        if idx >= len(decls): break
        d = decls[idx]; idx += 1
        if only and d['name'] not in only: continue
        if start:
            if d['name'] != start: continue
            start = None
        print('...', d['name'], flush=True)
        s, entry = minimise_decl(s, d, screen)
        log.append(entry)
        print('   ', entry, flush=True)
        open(full, 'w').write(s)
        names = {e['name'] for e in log}
        json.dump([e for e in old if e['name'] not in names] + log, open(rep, 'w'), indent=1)
        if entry['status'] == 'FAILED':
            print('STOPPING: fix', d['name'], 'by hand, then use --start', d['name'], flush=True)
            sys.exit(2)
    print('report', rep)

if __name__ == '__main__':
    main(sys.argv[1:])
