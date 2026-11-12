"""Constants copied in several places, minimised together.

usage: groups.py [--screen] FILE

Some constants of the bounds are copied in definitions and in other
statements (the cost function [rec_cost] and its bound [step_bound], the
potential [C_pot] and its majorants, ...): they must change together. The
spec groups/<file>.json lists the places, as pairs [old, new] where [new]
is [old] with markers «name» (or «name+k», for the value of the group plus
k) in place of its literals; its pattern (markers: any literal) must occur
once in FILE. The groups are then lowered one at a time by a parallel
binary search, while the whole file compiles, and the markers are replaced
by the values found.

--screen  if no group can be lowered by one, stop at once
"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import minimise as M

HERE = os.path.dirname(os.path.abspath(__file__))
MARK = re.compile(r'«(\w+)(?:\+(\d+))?:(\d+)»')

def mark(s, spec):
    """[s] with the markers of [spec], their values taken from [s]."""
    for old, new in spec:
        parts = re.split(r'«(\w+(?:\+\d+)?)»', new)
        tmpl = '(\\d+)'.join(re.escape(x) for x in parts[0::2])
        ms = list(re.finditer(tmpl, s))
        if len(ms) != 1:
            raise SystemExit(f'groups: the pattern of {new!r} occurs {len(ms)} times')
        filled = new
        for name, v in zip(parts[1::2], ms[0].groups()):
            filled = filled.replace('«%s»' % name, '«%s:%s»' % (name, v), 1)
        s = s[:ms[0].start()] + filled + s[ms[0].end():]
    return s

def values(s):
    g = {}
    for m in MARK.finditer(s):
        g.setdefault(m.group(1), int(m.group(3)) - int(m.group(2) or 0))
    return g

def render(s, vals, keep):
    def rep(m):
        off = int(m.group(2) or 0); v = vals[m.group(1)] + off
        return '«%s%s:%d»' % (m.group(1), ('+%d' % off) if off else '', v) if keep else str(v)
    return MARK.sub(rep, s)

def main(argv):
    args = list(argv); screen = '--screen' in args
    args = [a for a in args if a != '--screen']
    if len(args) != 1: raise SystemExit(__doc__)
    path = args[0]
    full = os.path.join(M.REPO, 'theories', path)
    spec = json.load(open(os.path.join(HERE, 'groups', os.path.basename(path)[:-2] + '.json')))
    s = mark(open(full).read(), spec)
    vals = values(s); names = list(vals)
    print('groups', vals, flush=True)
    def feasible(cands):
        import concurrent.futures as cf
        with cf.ThreadPoolExecutor(M.JOBS) as ex:
            return list(ex.map(lambda v: M.compile_ok(render(s, v, False))[0], cands))
    ok, out = M.compile_ok(render(s, vals, False))
    if not ok:
        raise SystemExit('groups: the file does not compile with its constants:\n' + out[-3000:])
    if not (screen and not any(feasible([dict(vals, **{n: vals[n] - 1}) for n in names if vals[n] > 0]))):
        order = names
        vec = M.search(lambda cs: feasible([dict(zip(order, c)) for c in cs]), [vals[n] for n in order])
        vals = dict(zip(order, vec))
    print('final', vals, flush=True)
    open(full, 'w').write(render(s, vals, False))

if __name__ == '__main__':
    main(sys.argv[1:])
