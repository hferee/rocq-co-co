"""The constants of a bound, from the inequalities that [cbound] leaves.

This is what one does by hand: write the bound with unknown constants, run
[cbound], and read the inequalities that it leaves. The minimiser
(minimise.py) makes the tunable constants of a bound variables [κ0], [κ1],
..., and runs its proof in export mode ([cexport], TimeCombinators): the
inequalities left are printed instead of being given to [lia]. This module
reads them and finds the constants.

For fixed values of the other atoms of an inequality (the values and
lengths of the arguments, the costs of the functional arguments, ...), each
inequality is linear in the constants: the claimed bound is linear in them,
and so is the cost of the recursive calls, which is the claimed bound. The
inequality holds for all values of the atoms (natural numbers) as soon as,
grouped by monomials of the atoms, each coefficient is nonnegative: a
system of linear inequalities in the constants. It is solved for the
smallest constants, one at a time, in their order in the bound, until none
can be lowered, as the binary search does. A subtraction [a - b] is read as
an exact one, and adds the inequality [b <= a].

The grouping by monomials ignores the relations between the atoms. A
hypothesis [a < x] or [a <= x], for an atom [x] (such as a size, [n < #|n|]),
is used by replacing [x] by [a + 1 + s] (or [a + s]), for a new atom [s].
The constants found are then checked by Rocq, with the proof of the file,
and each one lowered by one (minimise.py): if one can be lowered (a relation
that the grouping missed), the binary search goes on from them.

[solve] returns [None] when it cannot conclude: an inequality that is not
linear in the constants, a constant inside an atom (as an argument of a
function), a goal that is not an inequality, or no solution.
"""
import itertools

KAPPA = 'κ'


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------- parsing

def tokens(s):
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c in '()':
            yield c; i += 1
        elif c == '{':
            d, j = 0, i
            while j < n:
                if s[j] == '{': d += 1
                elif s[j] == '}':
                    d -= 1
                    if d == 0: break
                j += 1
            yield ('atom', ' '.join(s[i + 1:j].split())); i = j + 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in '(){}': j += 1
            yield s[i:j]; i = j


def parse(s):
    toks = list(tokens(s))
    pos = 0

    def expr():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == '(':
            op = toks[pos]; pos += 1
            args = []
            while toks[pos] != ')':
                args.append(expr())
            pos += 1
            return (op, *args)
        if isinstance(t, tuple):
            return t
        if t.isdigit():
            return ('num', int(t))
        raise Unsupported('token ' + t)

    e = expr()
    if pos != len(toks): raise Unsupported('trailing tokens')
    return e


# ------------------------------------------------------------- polynomials
# A polynomial: {monomial: coefficient}, a monomial being a sorted tuple of
# atoms (with repetitions).

def padd(p, q, k=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + k * c
        if r[m] == 0: del r[m]
    return r


def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            r[m] = r.get(m, 0) + c1 * c2
            if r[m] == 0: del r[m]
    return r


def const(n):
    return {(): n} if n else {}


def atom(a):
    return {(a,): 1}


def expand(e, side):
    """The polynomial of [e]; the subtractions [a - b] add [(a, b)] to
    [side] (to hold: [b <= a])."""
    op = e[0]
    if op == 'num': return const(e[1])
    if op == 'atom':
        a = e[1]
        if KAPPA in a and not is_kappa(a): raise Unsupported('constant in an atom: ' + a)
        return atom(a)
    if op == '+': return padd(expand(e[1], side), expand(e[2], side))
    if op == '*': return pmul(expand(e[1], side), expand(e[2], side))
    if op == '-':
        a, b = expand(e[1], side), expand(e[2], side)
        side.append((a, b))
        return padd(a, b, -1)
    raise Unsupported('operator ' + op)


def is_kappa(a):
    return a.startswith(KAPPA) and a[1:].isdigit()


def subst(p, x, q):
    """[p] with the atom [x] replaced by the polynomial [q]."""
    r = {}
    for m, c in p.items():
        k = m.count(x)
        rest = tuple(a for a in m if a != x)
        t = {rest: c}
        for _ in range(k): t = pmul(t, q)
        r = padd(r, t)
    return r


# -------------------------------------------------------------- constraints

def linear_constraints(p):
    """[p >= 0] for all nonnegative atoms, as constraints on the constants:
    each one a dict {constant or None: coefficient}, meaning [sum >= 0]."""
    groups = {}
    for m, c in p.items():
        ks = [a for a in m if is_kappa(a)]
        if len(ks) > 1: raise Unsupported('not linear in the constants')
        rest = tuple(a for a in m if not is_kappa(a))
        g = groups.setdefault(rest, {})
        k = ks[0] if ks else None
        g[k] = g.get(k, 0) + c
    return [g for g in groups.values() if any(g.values())]


def read_export(out):
    """The goals of an export: lists of (hypotheses, goal), each a relation
    (op, lhs, rhs) in s-expressions; [None] for a goal of another form."""
    goals, cur = [], None
    for line in out.splitlines():
        line = line.strip()
        if line == '#CGOAL': cur = ([], None)
        elif line.startswith('#H ') and cur is not None: cur[0].append(line[3:])
        elif line.startswith('#G ') and cur is not None: cur = (cur[0], line[3:])
        elif line.startswith('#X ') and cur is not None: cur = (cur[0], 'X')
        elif line == '#END' and cur is not None:
            goals.append(cur); cur = None
    return goals


def relation(s):
    e = parse(s)
    if e[0] not in ('<=', '<', '='): raise Unsupported('relation ' + e[0])
    return e


def substitutions(hyps):
    """For each atom [x] bounded below by a hypothesis [a < x] or [a <= x]
    ([a] without constants), the possible replacements of [x]."""
    cands = {}
    for i, h in enumerate(hyps):
        try:
            op, l, r = relation(h)
        except Unsupported:
            continue
        if op == '=' or r[0] != 'atom' or is_kappa(r[1]): continue
        try:
            lp = expand(l, [])
        except Unsupported:
            continue
        if any(is_kappa(a) for m in lp for a in m): continue
        q = padd(lp, padd(const(1 if op == '<' else 0), atom('σ%d' % i)))
        cands.setdefault(r[1], []).append(q)
    return cands


def goal_constraints(hyps, goal):
    """The constraints of one goal, for each choice of the replacements."""
    if goal is None or goal == 'X': raise Unsupported('not an inequality')
    op, l, r = relation(goal)
    side = []
    lp, rp = expand(l, side), expand(r, side)
    ineqs = []
    if op == '<=': ineqs.append(padd(rp, lp, -1))
    elif op == '<': ineqs.append(padd(padd(rp, lp, -1), const(-1)))
    else: ineqs += [padd(rp, lp, -1), padd(lp, rp, -1)]
    ineqs += [padd(a, b, -1) for a, b in side]
    cands = substitutions(hyps)
    atoms = [x for x in cands if any(x in m for p in ineqs for m in p)]
    choices = []
    for combo in itertools.islice(itertools.product(*[cands[x] for x in atoms]), 16):
        cs = []
        for p in ineqs:
            for x, q in zip(atoms, combo): p = subst(p, x, q)
            cs += linear_constraints(p)
        choices.append(cs)
    return choices


# ------------------------------------------------------------------ solving

def holds(cons, vals):
    return all(g.get(None, 0) + sum(c * vals[k] for k, c in g.items() if k is not None) >= 0
               for g in cons)


def raise_to(cons, names, vals):
    """A solution above [vals]: each violated inequality raises the last
    constant with a positive coefficient (the slopes come after the
    constants of the partial applications, which they must exceed)."""
    vals = dict(vals)
    for _ in range(1000):
        bad = [g for g in cons if g.get(None, 0) + sum(c * vals[k] for k, c in g.items() if k is not None) < 0]
        if not bad: return vals
        g = bad[0]
        pos = [k for k in names if g.get(k, 0) > 0]
        if not pos: return None
        k = pos[-1]
        rest = g.get(None, 0) + sum(c * vals[j] for j, c in g.items() if j not in (None, k))
        vals[k] = max(vals[k], -(rest // g[k]))
    return None


def lower(cons, names, vals):
    """Lower each constant in turn to the smallest value with the others
    fixed, until none changes."""
    vals = dict(vals)
    changed = True
    while changed:
        changed = False
        for k in names:
            lo = 0
            for g in cons:
                a = g.get(k, 0)
                if a > 0:
                    rest = g.get(None, 0) + sum(c * vals[j] for j, c in g.items() if j not in (None, k))
                    lo = max(lo, -(rest // a))       # ceil(-rest / a)
            if lo < vals[k]:
                vals[k] = lo; changed = True
    return vals


def solve(out, start):
    """The constants [κ0 ..] (a list, in order) from the export [out], from
    the feasible or not [start]; [None] if it cannot conclude."""
    names = [KAPPA + str(i) for i in range(len(start))]
    try:
        goals = read_export(out)
        if not goals: return None
        per_goal = [goal_constraints(h, g) for h, g in goals]
    except (Unsupported, IndexError, ValueError):
        return None
    best = None
    for choice in itertools.islice(itertools.product(*per_goal), 64):
        cons = [c for cs in choice for c in cs]
        if any(k is not None and k not in names for g in cons for k in g): return None
        # a constraint without constants must hold
        if any(set(g) <= {None} and g.get(None, 0) < 0 for g in cons): continue
        vals = dict(zip(names, start))
        t = 0
        while not holds(cons, vals) and t < 12:
            vals = {k: 2 * v + 4 for k, v in vals.items()}; t += 1
        if not holds(cons, vals):
            vals = raise_to(cons, names, dict(zip(names, start)))
        if vals is None or not holds(cons, vals): continue
        vals = lower(cons, names, vals)
        v = [vals[k] for k in names]
        if best is None or v < best: best = v
    return best
