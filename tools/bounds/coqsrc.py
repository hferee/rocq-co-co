"""Reading the complexity bounds of Rocq sources.

Shared by the extraction of snapshots (extract.py), their comparison
(compare.py) and the minimisation of constants (minimise.py): the same
declarations and the same tunable literals everywhere, so that the constants
of a bound in two snapshots can be compared position by position.
"""
import re

def normalise(s):
    """[s] in the current notations: [⋉] (older trees) is [+>], and the end
    of a bound [c +> tt] is [c >|]. Applied to the sources before they are
    read, and to the templates of the snapshots when they are loaded, so
    that the snapshots of all versions compare."""
    return re.sub(r'\s*\+>\s*tt\b', ' >|', s.replace('⋉', '+>'))

def mask_comments(s):
    """[s] with its comments replaced by spaces (newlines kept)."""
    out = list(s); i = 0; n = len(s)
    while i < n:
        if s.startswith('(*', i):
            d = 0; j = i
            while j < n:
                if s.startswith('(*', j): d += 1; j += 2; continue
                if s.startswith('*)', j):
                    d -= 1; j += 2
                    if d == 0: break
                    continue
                j += 1
            for k in range(i, j):
                if out[k] != '\n': out[k] = ' '
            i = j
        else:
            i += 1
    return ''.join(out)

def sentence_end(m, i):
    """Index just after the '.' ending the sentence that starts at [i]
    ([m]: masked source)."""
    depth = 0; n = len(m)
    while i < n:
        c = m[i]
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        elif c == '.' and depth <= 0 and (i + 1 == n or m[i + 1] in ' \n\t'):
            return i + 1
        i += 1
    raise ValueError('no end of sentence')

def top_assign(stmt):
    """Position of a ':=' outside parentheses, or None."""
    depth = 0
    for i, c in enumerate(stmt):
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        elif c == ':' and depth == 0 and stmt.startswith(':=', i):
            return i
    return None

DECL = re.compile(r'^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:Global[ \t]+|Local[ \t]+)?'
                  r'(Instance|Lemma|Corollary|Theorem|Example)[ \t]+([\w\']+)', re.M)
KIND = re.compile(r'((?:Time|Space|Machine)\.)?(ComplexityBound|FirstOrderBound)\b')

def find_decls(s):
    """The declarations of bounds of [s]: name, kind, positions of the
    statement and of the end of the proof."""
    m = mask_comments(s)
    decls = []
    for d in DECL.finditer(m):
        e = sentence_end(m, d.end())
        stmt = m[d.end():e]
        k = top_assign(stmt)
        head = stmt if k is None else stmt[:k]
        ks = list(KIND.finditer(head))
        if not ks:
            continue
        if k is not None:
            proof_end, kind = e, 'term'
        else:
            pm = re.compile(r'\s*Proof\b').match(m, e)
            if pm:
                q = re.compile(r'\b(Qed|Defined|Admitted)\s*\.').search(m, pm.end())
                proof_end, kind = q.end(), 'proof'
            else:
                proof_end, kind = e, 'none'      # e.g. Abort, or a Fail
        last = ks[-1]
        decls.append({'name': d.group(2), 'start': d.start(), 'stmt_end': e, 'end': proof_end,
                      'kind': kind, 'bound_kind': last.group(2),
                      'model': (last.group(1) or '').rstrip('.'),
                      'concl': d.end() + last.start(), 'concl_kw_end': d.end() + last.end(),
                      'stmt_text_end': d.end() + (len(stmt) - 1 if k is None else k)})
    return decls

def skip_arg(text, j):
    """Index after the argument of [text] starting at [j] (a parenthesised
    term or a token)."""
    while j < len(text) and text[j] in ' \n\t': j += 1
    if j < len(text) and text[j] == '(':
        depth = 0
        while j < len(text):
            if text[j] == '(': depth += 1
            elif text[j] == ')':
                depth -= 1
                if depth == 0: return j + 1
            j += 1
        return j
    while j < len(text) and text[j] not in ' \n\t': j += 1
    return j

LIT = re.compile(r'(?<![\w.\'%#])(\d+)(?![\w.\'%])')

def literal_positions(m, a, b, subtracted=False):
    """Positions of the tunable literals of [m[a:b]]: not 0, not exponents,
    not subtracted (unless [subtracted]: then the pairs (position, whether
    subtracted)), not indices of [List.nth], not under [S]."""
    pos = []
    for x in LIT.finditer(m, a, b):
        i, j = x.start(), x.end()
        before = m[max(0, i - 8):i]; after = m[j:j + 8]
        if x.group(1) == '0': continue
        if re.search(r'\^\s*$', before) or re.match(r'\s*\^', after): continue
        neg = bool(re.search(r'-\s*$', before))
        if neg and not subtracted: continue
        if re.search(r'nth\s*$', before) or re.match(r'\s*ss\b', after): continue
        if re.search(r'S\s*\(?\s*$', before): continue
        pos.append(((i, j), neg) if subtracted else (i, j))
    return pos

def bound_span(s, d):
    """The function and the bound of the declaration [d]: (function text,
    start and end of the bound in [s])."""
    m = mask_comments(s)
    a = d['concl_kw_end']
    f_end = skip_arg(m, a)
    return ' '.join(m[a:f_end].split()), f_end, d['stmt_text_end']

def tunables(s, d):
    """Positions (absolute) of the tunable literals of the bound of [d]."""
    m = mask_comments(s)
    _, a, b = bound_span(s, d)
    return literal_positions(m, a, b)

def template(s, a, b, pos):
    """[s[a:b]] with the literals at [pos] replaced by [{0}], [{1}], ...:
    the shape of a bound, and its constants."""
    out, last, vals = [], a, []
    for k, (i, j) in enumerate(pos):
        out.append(s[last:i]); out.append('{%d}' % k); vals.append(int(s[i:j])); last = j
    out.append(s[last:b])
    t = ' '.join(''.join(out).split())
    t = re.sub(r' \+ 0(?=\s*\)|\s*$)', '', t)      # a constant term 0 is no term
    return t, vals

def closers(prefix):
    """The [End]s that close the modules and sections open at the end of
    [prefix]."""
    m = mask_comments(prefix)
    stack = []
    for line in m.splitlines():
        t = line.strip()
        mm = re.match(r'(Module|Section)\s+(\w+)', t)
        if mm and not re.match(r'Module\s+Type\b', t) and ':=' not in t \
                and not t.startswith('Module Import'):
            stack.append(mm.group(2)); continue
        me = re.match(r'End\s+(\w+)\s*\.', t)
        if me and stack and stack[-1] == me.group(1):
            stack.pop()
    return ''.join(f'\nEnd {x}.' for x in reversed(stack))
