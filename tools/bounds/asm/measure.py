"""The x86-64 instruction counts of some functions of the library, as a run.

usage: measure.py [RUN]          (default RUN: asm)

The functions (Ex.v) are extracted to OCaml, as they are defined in the
standard library, and compiled with ocamlopt without optimisation
(-inline 0; ocamlopt without flambda does not optimise further). The
instructions executed are counted by single-stepping the program (icount.c,
ptrace), for inputs of two sizes, with and without the call: the
differences give the instructions per element and the constant, exactly
(the minor heap is large enough that no collection happens, and the addresses
are not randomised). The run is
written to bounds/runs/RUN.jsonl, and added to the manifest as a
reference run: the table shows it, but does not compare the bounds with it
(compare.py), and bounds-check ignores it.

The constants are those of the bound of the library with the same shape
when there is one, with [0] for the partial applications, which a
saturated call does not build. Otherwise the run gives its own formula,
for the inputs measured (see DESCRIPTION).
"""
import json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
ROCQ = os.environ.get('ROCQ', 'rocq')
WORK = os.path.join(os.environ.get('BOUNDS_TMP', os.path.join(tempfile.gettempdir(), 'rocq-bounds')), 'asm')
SIZES = (200, 300)

DESCRIPTION = (
    "x86-64 instructions executed by the functions extracted to OCaml (ocamlopt 5.4, -inline 0, "
    "no flambda), counted by single-stepping (tools/bounds/asm). Nat.add and Nat.mul: the second "
    "argument of size 3 (Nat.mul: 10 and 20, for its two coefficients); app: the second list of length 3; "
    "Pos.add and Pos.compare: two numbers of n bits, all 1; map: f = fun x => S x; fold_left: "
    "f = fun a _ => S a, from 0 (the costs of f included). Partial applications: 0 (the calls are "
    "saturated). The constants include the call from the measuring program.")


def sh(cmd, **kw):
    r = subprocess.run(cmd, cwd=WORK, capture_output=True, text=True, **kw)
    if r.returncode:
        raise SystemExit(' '.join(cmd) + ' failed:\n' + r.stdout + r.stderr)
    return r.stdout


def build():
    os.makedirs(WORK, exist_ok=True)
    for f in ('Ex.v', 'main.ml', 'icount.c'):
        shutil.copy(os.path.join(HERE, f), WORK)
    sh([ROCQ, 'compile', 'Ex.v'])
    sh(['gcc', '-O2', '-o', 'icount', 'icount.c'])
    sh(['ocamlopt', '-inline', '0', '-o', 'prog', 'fns.mli', 'fns.ml', 'main.ml'])


def count(fn, n, mode):
    """The median of five counts: the start-up of the OCaml runtime varies by a
    few instructions from one run to the next (a time read)."""
    env = dict(os.environ, OCAMLRUNPARAM='s=8M')
    cs = sorted(int(sh(['./icount', './prog', fn, str(n), mode], env=env).strip()) for _ in range(5))
    return cs[2]


def measure(fn):
    """(instructions per element, constant) of the call: the slope is an
    integer, and the constant is computed with it."""
    d = [count(fn, n, 'calls') - count(fn, n, 'build') for n in SIZES]
    per = round((d[1] - d[0]) / (SIZES[1] - SIZES[0]))
    return per, d[0] - per * SIZES[0]


def main(argv):
    run = argv[0] if argv else 'asm'
    build()
    m = {f: measure(f) for f in ('add', 'mul', 'mul20', 'length', 'app', 'map', 'fold_left',
                                  'pos_add', 'pos_compare')}
    # Nat.mul: n * (a * m + b) + c, from the slopes for m = 10 and 20
    a = (m['mul20'][0] - m['mul'][0]) // 10
    b = m['mul'][0] - 10 * a
    c = m['mul'][1]
    same = {
        'stdlib/NatComplexity.v#Nat_add_complexity': [0, *m['add']],
        'stdlib/NatComplexity.v#Nat_mul_complexity': [0, a, b, c],
        'stdlib/ListComplexity.v#length_complexity': list(m['length']),
        'stdlib/ListComplexity.v#app_complexity': [0, *m['app']],
    }
    own = {
        'stdlib/PosComplexity.v#Pos_add_complexity':
            ('(fun cx => fun cy => ({0} * Pos.size_nat (val cx) + {1}) >|)', m['pos_add']),
        'stdlib/PosComplexity.v#Pos_compare_complexity':
            ('(fun cx => fun cy => ({0} * Pos.size_nat (val cy) + {1}) >|)', m['pos_compare']),
        'stdlib/HOListComplexity.v#map_complexity':
            ('(fun cf => fun cl => ({0} * length (val cl) + {1}) >|)', m['map']),
        'stdlib/HOListComplexity.v#fold_left_complexity':
            ('(fun cf => fun cl => fun cx => ({0} * length (val cl) + {1}) >|)', m['fold_left']),
    }
    sys.path.insert(0, os.path.join(HERE, '..'))
    import compare
    man = compare.load_manifest()
    model = [r for r in man.values() if not r.get('reference')][-1]['name']
    ref = compare.load_run(model)
    out = []
    for i, vals in same.items():
        e = ref[i]
        out.append(dict(e, model='x86', constants=vals, hyps='', proof='measured'))
    for i, (t, vals) in own.items():
        e = ref[i]
        out.append(dict(e, model='x86', template=t, constants=list(vals), hyps='', proof='measured'))
    with open(os.path.join(REPO, 'bounds', 'runs', run + '.jsonl'), 'w') as f:
        for e in out: f.write(json.dumps(e, ensure_ascii=False) + '\n')
    path = os.path.join(REPO, 'bounds', 'runs.json')
    runs = json.load(open(path))
    runs = [r for r in runs if r['name'] != run] + [{
        'name': run, 'title': 'x86-64 instructions', 'reference': True,
        'source': 'measured, tools/bounds/asm/measure.py', 'description': DESCRIPTION}]
    with open(path, 'w') as f:
        json.dump(runs, f, indent=1, ensure_ascii=False); f.write('\n')
    for e in out: print(e['id'].split('#')[1], e['constants'])
    print(f'{len(out)} measurements -> bounds/runs/{run}.jsonl')


if __name__ == '__main__':
    main(sys.argv[1:])
