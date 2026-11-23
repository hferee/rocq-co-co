"""The x86-64 instruction counts of some functions of the library, as a run.

usage: measure.py [RUN]          (default RUN: asm)

The functions (Ex.v) are extracted to OCaml, as they are defined in the
standard library, and compiled with ocamlopt without optimisation
(-inline 0; ocamlopt without flambda does not optimise further). The
instructions executed are counted by single-stepping the program (icount.c,
ptrace), for inputs of two sizes, with and without the calls (ten calls on
the same input): the differences give the instructions per element and the
constant (the minor heap is large enough that no collection happens, and
the addresses are not randomised). The start-up of the program varies by a
few instructions from one run to the next, so the constants are exact to
about one instruction. The run is
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
REPS = 10                      # the calls of main.ml
FUNCTIONS = ('add', 'mul', 'mul20', 'sub', 'eqb', 'leb', 'ltb', 'length', 'app', 'seq', 'rev_append',
             'map', 'fold_left', 'fold_right', 'filter', 'forallb', 'succ_all', 'count_acc',
             'pos_succ', 'pos_add', 'pos_compare', 'pos_eqb', 'z_add')

DESCRIPTION = (
    "x86-64 instructions executed by the functions extracted to OCaml (ocamlopt 5.4, -inline 0, "
    "no flambda), counted by single-stepping (tools/bounds/asm). Nat.add and Nat.mul: the second "
    "argument of size 3 (Nat.mul: 10 and 20, for its two coefficients); Nat.sub, eqb, leb, ltb: two "
    "equal numbers; seq: from 0; app and rev_append: the second list of length 3; Pos.add, "
    "Pos.compare and Pos.eqb: two equal numbers of n bits, all 1 (Pos.succ: one, all 1: the carry "
    "goes through); Z.add: x and -x, of n bits, all 1 (Z.pos_sub); map: f = fun x => S x; "
    "fold_left and fold_right: f = fun a _ => S a (fun _ a => S a), from 0; filter and forallb: "
    "f = fun _ => true (the costs of f included); count_acc: from 0. Partial applications: 0 (the "
    "calls are saturated). The constants include the call from the measuring program.")


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
    """(instructions per element, constant) of one call: the program makes
    [REPS] calls (main.ml); the slope is an integer, and the constant is
    computed with it."""
    d = [(count(fn, n, 'calls') - count(fn, n, 'build')) / REPS for n in SIZES]
    per = round((d[1] - d[0]) / (SIZES[1] - SIZES[0]))
    return per, round(d[0] - per * SIZES[0])


def main(argv):
    run = argv[0] if argv else 'asm'
    build()
    m = {f: measure(f) for f in FUNCTIONS}
    # Nat.mul: n * (a * m + b) + c, from the slopes for m = 10 and 20
    a = (m['mul20'][0] - m['mul'][0]) // 10
    b = m['mul'][0] - 10 * a
    c = m['mul'][1]
    # the bounds of the same shape: [0] for the partial applications
    same = {
        'models/time/stdlib/NatComplexity.v#Nat_add_complexity': [0, *m['add']],
        'models/time/stdlib/NatComplexity.v#Nat_mul_complexity': [0, a, b, c],
        'models/time/stdlib/NatComplexity.v#Nat_sub_complexity': [0, *m['sub']],
        'models/time/stdlib/NatComplexity.v#Nat_eqb_complexity': [0, *m['eqb']],
        'models/time/stdlib/NatComplexity.v#Nat_leb_complexity': [0, *m['leb']],
        'models/time/stdlib/NatComplexity.v#Nat_ltb_complexity': [0, *m['ltb']],
        'models/time/stdlib/ListComplexity.v#length_complexity': list(m['length']),
        'models/time/stdlib/ListComplexity.v#app_complexity': [0, *m['app']],
        'models/time/stdlib/ListComplexity.v#seq_complexity': [0, *m['seq']],
        'models/time/machine/examples/MachineExamples.v#Nat_add_machine': [0, *m['add']],
        'models/time/machine/examples/MachineExamples.v#length_machine': list(m['length']),
        'models/time/machine/examples/MachineExamples.v#app_machine': [0, *m['app']],
        'models/time/machine/examples/MachineExamples.v#rev_append_machine': [0, *m['rev_append']],
        'models/time/machine/examples/MachineExamples.v#count_acc_machine': [0, *m['count_acc']],
        'models/time/machine/examples/MachineExamples.v#succ_all_machine': list(m['succ_all']),
    }
    hl = '(fun cf => fun cl => ({0} * length (val cl) + {1}) >|)'
    own = {
        'models/time/stdlib/PosComplexity.v#Pos_succ_complexity':
            ('(fun cp => ({0} * Pos.size_nat (val cp) + {1}) >|)', m['pos_succ']),
        'models/time/stdlib/PosComplexity.v#Pos_eqb_complexity':
            ('(fun cp => fun cq => ({0} * Pos.size_nat (val cp) + {1}) >|)', m['pos_eqb']),
        'models/time/stdlib/PosComplexity.v#Pos_add_complexity':
            ('(fun cx => fun cy => ({0} * Pos.size_nat (val cx) + {1}) >|)', m['pos_add']),
        'models/time/stdlib/PosComplexity.v#Pos_compare_complexity':
            ('(fun cx => fun cy => ({0} * Pos.size_nat (val cy) + {1}) >|)', m['pos_compare']),
        'models/time/stdlib/ZComplexity.v#Z_add_linear_complexity':
            ('(fun cx => fun cy => ({0} * zsize (val cx) + {1}) >|)', m['z_add']),
        'models/time/stdlib/HOListComplexity.v#map_complexity': (hl, m['map']),
        'models/time/stdlib/HOListComplexity.v#filter_complexity': (hl, m['filter']),
        'models/time/stdlib/HOListComplexity.v#forallb_complexity': (hl, m['forallb']),
        'models/time/stdlib/HOListComplexity.v#fold_left_complexity':
            ('(fun cf => fun cl => fun cx => ({0} * length (val cl) + {1}) >|)', m['fold_left']),
        'models/time/stdlib/HOListComplexity.v#fold_right_complexity':
            ('(fun cf => fun ca0 => fun cl => ({0} * length (val cl) + {1}) >|)', m['fold_right']),
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
