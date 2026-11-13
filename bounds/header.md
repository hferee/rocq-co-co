# Complexity bounds of the repository, across compilations of `match`

This table is generated: `make bounds-table` (see `tools/bounds/README.md`).
Do not edit it; edit `bounds/header.md` and the runs of `bounds/runs.json`.

Each row is a bound. The **Bound** column is its shape, with its constants
numbered ①, ②, …. Each column after it is a run, and gives the values of
these constants. A cell differing from the previous run is in **bold**. The
last column compares the first run with the last: ↓ means every constant is
lower or equal, ↑ every constant is higher or equal, ↕ mixed, = unchanged.

## The runs

- **Old compilation** (`thunks`, commit `3087c87`): a `match` is compiled to
  its case combinator applied to one closure per branch (a thunk
  `fun _ : unit => …` for a constant constructor) and to the matched value.
  The closures are built each time the `match` is evaluated.
- **Environment combinators** (`env`): the case combinators take the branches
  and the matched value as code over the environment of the enclosing
  closure. `nat_case z s n e` runs `n e`, then `z e` on `O`, or
  `s (ECons e k)` on `S k`. No closure is built when a `match` is evaluated;
  the arguments of the constructor are read from the extended environment.
  The case axioms (`nat_case_complexity`, …) are the environment versions,
  with the same names, proved in L (`LInstance`).
- **Matched variable as environment** (`selfcase`): the same axioms, and a
  closed `fun x => match x with … end` is compiled to the case combinator
  itself, with `x` as its environment, read by `Ic`. For example, `negb` is
  `bool_case (Kc false) (Kc true) Ic` instead of
  `Lam (bool_case (Kc false) (Kc true) ehd) tt`. This saves the step of the
  closure.
- **Argument as environment** (`argenv`): every closed function that is not
  an eta-reduction is the code of its body, with its argument as the
  environment (`closed` in `Compile`). A curried `fun a b => …` is `Lam c`,
  with `c` the code of the body in `ECons a b`. The first application costs
  one step less, and the first argument is read with `etl` alone. This also
  holds for the functional `F` of a recursive function, whose first argument
  is the function itself: each recursive call is cheaper.

- **Fixpoints with an environment** (`envfix`): the fixpoint axiom
  `fix_complexity` is stated for a recursive function `f e` with an
  environment `e` (its free variables): its functional runs in
  `ECons e (f e)`. A closed recursive function is the case `e = tt`: it
  reads itself in `ECons tt f`, 2 steps more for each recursive call. The
  arguments that every recursive call passes unchanged go in the
  environment, and are no longer passed again: the second argument of
  `app`, `Nat.add`, `Nat.mul` and `Pos.mul`, the first ones of `Nat.pow` and
  `rec_pos`, the function of `fold_left`. Lists and options of any data get
  their own models (`TimeLists`, `TimeDatatypes`, `HOTimeCostModel`), with
  new bounds for `map`, `filter`, `find`, the folds, `option_map`, ...
  (`HOListComplexity`). The constants were found from
  the inequalities left by the proofs (`goals.py`), and the bounds in the
  sizes were minimised too.

- **x86-64 instructions** (`asm`, a reference, not compared): the
  instructions executed by some functions extracted to OCaml and compiled
  with `ocamlopt` without optimisation, counted exactly by single-stepping
  them (`make bounds-asm`, `tools/bounds/asm`). Where the shape of the
  bound is the same, the cells give the constants (a partial application
  costs 0: the calls are saturated); otherwise the formula measured, for
  the inputs described in `bounds/runs.json`. For `map` and `fold_left`, the
  costs of `f` are included. The per-element constants of the model and of
  x86 are close for the recursions on one argument (`Nat.add` 14 and 15,
  `length` 16 and 15, `app` 21 and 21), and far apart for the functions of
  several arguments with nested matches (`Pos.compare` 42 and 15 per bit).

The section **Environment machine for L** gives bounds in another cost
model: steps of an environment machine for L (`machine/MachineCostModel`,
instance `instances/LMachine`, of the whole time model), which reads variables in a linked
environment, allocates closures and pays a frame for each evaluation in
non-tail position. Each combinator costs at most 16 steps of the machine,
so that these bounds are about 17 times those of the time model.

No new axiom was needed between `env` and `argenv`. `envfix` replaces the
fixpoint axiom, and adds the axioms of lists and options of any data, all
proved in L.

## Summary

Against the old compilation, the last run has 83 bounds with every constant
lower or equal, 18 mixed, 13 higher and 16 unchanged, out of 131 (one has
another shape: `horner`, see below). From `env` to `argenv`, each step only
lowered constants: `selfcase` lowered 44 bounds, `argenv` 90. `argenv` also
added 39 bounds in the sizes of the arguments (`…_size_complexity`, in
`#|x|`), derived from the bounds in the values.

`envfix` trades costs: 19 bounds are lower, 35 mixed, 71 higher and 44
unchanged, against `argenv`.
- Functions with an argument passed unchanged are cheaper per step:
  `Nat.add` 22n → 14n, `Nat.mul` 22 → 14, `app` 31 → 21 per element,
  `rec_pos` 105 → 75 per bit, `pad`/`chop` 28 → 20 per bit. Their partial
  application costs 1 (a closure), and the last application 2 or 3 more,
  once: `Nat.add` `4 +> 22n + 6` → `1 +> 14n + 10`.
- The other recursive functions pay 2 more per call (`length` 14 → 16,
  `Pos.compare` 40 → 42): they read themselves in their environment.
- `horner x l` charges its last unfolding when `l` is given, not when `x`
  is: its bound changed shape.
- In the space model, the closure of the environment of `Nat.add`,
  `Nat.mul`, `app` and `repeat` is allocated once, when the last argument is
  given: their bounds have a constant term.

Against the old compilation:
- Recursive functions are cheaper per step: `Nat.add` 36n → 14n, `Pos.add`
  34 → 19 per bit, `Pos.compare` 86 → 42, `app` 47 → 21 per element,
  `length` 17 → 16.
- Small non-recursive functions (`negb`, `Z.opp`, `tr`, `par`) are still
  dearer than with the old compilation: the matched value and the arguments
  of the constructors are read from the environment, where the old
  combinators received them directly.
- Every space bound is lower or equal per step: a `match` allocates
  nothing. `Nat.add`, `Nat.mul`, `app` and `repeat` allocate a little more
  once (the closure of the environment of their fixpoint), and much less
  per step: `Nat.add` `3 +> 7n + 2` → `1 +> 3n + 3`.

## How the constants were obtained

For each bound, in file order, every literal was lowered while the proof
still checked, until none could be lowered. Up to `argenv`, the search was a
binary search, one literal at a time; for `envfix`, the literals were first
solved from the inequalities that the proof leaves when they are variables
(`tools/bounds/goals.py`), then checked and lowered by one, with the binary
search as a fallback. The proof script of the file was kept when it
worked; otherwise a `cbound` variant was used. Constants copied in several
places were lowered jointly, with the whole file as the check:
`rec_cost`/`step_bound`, `C_pot`/`V_cost`/`W_cost` and their majorants, and
the majorants of `BFFFeasibility`. The same procedure was run on the old
version. From `selfcase` on, a bound was minimised again only if one of its
constants could be lowered by one.

This is a minimum per constant, not a global optimum: when a bound has
several constants, another combination may lower one constant and raise
another. For example, `Z.succ_double` admits both `16·z + 6` and `15·z + 7`
with the environment combinators, and the table keeps the lower slope.

## Notation

`λn. ① +> λm. ②`: applying the function to `n` costs ①, and gives a closure;
applying that closure to `m` costs ②. The end of a ground result, `>|` (that is
`+> tt`), is left out.
`n` stands for the value of the argument (`val cn`). `|x|` is a length: the
number of bits of a binary number (`N.size_nat`, `Pos.size_nat`) or the length
of a list. `#|x|` is the size of `x` in the model (`size`, class `Size`).
`pot f` is the potential of a functional argument, the bound of its
applications.
