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

No new axiom was needed after `env`.

## Summary

Against the old compilation, the last run has 88 bounds with every constant
lower or equal, 13 mixed, 13 higher and 17 unchanged, out of 131. Each step
after `env` only lowered constants: `selfcase` lowered 44 bounds, `argenv`
90. The last run also has 39 bounds in the sizes of the arguments
(`…_size_complexity`, in `#|x|`), derived from the bounds in the values.

- Recursive functions are cheaper per step: `Nat.add` 36n → 22n, `Pos.add`
  34 → 18 per bit, `Pos.compare` 86 → 40, `app` 47 → 31 per element,
  `length` 17 → 14.
- Partial applications cost one step less with `argenv` (`5 +>` → `4 +>`).
- Small non-recursive functions (`negb`, `Z.opp`, `tr`, `par`) are still
  dearer than with the old compilation: the matched value and the arguments
  of the constructors are read from the environment, where the old
  combinators received them directly.
- Every space bound is lower: a `match` allocates nothing.

## How the constants were obtained

For each bound, in file order, every literal was lowered while the proof
still checked, until none could be lowered. The search was a binary
search, one literal at a time. The proof script of the file was kept when it
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
