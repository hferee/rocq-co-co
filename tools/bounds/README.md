# Complexity bounds: snapshots and comparison

These tools record the complexity bounds of the repository, minimise their
constants, and compare them across versions of the compiler or of the cost
model.

## Data

- `bounds/runs.json`: the manifest of runs. A run is one state of the bounds,
  such as a compiler or a cost model, with a name, a title (the column header
  of the tables), its source (a commit or a working tree) and a description.
- `bounds/runs/<name>.jsonl`: the snapshot of a run, one bound per line:

  ```json
  {"id": "stdlib/NatComplexity.v#Nat_add_complexity", "kind": "ComplexityBound", "model": "Time",
   "function": "Nat.add", "template": "(fun cn => {0} +> fun cm => ({1} * val cn + {2}) >|)",
   "constants": [4, 22, 6], "hyps": "", "proof": "term"}
  ```

  `template` is the bound with its tunable literals numbered. Exponents,
  subtracted literals, indices and `0` are not tunable. The bounds of two
  runs with the same template are compared constant by constant.
  `kind` is `ComplexityBound`, `FirstOrderBound`, `Definition` (a cost
  function or a majorant defined apart, listed in `config.json`) or
  `Majorant` (the higher-order polynomials of `BFFFeasibility`).

A run marked `"reference": true` in the manifest is a measurement, not a
state of the bounds: the run `asm` (`asm/measure.py`) gives the x86-64
instructions executed by some functions, extracted to OCaml and compiled
with `ocamlopt` without optimisation, counted by single-stepping them. The
tables show it, but the comparison column and `bounds-check` ignore it.

A snapshot is cheap to make: it reads the sources, and doesn't compile them.
The minimisation that produced the constants is recorded in the run's
description.

## Commands

From the root of the repository, with the library built:

| Command | What it does |
|---|---|
| `make bounds-snapshot RUN=name [REV=rev] [TITLE=..] [DESCRIPTION=..]` | snapshot of the working tree, or of a git revision |
| `make bounds-minimise [SCREEN=1] [FILES="stdlib/NatComplexity.v ..."]` | minimise the constants, in dependency order (slow) |
| `make bounds-table` | regenerate `bounds-comparison.md` from the runs of `config.json` |
| `make show-bounds-table [RUNS="name ..."]` | the same table as an HTML page, `bounds-comparison.html` (not versioned), opened in the browser |
| `make bounds-check [RUN=name]` | fail if a bound of the working tree is higher than in the run, or has another shape |
| `make bounds-asm` | the x86-64 instructions executed by some functions, extracted to OCaml (`asm/`), as the reference run `asm` |

`tools/bounds/compare.py` gives other views, from any list of runs:
`--format html` (a page with a filter and sticky columns), `--format csv`
(the long format: one line per run, bound and constant), `--cells formula`
(the bounds themselves instead of their constants), `--changed-only`.

## Minimisation

`minimise.py FILE` finds, for each bound of the file in order, the smallest
values of its tunable literals, as one does by hand:

1. The literals become variables `κ0`, `κ1`, ..., and the proof is run in
   export mode (`Ltac2 Set cexport := true`, `TimeCombinators`): instead of
   calling `lia`, `cbound` prints the inequalities it leaves, with their
   arithmetic hypotheses, and admits them. One compilation.
2. `goals.py` solves them. For fixed values of the other atoms (values and
   lengths of the arguments, costs of functional arguments), each one is
   linear in the constants; grouped by monomials of the atoms, it gives
   linear inequalities on the constants, which are lowered one at a time
   until none can be. A hypothesis `a < x` on an atom `x` (a size) is used
   by replacing `x` with `a + 1 + s`.
3. The values are checked with the proof of the file, and each one lowered
   by one, in one parallel round.

If this does not conclude (a constant inside an atom, such as an argument
of a cost function, an inequality that is not linear in the constants, or a
constant that can still be lowered), the minimiser falls back on a parallel
binary search: the literals are scaled up until the proof goes through,
then lowered one at a time, while it still checks. It keeps the proof
script of the file when it works, and otherwise tries variants of `cbound`.
Either way, the result is minimal per constant: no single constant can be
lowered. This is not a global optimum.

`--screen` keeps a bound in which no constant can be lowered by one. This is
fast after a change that only lowers costs.

Constants copied in several places must change together. Each file with
such constants has a spec in `groups/` listing the places, and `groups.py`
lowers them jointly while the whole file compiles. Prefer named constants,
referred to everywhere, to copies.

The minimiser only checks each file up to the declaration it changes:
`make bounds-minimise` builds each file afterwards. It stops at the first
bound it cannot prove.

Environment variables: `JOBS` (parallel compilations, default 8), `TIMEOUT`
(seconds per compilation, default 150), `ROCQ` (the compiler), `BOUNDS_TMP`
(scratch directory).
