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
   "function": "Nat.add", "template": "(fun cn => {0} ⋉ fun cm => ({1} * val cn + {2}) ⋉ tt)",
   "constants": [4, 22, 6], "hyps": "", "proof": "term"}
  ```

  `template` is the bound with its tunable literals numbered. Exponents,
  subtracted literals, indices and `0` are not tunable. The bounds of two
  runs with the same template are compared constant by constant.
  `kind` is `ComplexityBound`, `FirstOrderBound`, `Definition` (a cost
  function or a majorant defined apart, listed in `config.json`) or
  `Majorant` (the higher-order polynomials of `BFFFeasibility`).

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
| `make bounds-check [RUN=name]` | fail if a bound of the working tree is higher than in the run, or has another shape |

`tools/bounds/compare.py` gives other views, from any list of runs:
`--format html` (a page with a filter and sticky columns), `--format csv`
(the long format: one line per run, bound and constant), `--cells formula`
(the bounds themselves instead of their constants), `--changed-only`.

## Minimisation

`minimise.py FILE` lowers, for each bound of the file in order, every
tunable literal by a parallel binary search, while the proof still checks.
It keeps the proof script of the file when it works, and otherwise tries
variants of `cbound`. The result is minimal per constant: no single constant
can be lowered. This is not a global optimum.

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
