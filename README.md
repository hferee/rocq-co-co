# rocq-co-co : Computational Complexity in Rocq for Rocq
Experiments in around reasoning on the complexity of Rocq in Rocq

## Layout (`theories/`, logical path `Complexity`)

- `models/`: the cost models, each with its results and an `examples/`
  folder.
  - `core/`: the cost model, independent of the resource: complexities,
    representations, `ComplexityBound` (`CostModelCore`), and bounds in the
    sizes of the inputs (`Bounds`, with their tactics in `BoundsTactics`),
    and at higher types: majorizations, higher-order polynomial bounds,
    sizes of functionals (`HOBounds`), together in `CostModel`.
  - `time/`: the time cost model, as one signature gathering the costs of
    application and of the combinators (`TimeCombinators`), of the
    datatypes (`TimeDatatypes`, with separate layers for the data, the
    constructors and the case analysis of each datatype; lists in
    `TimeLists`) and of fixpoints (`TimeFix`). The data are of any type:
    the complexity of a list is the list of the complexities of its
    elements, one for each (it is well-formed, `wf`); ground data (numbers,
    pairs of numbers, ...) are those whose complexities carry no
    information (`IsGround`), and a bound with a ground result ends with
    `>|`. The costs are constants: `ParamTimeCostModel` leaves them
    abstract, `TimeCostModel` sets them all to 1. The size of a value is
    the length of its binary encoding, its number of constructors (exact
    equations: `size (S n) = 1 + size n`, ...).
    - `stdlib/`: analyses of the standard library, as layers over
      `TimeCostModel` (`TimeBoolPair`, `TimeNat`, `TimePos`, `TimeStdlib`;
      booleans and pairs first, then numbers and lists: the first-order
      functions of lists and the higher-order ones on lists of numbers
      (`ListComplexity`), the higher-order functions on options and on
      lists of any data (`option_map`, `HOOptionComplexity`; `map`,
      `filter`, `find`, the folds, `lefts` and `rights` on lists of sums,
      ..., `HOListComplexity`), and the usual functions on sums
      (`SumComplexity`)).
    - `machine/`: the cost model of an environment machine for L
      (`MachineCostModel`: closures, variables read in a linked
      environment, frames for the evaluations in non-tail position, so that
      tail calls are cheaper), and running times on it
      (`examples/MachineExamples`). The machine is an instance of the whole
      time model (`instances/LMachine`: `LM`).
    - `instances/`: the call-by-value λ-calculus L as an instance of
      `TimeCostModel` (`LInstance`), with the bounds of the higher-order
      functions on lists (`LHOLists`); the environment machine for L as an
      instance of `MachineTimeCostModel` (`LMachine`).
    - `examples/`: examples, the analysis of an ETH algorithm (`eth/`), and
      why unfoldings of fixpoints must not be free (`UnguardedFix`).
      `Tutorial` is a set of exercises for students: bounds to prove, with
      the method (`cbound`, `cexplain`, `cproject`, `csize`). `Examples`
      also shows how to prove functions with local fixpoints (their bounds
      declared first) and functions defined by well-founded recursion
      (`Function`). `Limitations` shows what the analysis does not cover
      (dependent matches), with the error reported.
  - `counting/`: models counting chosen operations.
    - `counting_arith/`: addition and multiplication as primitives, and no
      case analysis on `nat` (`TimeArith`); `examples/`: operation counts
      (`HornerCount`, and Strassen's matrix product in `StrassenCount`).
    - `counting_comparisons/`: comparisons of an abstract type as the only
      primitive charged (`CmpCount`); `examples/`: van der Weegen and
      McKinna's quicksort, with its exact comparison count (`QuickSort`).
  - `space/`: the total allocation (`TotalAllocationModel`): the layers of
    the time cost model, with the allocations of the primitives as costs (a
    closure, a constructor or a frame allocates a cell; an application or a
    case analysis allocates nothing), never freed.
    `AllocCostModel` adds an experimental axiom relating allocations to the
    sizes of functionals. `examples/SpaceExamples` bounds the allocations of
    standard functions (`Nat.add`, `Nat.mul`, `app`, `rev`, `rev_append`,
    `map`, ...).
- `compiler/`: the compilers of Gallina terms to the combinators
  (`math/Combinators`): closure conversion (`ClosureCompile`, the default)
  and bracket abstraction (`BracketCompile`), over common tools
  (`CompileCommon`: case combinators, unfolding equations of recursive
  functions). `cbound` uses the compiler `ccompiler` (`Compile`), which a
  file can change for its proofs (`#[local] Ltac2 Set ccompiler := ...`, as
  `BracketComparison` does).
- `math/`: the closure combinators (`Combinators`), polynomials, the simply
  typed λ-calculus over a signature (`Lambda`, its terms denoted with the
  combinators), higher-order polynomials (`HOPoly`), second-order
  polynomials (`SOPoly`), sizes of binary numbers.
- `bff/`: the basic feasible functionals (PV^ω), their complexity, their
  higher-order polynomial bounds, and Irwin, Kapron and Royer's type-3
  example.
- `lower/`: lower bounds, from axioms with negative content (what a bound
  implies). An application of `S` costs at least 1, and the output of a
  function on numbers exceeds its input by at most a constant times the
  cost (`NatLowerBound`); likewise for lists of numbers, with a linear
  lower bound for sorting (`ListLowerBound`); both proved in L.

Build with `make` (Rocq 9.2, rocq-stdlib, coq-library-undecidability).
`make doc` generates the HTML documentation in `html/` (start at
`html/index.html`), with [CoqdocJS](https://github.com/coq-community/coqdocjs)
(`doc/coqdocjs`): proofs are folded, and unfolded by clicking on them.

The complexity bounds of the repository are recorded in snapshots
(`bounds/runs/`, one per version of the compiler or of the cost model) and
compared in `bounds-comparison.md`; `make bounds-snapshot`,
`make bounds-minimise`, `make bounds-table`, `make show-bounds-table` (the
table in the browser) and `make bounds-check` manage them
(`tools/bounds/README.md`).

`make depgraph` draws the dependency graph of the files, with
coq-library-undecidability: `doc/deps.dot` (every direct import) and
`doc/deps.svg` (without the transitive edges; Graphviz). In a browser, a
file of `doc/deps.svg` links to its documentation (`make doc`).

`attic/` keeps old experiments, not compiled (`attic/README.md`), among
them the deque example (`attic/deque`).
