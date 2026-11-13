# rocq-co-co : Computational Complexity in Rocq for Rocq
Experiments in around reasoning on the complexity of Rocq in Rocq

## Layout (`theories/`, logical path `Complexity`)

- `model/`: the cost model, independent of the resource: complexities,
  representations, `ComplexityBound` (`CostModelCore`), and bounds in the
  sizes of the inputs (`Bounds`), and at higher types: majorizations,
  higher-order polynomial bounds, sizes of functionals (`HOBounds`), together
  in `CostModel`.
- `time/`: the time cost model, as one signature gathering the costs of
  application (`TimeBasic`), of the combinators (`TimeCombinators`), of the
  datatypes (`TimeDatatypes`, with separate layers for the data, the
  constructors and the case analysis of each datatype; lists in `TimeLists`,
  with two models: lists of ground data, and lists of any data, whose
  complexity is the list of the complexities of their elements) and of
  fixpoints (`TimeFix`). The costs are constants: `ParamTimeCostModel` leaves
  them abstract, `TimeCostModel` sets them all to 1, and `HOTimeCostModel` is
  the same with lists and options of any data (`TimeDatatypes` has the two
  models of options). `TimeArith` defines another
  model, with addition and multiplication as primitives and no case analysis
  on `nat`, and its instance counting arithmetic operations.
- `space/`: the space cost model (`SpaceCostModel`): the layers of the time
  cost model, with the allocations of the primitives as costs (a closure, a
  constructor or a frame allocates a cell; an application or a case analysis
  allocates nothing). The space is the total allocation. `SpaceExamples`
  bounds the allocations of standard functions (`Nat.add`, `Nat.mul`, `app`,
  `rev`, `rev_append`, `map`, ...). `AllocCostModel` adds an experimental
  axiom relating allocations to the sizes of functionals.
- `compiler/`: the combinators and the compilers of Gallina terms to them:
  closure conversion (`ClosureCompile`, the default) and bracket abstraction
  (`BracketCompile`), over common tools (`CompileCommon`: case combinators,
  unfolding equations of recursive functions). `cbound` uses the compiler
  `ccompiler` (`Compile`), which a file can change for its proofs
  (`#[local] Ltac2 Set ccompiler := ...`, as `BracketComparison` does).
- `math/`: polynomials, the simply typed λ-calculus over a signature
  (`Lambda`), higher-order polynomials (`HOPoly`), second-order polynomials
  (`SOPoly`), sizes of binary numbers.
- `stdlib/`: analyses of the standard library, as layers over
  `TimeCostModel` (`TimeNat`, `TimePos`, `TimeStdlib`), and the
  higher-order functions on lists and options of any data (`map`, `filter`,
  `find`, the folds, `option_map`, ...) over `HOTimeCostModel`
  (`HOListComplexity`).
- `bff/`: the basic feasible functionals (PV^ω), their complexity, their
  higher-order polynomial bounds, and Irwin, Kapron and Royer's type-3
  example.
- `machine/`: the cost model of an environment machine for L
  (`MachineCostModel`: closures, variables read in a linked environment,
  frames for the evaluations in non-tail position, so that tail calls are
  cheaper), and running times on it (`MachineExamples`). The machine is an
  instance of the whole time model, with ground lists and options and with
  lists and options of any data (`instances/LMachine`: `LM`, `LMH`).
- `instances/`: the call-by-value λ-calculus L as an instance of
  `TimeCostModel` and of `HOTimeCostModel` (`LInstance`), with the bounds of
  the higher-order functions on lists (`LHOLists`), and of the arithmetic
  signature (`LArith`).
- `examples/`: examples, the analysis of an ETH algorithm, operation counts
  in the arithmetic model (`HornerCount`, and Strassen's matrix product in
  `StrassenCount`), and why unfoldings of fixpoints must not be free
  (`UnguardedFix`). `Tutorial` is a set of exercises for students: bounds
  to prove, with the method (`cbound`, `cexplain`, `cproject`, `csize`).

Build with `make` (Rocq 9.2, rocq-stdlib, coq-library-undecidability).

The complexity bounds of the repository are recorded in snapshots
(`bounds/runs/`, one per version of the compiler or of the cost model) and
compared in `bounds-comparison.md`; `make bounds-snapshot`,
`make bounds-minimise`, `make bounds-table`, `make show-bounds-table` (the
table in the browser) and `make bounds-check` manage them
(`tools/bounds/README.md`).

`attic/` keeps old experiments, not compiled (`attic/README.md`), among
them the deque example (`attic/deque`).
