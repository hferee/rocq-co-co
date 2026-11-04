# rocq-co-co : Computational Complexity in Rocq for Rocq
Experiments in around reasoning on the complexity of Rocq in Rocq

## Layout (`theories/`, logical path `Complexity`)

- `model/`: the cost model, independent of the resource: complexities,
  representations, `ComplexityBound` (`CostModelCore`), and bounds in the
  sizes of the inputs (`Bounds`), together in `CostModel`.
- `time/`: the time cost model, as one signature `TimeCostModel` gathering
  the costs of application (`TimeBasic`), of the combinators
  (`TimeCombinators`), of the datatypes (`TimeDatatypes`) and of fixpoints
  (`TimeFix`).
- `compiler/`: the combinators and the compilation of Gallina terms to them
  (closure conversion in `Compile`, bracket abstraction in `BracketCompile`).
- `math/`: polynomials, the simply typed λ-calculus over a signature
  (`Lambda`), higher-order polynomials (`HOPoly`), sizes of binary numbers.
- `stdlib/`: analyses of the standard library, as layers over
  `TimeCostModel` (`TimeNat`, `TimePos`, `TimeStdlib`).
- `bff/`: the basic feasible functionals (PV^ω), their complexity, their
  higher-order polynomial bounds, and Irwin, Kapron and Royer's type-3
  example.
- `instances/`: the call-by-value λ-calculus L as an instance of
  `TimeCostModel`.
- `examples/`: examples, and the analysis of an ETH algorithm.

Build with `make` (Rocq 9.2, rocq-stdlib, coq-library-undecidability).
