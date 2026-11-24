# TODOS

## Applications
See if F&K can handle these. A priori no, as they can't register function types?

### Computable Analysis
Kawamura & Cook-like complexify ; Stdlib's CReal? or CoRN (CR)

## Master theorem
Prove the master theorem (Cormen et al.), with standard examples for each of its cases, whose proofs use the theorem explicitly.

## Okasaki's lazy data structures
Uses suspensions (unit -> A). Amortised analysis.
See  (Danielsson POPL'08, Pottier et al. POPL'24, and Xia et al. ICFP'24 in Rocq).

## Amortised analysis
An example: quicksort, batched queues, or something simpler.

## Parallelism
A model of parallel computations, with the costs of calf's `ParCostMonoid` (sequential `⊕`, parallel `⊗`, e.g. work and span).

## Monadic code
* parser combinator
* interaction trees (which applications?)

## Lists
concatenating lists by composition

## Space
* insertion sort, merge sort, quicksort (i.e. the benchmarks of heap-space analyses: Hofmann & Jost (POPL'03), RaML (Hoffmann, Das & Weng, POPL'17), and the higher-order follow-up by Jost et al. (POPL'10)).

* a function that allocates `n` cells and never uses them: with a perfect garbage collector, its peak memory is constant.

* tail calls: `loop` (`PeakExamples`) runs in constant space as a loop (`while_complexity`, `PeakSpace`); through the fixpoint rule, its peak is linear. The rules of `PeakSpace` have no instance (in L, or on a machine with a heap).

* a separate compiler for space complexity: it recognises tail recursion (compiled to loops, `while_unfold`) and frees memory when it can (the releases of `PeakSpace`), instead of the manual proofs of `PeakExamples`.

* the compilation time of `PeakExamples` (`double`: about 13 s). `ccases` takes most of it, on goals with about 1500 truncated subtractions, nearly all `x - 0` or `0 - x` from the zero profiles: calf's composition `p + (q ∸ p')` does not compute for a symbolic `q`. Two ways:
  - profiles in the coordinates `(steps, need, net)`, with `net = need - ret` in `Z`, negative after frees: the same algebra, composed in max-plus (`need (a·b) = max (need a) (net a + need b)`, `net (a·b) = net a + net b`), with no truncated subtraction, but bounds in `Z`;
  - calf's pairs in `nat`, with the zero profiles simplified at the level of `cplus`, before `csimpl` unfolds them.

* bruteforce SAT
* QBF
* SAvitch reachability
* space/time tradeoffs (fibonacci memoised, iterative)
* sublinear space:  (Dal Lago & Schöpp, Functional programming in sublinear space, ESOP 2010);
  - palindrome check
  - binary addition
  - function composition

## parameterised cost constants
The costs of the primitives are constants, fixed by each model (`ParamTimeCostModel`, `TimeCostModel`, `TimeArith`). Remaining:
* analyses generic in the constants: bounds are linear forms in the constants, heavy to write by hand. Needs a tactic computing the coefficients, and `poly_of` (`Bounds`) to treat constants as coefficients rather than as measures of degree 1.
* operation counts are separated by keeping their constants abstract (`ArithOpsTimeCostModel`, `HornerCount`); unfoldings must cost at least 1 (`UnguardedFix`), so they are still charged, with their own constant.

## Cleanups
* `ℂO` and `ℂO'`: `ℂO'` is the record of a cost and a result, `ℂO` an abbreviation of it, for the costs of the model (`CostModelAxioms`) and for `nat` outside a model (`CostModelCore`).

## To check

Polynomial time is a mess.
Check BFF as well: might need a deep embedding (or inductive predicate that a function is BFF).
The complexity bound for R should have no hypothesis and be higher-order.


## This is starting to be module hell.
try and find a way to refactor this nicely.

