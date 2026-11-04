# TODOS

## Applications
See if F&K can handle these. A priori no, as they can't register function types?

### Computable Analysis
Kawamura & Cook-like complexify ; Stdlib's CReal? or CoRN (CR)

## Okasaki's lazy data structures
Uses suspensions (unit -> A). Amortised analysis.
See  (Danielsson POPL'08, Pottier et al. POPL'24, and Xia et al. ICFP'24 in Rocq).

## Monadic code
* parser combinator
* interaction trees (which applications?)

## Lists
concatenating lists by composition

## Space
* insertion sort, merge sort, quicksort (i.e. the benchmarks of heap-space analyses: Hofmann & Jost (POPL'03), RaML (Hoffmann, Das & Weng, POPL'17), and the higher-order follow-up by Jost et al. (POPL'10)).

* bruteforce SAT
* QBF
* SAvitch reachability
* space/time tradeoffs (fibonacci memoised, iterative)
* sublinear space:  (Dal Lago & Schöpp, Functional programming in sublinear space, ESOP 2010);
  - palindrome check
  - binary addition
  - function composition