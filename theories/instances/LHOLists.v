(** * The bounds of the higher-order functions on lists hold in L

    [L] ([LInstance]) is the instance of the cost model. With the bounds of
    the boolean operations ([BoolComplexity]), it is an instance of
    [TimeBool], to which the analyses of [HOListComplexity] apply: their
    bounds are L running times. They use no axiom. *)

From Complexity Require Import LInstance BoolComplexity HOListComplexity PairComplexity.

Module LHB <: TimeBool.
  Include L.
  Include BoolComplexity L.
End LHB.

Module LHL := HOListComplexity LHB.

(** The projections of pairs ([PairComplexity]). *)
Module LHP := PairComplexity L.
