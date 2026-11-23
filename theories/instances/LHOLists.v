(** * The bounds of the higher-order functions on options and lists hold in L

    [L] ([LInstance]) is the instance of the cost model, to which the
    analyses of [HOOptionComplexity] apply. With the bounds of the boolean
    operations ([BoolComplexity]), it is an instance of [TimeBool], to
    which those of [HOListComplexity] apply. Their bounds are L running
    times. They use no axiom. *)

From Complexity Require Import LInstance BoolComplexity HOOptionComplexity HOListComplexity
  PairComplexity.

Module LHO := HOOptionComplexity L.

Module LHB <: TimeBool.
  Include L.
  Include BoolComplexity L.
End LHB.

Module LHL := HOListComplexity LHB.

(** The projections of pairs ([PairComplexity]). *)
Module LHP := PairComplexity L.
