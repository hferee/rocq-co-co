(** * The bounds of the higher-order functions on lists hold in L

    [LH] ([LInstance], the same as [L]) is the instance of the cost
    model. With the bounds of the boolean operations
    ([BoolComplexity]), it is an instance of [HOTimeBool], to which the
    analyses of [HOListComplexity] apply: their bounds are L running times.
    They use no axiom. *)

From Complexity Require Import LInstance BoolComplexity HOListComplexity PairComplexity.

Module LHB <: HOTimeBool.
  Include LH.
  Include BoolComplexity LH.
End LHB.

Module LHL := HOListComplexity LHB.

(** The projections of pairs of any data ([HPairComplexity]). *)
Module LHP := HPairComplexity LH.
