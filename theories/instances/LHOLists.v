(** * The bounds of the higher-order functions on lists hold in L

    [LH] ([LInstance]) is the instance of the cost model with lists and
    options of any data ([HOTimeCostModel]). With the bounds of the boolean operations
    ([BoolComplexity]), it is an instance of [HOTimeBool], to which the
    analyses of [HOListComplexity] apply: their bounds are L running times.
    The only axiom they use is functional extensionality, through
    [fix_complexity]. *)

From Complexity Require Import LInstance BoolComplexity HOListComplexity.

Module LHB <: HOTimeBool.
  Include LH.
  Include BoolComplexity LH.
End LHB.

Module LHL := HOListComplexity LHB.
