(** * Cost model for [unit]

    [tt] is the argument of the thunks used for the branches of constant
    constructors in case analyses (see [Combinators]). *)

From Complexity Require Import CostModel HOCostModel.

Module Type UnitTimeCostModel
  (Import CM : CostModel).

  Parameter tt_complexity : ComplexityBound tt tt.
  Global Existing Instance tt_complexity.
End UnitTimeCostModel.
