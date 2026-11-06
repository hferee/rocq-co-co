(** * L is an instance of the arithmetic signature

    In L, [Nat.add] and [Nat.mul] are not primitive: the constants of their
    costs in [NatArithTimeCostModel] are those of the bounds proved from
    their definitions in [NatComplexity]. L is thus an instance of
    [ParamArithTimeCostModel] ([TimeArith]), and an analysis over this
    signature holds both in L and in [ArithOpsTimeCostModel]. *)

From Complexity Require Import TimeArith NatComplexity LInstance.

Module LNC := NatComplexity L.

Module LNA <: NatArithTimeCostModel L L.
  Import L.
  Definition c_add_clo := 5.
  Definition c_add_n := 36.
  Definition c_add := 14.
  Definition c_mul_clo := 5.
  Definition c_mul_nm := 36.
  Definition c_mul_n := 52.
  Definition c_mul := 10.

  Definition add_complexity := LNC.Nat_add_complexity.
  Definition mul_complexity := LNC.Nat_mul_complexity.
End LNA.

Module LA <: ParamArithTimeCostModel.
  Include L. Include LNA.
End LA.
