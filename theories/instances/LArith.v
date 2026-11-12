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
  (** The constants are those of the bounds of [NatComplexity], read in
      their statements: they follow the analyses. *)
  Definition c_add_clo : nat := ltac:(
    lazymatch type of LNC.Nat_add_complexity with
    | ComplexityBound _ (fun _ => ?a +> _) => exact a end).
  Definition c_add_n : nat := ltac:(
    lazymatch type of LNC.Nat_add_complexity with
    | ComplexityBound _ (fun cn => _ +> fun _ => (?b * @?v cn + _) +> _) => exact b end).
  Definition c_add : nat := ltac:(
    lazymatch type of LNC.Nat_add_complexity with
    | ComplexityBound _ (fun cn => _ +> fun _ => (_ * @?v cn + ?c) +> _) => exact c end).
  Definition c_mul_clo : nat := ltac:(
    lazymatch type of LNC.Nat_mul_complexity with
    | ComplexityBound _ (fun _ => ?a +> _) => exact a end).
  Definition c_mul_nm : nat := ltac:(
    lazymatch type of LNC.Nat_mul_complexity with
    | ComplexityBound _ (fun cn => _ +> fun cm => (@?n cn * (?b * @?m cm + _) + _) +> _) => exact b end).
  Definition c_mul_n : nat := ltac:(
    lazymatch type of LNC.Nat_mul_complexity with
    | ComplexityBound _ (fun cn => _ +> fun cm => (@?n cn * (_ * @?m cm + ?c) + _) +> _) => exact c end).
  Definition c_mul : nat := ltac:(
    lazymatch type of LNC.Nat_mul_complexity with
    | ComplexityBound _ (fun cn => _ +> fun cm => (@?n cn * (_ * @?m cm + _) + ?d) +> _) => exact d end).

  Definition add_complexity := LNC.Nat_add_complexity.
  Definition mul_complexity := LNC.Nat_mul_complexity.
End LNA.

Module LA <: ParamArithTimeCostModel.
  Include L. Include LNA.
End LA.
