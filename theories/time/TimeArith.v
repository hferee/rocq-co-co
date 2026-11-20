(** * Arithmetic as primitive: a cost model counting operations

    Models where [Nat.add] and [Nat.mul] are primitives, for counting the
    operations of interest as in a course, rather than running times. *)

From Complexity Require Export TimeDatatypes TimeLists TimeFix.

(** The costs of [Nat.add] and [Nat.mul] are constants: one for the partial
    application, the coefficients of a linear bound for [Nat.add] in its
    first argument, and those of a bilinear bound for [Nat.mul]. *)
Module Type NatArithTimeCostModel (Import CM : CostModel) (Import ND : NatData CM).

  Parameter c_add_clo c_add_n c_add : nat.
  Parameter c_mul_clo c_mul_nm c_mul_n c_mul : nat.
  #[global] Hint Unfold c_add_clo c_add_n c_add c_mul_clo c_mul_nm c_mul_n c_mul : costs.

  #[global] Declare Instance add_complexity : ComplexityBound Nat.add
    (fun cn => c_add_clo +> fun cm => (c_add_n * val cn + c_add) >|).

  #[global] Declare Instance mul_complexity : ComplexityBound Nat.mul
    (fun cn => c_mul_clo +> fun cm => (val cn * (c_mul_nm * val cm + c_mul_n) + c_mul) >|).
End NatArithTimeCostModel.

(** The primitives, the constructor [S], booleans and lists, but no case
    analysis on [nat]: functions on numbers are analysed through [Nat.add]
    and [Nat.mul] only. L is an instance, with the bounds of [Nat.add] and
    [Nat.mul] of [NatComplexity] ([LArith]). *)
Module Type ParamArithTimeCostModel := CostModel.CostModel <+ BasicTimeCostModel
  <+ CombinatorTimeCostModel <+ BoolTimeCostModel
  <+ NatData <+ NatCtorTimeCostModel <+ NatArithTimeCostModel
  <+ ListTimeCostModel <+ ListShapes <+ FixTimeCostModel.

(** Only the arithmetic operations are charged: an addition [c_add], a
    multiplication [c_mul], an unfolding [c_fix]; everything else is free.
    The constants are abstract, so that a bound is a linear form whose
    coefficients count the operations ([HornerCount]). Unfoldings cannot
    be free: free unfoldings would give every function every bound
    ([TimeFix], [UnguardedFix]). L is not an instance: unary addition
    takes linear time. *)
Module Type ArithOpsTimeCostModel := ParamArithTimeCostModel
  with Definition c_add_clo := 0 with Definition c_add_n := 0
  with Definition c_mul_clo := 0 with Definition c_mul_nm := 0 with Definition c_mul_n := 0
  with Definition c_clo := 0 with Definition c_frame := 0
  with Definition c_ehd := 0 with Definition c_etl := 0 with Definition c_Lam := 0
  with Definition c_Kc := 0 with Definition c_Ic := 0 with Definition c_compose := 0
  with Definition c_Cc := 0 with Definition c_Sc := 0
  with Definition c_case_bool := 0 with Definition c_S := 0
  with Definition c_cons := 0 with Definition c_case_list := 0.

(** The total number of operations. Unit-cost multiplication computes
    [2 ^ 2 ^ n] in [n] steps: these models do not bound the running time,
    and polynomial bounds in the sizes lose their usual meaning. *)
Module Type ArithCountTimeCostModel := ArithOpsTimeCostModel
  with Definition c_add := 1 with Definition c_mul := 1 with Definition c_fix := 1.
