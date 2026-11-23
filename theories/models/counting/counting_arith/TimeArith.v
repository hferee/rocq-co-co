(** * Arithmetic as primitive: a cost model counting operations

    Models where [Nat.add] and [Nat.mul] are primitives, for counting the
    operations of interest as in a course, rather than running times. *)

From Complexity Require Export TimeDatatypes TimeLists TimeFix.

(** The costs of [Nat.add] and [Nat.mul] are constants. They are defined as
  parameters so that we can distinguish between both. *)
Module Type NatArithTimeCostModel (Import CM : CostModel) (Import ND : NatData CM).
  Local Abbreviation ℂO := (ℂO' Cost).
  Parameter c_add_clo c_add : Cost.
  Parameter c_mul_clo  c_mul : Cost.
  #[global] Hint Unfold c_add c_mul : costs.

  #[global] Declare Instance add_complexity : ComplexityBound Nat.add
    (fun cn : ℂI nat unit => czero +> fun cm : ℂI nat unit => c_add >|).

  #[global] Declare Instance mul_complexity : ComplexityBound Nat.mul
    (fun cn : ℂI nat unit => czero +> fun cm : ℂI nat unit => c_mul >|).
End NatArithTimeCostModel.

(** The primitives, the constructor [S], booleans and lists, but no case
    analysis on [nat]: functions on numbers are analysed through [Nat.add]
    and [Nat.mul] only. *)
Module Type ParamArithTimeCostModel := NatCostModel <+ BasicTimeCostModel
  <+ CombinatorTimeCostModel <+ BoolTimeCostModel
  <+ NatData <+ NatCtorTimeCostModel <+ NatArithTimeCostModel
  <+ ListTimeCostModel <+ ListWf <+ FixTimeCostModel.

(** Only the arithmetic operations are charged: an addition [c_add], a
    multiplication [c_mul], an unfolding [c_fix]; everything else is free.
    Unfoldings cannot be free: free unfoldings would give every function every 
    bound ([TimeFix], [UnguardedFix]). *)
Module Type ArithOpsTimeCostModel := ParamArithTimeCostModel
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

(** ** [S] is free

    In these models, an application of [S] costs nothing: the lower bound
    [succ_not_free] of L ([NatLowerBound]), whose statement is negated
    here, does not hold. *)

From Stdlib Require Import Lia.

Module ArithOpsSuccFree (Import M : ArithOpsTimeCostModel).
  Local Abbreviation ℂO := (ℂO' Cost).
  Lemma succ_free :
    ~ (forall c : ℂI nat unit -> ℂO unit, ComplexityBound S c -> forall cn, 1 <= cost (c cn)).
  Proof.
    intro H. pose proof (H _ S_complexity (0 ⋊ tt)) as H'.
    autounfold with costs in H'. cbn in H'. lia.
  Qed.
End ArithOpsSuccFree.
