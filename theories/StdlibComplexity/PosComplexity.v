(** * Complexity of functions over [positive] from the standard library

    As in [NatComplexity]: each function is analysed as defined, with
    [cbound] (or [cbound_mutual] for [Pos.add] and [Pos.add_carry]) and the
    smallest constants for the shape of the bound. Costs are linear in the
    bit size [Pos.size_nat] ([BitSize]). *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel ZCostModel FixCostModel NatComplexity
  BitSize.
From Stdlib Require Import Program.Basics Arith PArith Lia.

Module PosComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT) (Import UN : UnitTimeCostModel CM)
  (Import BO : BoolTimeCostModel CM BT) (Import ZM : ZTimeCostModel CM BT)
  (Import FX : FixTimeCostModel CM BT CB).

  Module NC := NatComplexity CM BT NT CB UN BO FX.
  Import NC.

  Lemma succ_complexity : ComplexityBound Pos.succ
    (fun cp : ℂI positive unit => (11 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance succ_complexity.

  Lemma pred_double_complexity : ComplexityBound Pos.pred_double
    (fun cp : ℂI positive unit => (9 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. size_facts; lia. Qed.
  Global Existing Instance pred_double_complexity.

  Lemma eqb_complexity : ComplexityBound Pos.eqb
    (fun cp : ℂI positive unit => 13 ⋉ fun cq : ℂI positive unit =>
       (60 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance eqb_complexity.

  (** [Pos.compare_cont] is recursive on its third argument. *)
  Lemma compare_cont_complexity : ComplexityBound Pos.compare_cont
    (fun cr : ℂI comparison unit => 9 ⋉ fun cp : ℂI positive unit => 15 ⋉
     fun cq : ℂI positive unit => (101 * Pos.size_nat (val cq)) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance compare_cont_complexity.

  (** [Pos.add] and [Pos.add_carry] are mutually recursive: the recursion is
      analysed on the function [fun b => if b then Pos.add else
      Pos.add_carry], from which both bounds follow. *)
  Lemma add_mutual_complexity :
    ComplexityBound (fun b : bool => if b then Pos.add else Pos.add_carry)
      (fun cb : ℂI bool unit => 6 ⋉ fun cx : ℂI positive unit => 11 ⋉
       fun cy : ℂI positive unit =>
         (32 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt).
  Proof. cbound_mutual. Qed.

  Lemma add_complexity : ComplexityBound Pos.add
    (fun cx : ℂI positive unit => 11 ⋉ fun cy : ℂI positive unit =>
       (32 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt).
  Proof. exact (apply_complexity (v := true) _ _ add_mutual_complexity). Qed.

  Lemma add_carry_complexity : ComplexityBound Pos.add_carry
    (fun cx : ℂI positive unit => 11 ⋉ fun cy : ℂI positive unit =>
       (32 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt).
  Proof. exact (apply_complexity (v := false) _ _ add_mutual_complexity). Qed.

  Global Existing Instances add_complexity add_carry_complexity.

  (** [Pos.compare] is [Pos.compare_cont Eq]. *)
  Lemma compare_complexity : ComplexityBound Pos.compare
    (fun cx : ℂI positive unit => 15 ⋉ fun cy : ℂI positive unit =>
       (101 * Pos.size_nat (val cy)) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance compare_complexity.

  (** The recursive step of [Pos.mul] adds [y] to the doubled product: its
      cost depends on the size of the product. *)
  Lemma mul_complexity : ComplexityBound Pos.mul
    (fun cx : ℂI positive unit => 13 ⋉ fun cy : ℂI positive unit =>
       (Pos.size_nat (val cx) *
          (64 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)))) ⋉ tt).
  Proof. cbound. all: try pose proof (size_nat_mul cx cy); size_facts; nia. Qed.
  Global Existing Instance mul_complexity.

  (** [Pos.of_succ_nat n] calls [Pos.succ] [n] times, on numbers of size at
      most the size of the result. *)
  Lemma of_succ_nat_complexity : ComplexityBound Pos.of_succ_nat
    (fun cn : ℂI nat unit =>
       (val cn * (17 * Pos.size_nat (Pos.of_succ_nat (val cn))) + 6) ⋉ tt).
  Proof. cbound. pose proof (size_nat_succ (Pos.of_succ_nat cn)). size_facts; nia. Qed.
  Global Existing Instance of_succ_nat_complexity.

  Lemma of_nat_complexity : ComplexityBound Pos.of_nat
    (fun cn : ℂI nat unit =>
       (val cn * (41 * Pos.size_nat (Pos.of_nat (val cn))) + 18) ⋉ tt).
  Proof.
    cbound. pose proof (size_nat_succ (Pos.of_nat (S cn))).
    pose proof (size_nat_pos (Pos.of_nat (S cn))). cbn [Pos.of_nat] in *. nia.
  Qed.
  Global Existing Instance of_nat_complexity.

  (** [Pos.to_nat] is [Pos.iter_op Nat.add p 1]: on unary numbers, the
      accumulator doubles at each step, and so does the cost of the
      additions. *)
  Lemma iter_op_add_complexity : ComplexityBound (Pos.iter_op Nat.add)
    (fun cp : ℂI positive unit => 13 ⋉ fun ca : ℂI nat unit =>
       (55 * (Pos.to_nat (val cp) - 1) * val ca + 138 * Pos.size_nat (val cp)) ⋉ tt).
  Proof.
    cbound. all: pose proof (Pos2Nat.is_pos cp);
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *; nia.
  Qed.
  Global Existing Instance iter_op_add_complexity.

  Lemma to_nat_complexity : ComplexityBound Pos.to_nat
    (fun cp : ℂI positive unit =>
       (55 * Pos.to_nat (val cp) + 138 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance to_nat_complexity.
End PosComplexity.
