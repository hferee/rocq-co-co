(** * Complexity of functions over [positive] from the standard library

    As in [NatComplexity]: each function is analysed as defined, with
    [crec] (or [crec_mutual] for [Pos.add] and [Pos.add_carry]) and the
    smallest constants for the shape of the bound. Costs are linear in the
    bit size [Pos.size_nat]. *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel ZCostModel FixCostModel NatComplexity.
From Stdlib Require Import Program.Basics Arith PArith Lia.

(** ** Bit sizes *)

Lemma size_nat_pow_gt p : Pos.to_nat p < 2 ^ Pos.size_nat p.
Proof.
  induction p; cbn [Pos.size_nat]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO,
    ?Nat.pow_succ_r'; cbn; lia.
Qed.

Lemma size_nat_pow_le p : 2 ^ Pos.size_nat p <= 2 * Pos.to_nat p.
Proof.
  induction p; cbn [Pos.size_nat]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO,
    ?Nat.pow_succ_r'; cbn; lia.
Qed.

Lemma size_nat_mul p q : Pos.size_nat (p * q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  enough (2 ^ Pos.size_nat (p * q) < 2 ^ S (Pos.size_nat p + Pos.size_nat q)) as H
    by (apply Nat.pow_lt_mono_r_iff in H; lia).
  pose proof (size_nat_pow_le (p * q)). pose proof (size_nat_pow_gt p).
  pose proof (size_nat_pow_gt q). rewrite Pos2Nat.inj_mul in *.
  rewrite Nat.pow_succ_r', Nat.pow_add_r. nia.
Qed.

Lemma size_nat_succ p : Pos.size_nat p <= Pos.size_nat (Pos.succ p).
Proof. apply Pos.size_nat_monotone, Pos.lt_succ_diag_r. Qed.

Lemma size_nat_pos p : 1 <= Pos.size_nat p.
Proof. destruct p; cbn; lia. Qed.

Module PosComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT) (Import UN : UnitTimeCostModel CM)
  (Import BO : BoolTimeCostModel CM BT) (Import ZM : ZTimeCostModel CM BT)
  (Import FX : FixTimeCostModel CM BT).

  Module NC := NatComplexity CM BT NT CB UN BO FX.
  Import NC.

  Lemma succ_complexity : ComplexityBound Pos.succ
    (fun cp : ℂI positive unit => (4 * Pos.size_nat (ival cp)) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cp; bo_split; destr_inputs; destruct cp; cbn -[Nat.mul];
      try pose proof (size_nat_pos cp); lia.
  Qed.
  Global Existing Instance succ_complexity.

  Lemma pred_double_complexity : ComplexityBound Pos.pred_double
    (fun cp : ℂI positive unit => (4 * Pos.size_nat (ival cp)) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cp; bo_split; destr_inputs; destruct cp; cbn -[Nat.mul];
      try pose proof (size_nat_pos cp); lia.
  Qed.
  Global Existing Instance pred_double_complexity.

  Lemma eqb_complexity : ComplexityBound Pos.eqb
    (fun cp : ℂI positive unit => 2 ⋉ fun cq : ℂI positive unit =>
       (5 * Pos.size_nat (ival cp)) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cp; bo_split; destr_inputs; [cbn; lia |].
    destruct cp, cq; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance eqb_complexity.

  (** [Pos.compare_cont] is recursive on its third argument. *)
  Lemma compare_cont_complexity : ComplexityBound Pos.compare_cont
    (fun cr : ℂI comparison unit => 2 ⋉ fun cp : ℂI positive unit => 1 ⋉
     fun cq : ℂI positive unit => (6 * Pos.size_nat (ival cq)) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cr; bo_split; destr_inputs; [cbn; lia | cbn; lia |].
    destruct cp, cq; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance compare_cont_complexity.

  (** [Pos.add] and [Pos.add_carry] are mutually recursive: the recursion is
      analysed on the function [fun b => if b then Pos.add else
      Pos.add_carry], from which both bounds follow. *)
  Lemma add_mutual_complexity :
    ComplexityBound (fun b : bool => if b then Pos.add else Pos.add_carry)
      (fun cb : ℂI bool unit => 3 ⋉ fun cx : ℂI positive unit => 1 ⋉
       fun cy : ℂI positive unit =>
         (4 * (Pos.size_nat (ival cx) + Pos.size_nat (ival cy))) ⋉ tt).
  Proof.
    crec_mutual; [cbc |].
    intro cb; bo_split; destr_inputs; destruct cb; [cbn; lia .. | |];
      destruct cx, cy; cbn -[Nat.mul]; lia.
  Qed.

  Lemma add_complexity : ComplexityBound Pos.add
    (fun cx : ℂI positive unit => 1 ⋉ fun cy : ℂI positive unit =>
       (4 * (Pos.size_nat (ival cx) + Pos.size_nat (ival cy))) ⋉ tt).
  Proof. exact (apply_complexity (v := true) _ _ add_mutual_complexity). Qed.

  Lemma add_carry_complexity : ComplexityBound Pos.add_carry
    (fun cx : ℂI positive unit => 1 ⋉ fun cy : ℂI positive unit =>
       (4 * (Pos.size_nat (ival cx) + Pos.size_nat (ival cy))) ⋉ tt).
  Proof. exact (apply_complexity (v := false) _ _ add_mutual_complexity). Qed.

  Global Existing Instances add_complexity add_carry_complexity.

  (** [Pos.compare] is [Pos.compare_cont Eq]. *)
  Lemma compare_complexity : ComplexityBound Pos.compare
    (fun cx : ℂI positive unit => 1 ⋉ fun cy : ℂI positive unit =>
       (6 * Pos.size_nat (ival cy)) ⋉ tt).
  Proof.
    capply. unfold Pos.compare. cbc.
    Unshelve. bo_split; destr_inputs; cbn; lia.
  Qed.
  Global Existing Instance compare_complexity.

  (** The recursive step of [Pos.mul] adds [y] to the doubled product: its
      cost depends on the size of the product. *)
  Lemma mul_complexity : ComplexityBound Pos.mul
    (fun cx : ℂI positive unit => 2 ⋉ fun cy : ℂI positive unit =>
       (Pos.size_nat (ival cx) *
          (8 * (Pos.size_nat (ival cx) + Pos.size_nat (ival cy)))) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cx; bo_split; destr_inputs; [cbn; lia |].
    pose proof (size_nat_pos cy).
    destruct cx; cbn -[Nat.mul]; unfold_comb; try pose proof (size_nat_pos cx); [| nia | nia].
    pose proof (size_nat_mul cx cy). nia.
  Qed.
  Global Existing Instance mul_complexity.

  (** [Pos.of_succ_nat n] calls [Pos.succ] [n] times, on numbers of size at
      most the size of the result. *)
  Lemma of_succ_nat_complexity : ComplexityBound Pos.of_succ_nat
    (fun cn : ℂI nat unit =>
       (ival cn * (7 * Pos.size_nat (Pos.of_succ_nat (ival cn))) + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; destruct cn; cbn -[Nat.mul Pos.size_nat]; [lia |].
    unfold_comb. pose proof (size_nat_succ (Pos.of_succ_nat cn)).
    pose proof (size_nat_pos (Pos.of_succ_nat cn)). nia.
  Qed.
  Global Existing Instance of_succ_nat_complexity.

  Lemma of_nat_complexity : ComplexityBound Pos.of_nat
    (fun cn : ℂI nat unit =>
       (ival cn * (9 * Pos.size_nat (Pos.of_nat (ival cn))) + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; destruct cn as [|[|cn]];
      cbn -[Nat.mul Pos.size_nat]; [cbn; lia .. |].
    unfold_comb. pose proof (size_nat_succ (Pos.of_nat (S cn))).
    pose proof (size_nat_pos (Pos.of_nat (S cn))). cbn [Pos.of_nat] in *. nia.
  Qed.
  Global Existing Instance of_nat_complexity.

  (** [Pos.to_nat] is [Pos.iter_op Nat.add p 1]: on unary numbers, the
      accumulator doubles at each step, and so does the cost of the
      additions. *)
  Lemma iter_op_add_complexity : ComplexityBound (Pos.iter_op Nat.add)
    (fun cp : ℂI positive unit => 2 ⋉ fun ca : ℂI nat unit =>
       (5 * (Pos.to_nat (ival cp) - 1) * ival ca + 14 * Pos.size_nat (ival cp)) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cp; bo_split; destr_inputs; [cbn; lia |].
    pose proof (Pos2Nat.is_pos cp).
    destruct cp; cbn -[Nat.mul Pos.to_nat]; unfold_comb;
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *; cbn; nia.
  Qed.
  Global Existing Instance iter_op_add_complexity.

  Lemma to_nat_complexity : ComplexityBound Pos.to_nat
    (fun cp : ℂI positive unit =>
       (5 * Pos.to_nat (ival cp) + 14 * Pos.size_nat (ival cp)) ⋉ tt).
  Proof.
    capply. unfold Pos.to_nat. cbc.
    Unshelve. bo_split; destr_inputs. pose proof (Pos2Nat.is_pos cp).
    cbn -[Nat.mul Pos.size_nat Pos.to_nat]; lia.
  Qed.
  Global Existing Instance to_nat_complexity.
End PosComplexity.
