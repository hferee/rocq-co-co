(** * Complexity of functions over [nat] from the standard library

    Each function is analysed as defined in the standard library: [crec]
    states the unfolding equation of the fixpoint ([FixCostModel]), [cbc]
    finds the complexity of its functional, and the remaining goal is the
    recurrence for the claimed bound, which [bo_split] and [destr_inputs]
    turn into inequalities between costs.

    The constants are the smallest ones for the shape of each bound: they
    were found by stating the bound with abstract constants and reading the
    inequalities that the recurrence requires. The first cost ([2] for
    [Nat.add]) is the cost of the partial application to the first argument;
    the cost of a step of the recursion includes it, since the recursive call
    is a partial application too. *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel FixCostModel.
From Stdlib Require Import Program.Basics Arith Lia.

Module NatComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT)
  (Import FX : FixTimeCostModel CM BT).

  Lemma add_complexity : ComplexityBound Nat.add
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit => (5 * ival cn + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul]; [lia |].
    destruct cn; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance add_complexity.

  (** [Nat.sub] is recursive on its first argument and matches on the second
      one. *)
  Lemma sub_complexity : ComplexityBound Nat.sub
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit => (6 * ival cn + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul]; [lia |].
    destruct cn, cm; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance sub_complexity.

  Lemma eqb_complexity : ComplexityBound Nat.eqb
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit => (5 * ival cn + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul]; [lia |].
    destruct cn, cm; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance eqb_complexity.

  Lemma leb_complexity : ComplexityBound Nat.leb
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit => (5 * ival cn + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul]; [lia |].
    destruct cn, cm; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance leb_complexity.

  (** [Nat.ltb] is not recursive: its complexity follows from the one of
      [Nat.leb] by compilation alone. *)
  Lemma ltb_complexity : ComplexityBound Nat.ltb
    (fun cn : ℂI nat unit => 0 ⋉ fun cm : ℂI nat unit => (5 * ival cn + 11) ⋉ tt).
  Proof.
    capply. unfold Nat.ltb. cbc.
    Unshelve. bo_split; destr_inputs; unfold_comb; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance ltb_complexity.

  (** The recursive branch of [Nat.mul] calls [Nat.add]. *)
  Lemma mul_complexity : ComplexityBound Nat.mul
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit =>
       (ival cn * (5 * ival cm + 9) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul]; [lia |].
    destruct cn; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance mul_complexity.

  (** [Nat.pow] is recursive on its second argument, and the step [m] calls
      [Nat.mul] on [n ^ m]: the sum of the [n ^ i] is bounded by
      [m * n ^ m]. *)
  Lemma pow_complexity : ComplexityBound Nat.pow
    (fun cn : ℂI nat unit => 2 ⋉ fun cm : ℂI nat unit =>
       (5 * ival cm * ival cn ^ ival cm + ival cm * (9 * ival cn + 9) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cn; bo_split; destr_inputs; cbn -[Nat.mul Nat.pow]; [lia |].
    destruct cm as [|m]; cbn -[Nat.mul Nat.pow]; [lia |].
    rewrite Nat.pow_succ_r'.
    destruct cn as [|n]; [destruct m; cbn -[Nat.mul]; lia |].
    unfold_comb; generalize (S n ^ m); intro X; nia.
  Qed.
  Global Existing Instance pow_complexity.
End NatComplexity.
