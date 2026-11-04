(** * Complexity of functions over [nat] from the standard library

    Each function is analysed as defined in the standard library, by
    [cbound] ([FixCostModel]).

    The constants are the smallest ones for the shape of each bound: they
    were found by stating the bound with abstract constants, which [cbound]
    turns into the inequalities that the recurrence requires. The first cost
    ([35] for [Nat.add]) is the cost of the partial application to the first
    argument; the cost of a step of the recursion includes it, since the
    recursive call is a partial application too. *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel FixCostModel.
From Stdlib Require Import Program.Basics Arith Lia.

Module NatComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT)
  (Import FX : FixTimeCostModel CM BT CB).

  Lemma add_complexity : ComplexityBound Nat.add
    (fun cn : ℂI nat unit => 35 ⋉ fun cm : ℂI nat unit => (55 * val cn + 7) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance add_complexity.

  (** [Nat.sub] is recursive on its first argument and matches on the second
      one. *)
  Lemma sub_complexity : ComplexityBound Nat.sub
    (fun cn : ℂI nat unit => 34 ⋉ fun cm : ℂI nat unit => (64 * val cn + 8) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance sub_complexity.

  Lemma eqb_complexity : ComplexityBound Nat.eqb
    (fun cn : ℂI nat unit => 35 ⋉ fun cm : ℂI nat unit => (54 * val cn + 8) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance eqb_complexity.

  Lemma leb_complexity : ComplexityBound Nat.leb
    (fun cn : ℂI nat unit => 21 ⋉ fun cm : ℂI nat unit => (41 * val cn + 6) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance leb_complexity.

  (** [Nat.ltb] is not recursive: its complexity follows from the one of
      [Nat.leb] by compilation alone. *)
  Lemma ltb_complexity : ComplexityBound Nat.ltb
    (fun cn : ℂI nat unit => 9 ⋉ fun cm : ℂI nat unit => (41 * val cn + 74) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance ltb_complexity.

  (** The recursive branch of [Nat.mul] calls [Nat.add]. *)
  Lemma mul_complexity : ComplexityBound Nat.mul
    (fun cn : ℂI nat unit => 9 ⋉ fun cm : ℂI nat unit =>
       (val cn * (55 * val cm + 67) + 13) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance mul_complexity.

  (** [Nat.pow] is recursive on its second argument, and the step [m] calls
      [Nat.mul] on [n ^ m]: the sum of the [n ^ i] is bounded by
      [m * n ^ m]. *)
  Lemma pow_complexity : ComplexityBound Nat.pow
    (fun cn : ℂI nat unit => 32 ⋉ fun cm : ℂI nat unit =>
       (55 * val cm * val cn ^ val cm + val cm * (67 * val cn + 62) + 2) ⋉ tt).
  Proof. cbound. destruct cn; [destruct cm; cbn; lia | nia]. Qed.
  Global Existing Instance pow_complexity.
End NatComplexity.
