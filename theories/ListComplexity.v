(** * Complexity of list functions from the standard library

    As in [NatComplexity]: [crec] states the unfolding equation of the
    fixpoint, [cbc] finds the complexity of its functional, and the
    recurrence is checked for the smallest constants. These functions are
    defined in sections: their type and function parameters are fixed
    arguments of the fixpoint. A functional parameter comes with a
    hypothesis on its complexity. *)

From Complexity Require Import CostModel HOCostModel NatCostModel GroundListCostModel
  Combinators Compile CombinatorCostModel UnitCostModel BoolCostModel
  FixCostModel.
From Stdlib Require Import Program.Basics List Arith Lia.
Import ListNotations.

Module ListComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT) (Import LM : ListTimeCostModel CM BT)
  (Import FX : FixTimeCostModel CM BT).

  (** ** List tail *)
  Instance complexity_tl {A} :
    ComplexityBound (@tl A) (fun (lc : ℂI (list A) unit) => 1 ⋉ tt).
  Proof.
    capply. unfold tl. cbc.
    Unshelve. bo_split; destr_inputs; destruct lc; cbn; lia.
  Qed.

  Lemma length_complexity {A} : ComplexityBound (@length A)
    (fun cl : ℂI (list A) unit => (4 * length (ival cl) + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cl; bo_split; destr_inputs; destruct cl; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance length_complexity.

  Lemma app_complexity {A} : ComplexityBound (@app A)
    (fun cl : ℂI (list A) unit => 2 ⋉ fun cm : ℂI (list A) unit =>
       (6 * length (ival cl) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cl; bo_split; destr_inputs; [cbn; lia |].
    destruct cl; cbn; ring_simplify; try lia.
  Qed.
  Global Existing Instance app_complexity.

  (** [seq] is recursive on its second argument; the first one changes. *)
  Lemma seq_complexity : ComplexityBound seq
    (fun cs : ℂI nat unit => 2 ⋉ fun cn : ℂI nat unit => (8 * ival cn + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cs; bo_split; destr_inputs; [cbn; ring_simplify; try lia |].
    destruct cn; cbn -[Nat.mul]; ring_simplify; try lia.
  Qed. (* TODO: why did the bounds increase when we started to use FixComplexity? *)
  Global Existing Instance seq_complexity.

  (** [fold_left] with a function whose partial and full applications cost at
      most [c1] and [c2] (on ground data): a higher-order bound. *)
  Lemma fold_left_complexity {A B} (f : A -> B -> A) (c1 c2 : nat) :
    ComplexityBound f (fun _ : ℂI A unit => c1 ⋉ fun _ : ℂI B unit => c2 ⋉ tt) ->
    ComplexityBound (fold_left f)
      (fun cl : ℂI (list B) unit => 2 ⋉ fun cx : ℂI A unit =>
         ((c1 + c2 + 4) * length (ival cl) + 2) ⋉ tt).
  Proof.
    intro Hf. crec; [cbc |].
    intro cl; bo_split; destr_inputs; [cbn; lia |].
    destruct cl; cbn -[Nat.mul]; ring_simplify; try lia.
  Qed.
End ListComplexity.
