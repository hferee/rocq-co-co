(** * Complexity of list functions from the standard library

    As in [NatComplexity]: [cbound] proves the bounds, with the smallest
    constants. These functions are
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
  (Import FX : FixTimeCostModel CM BT CB).

  (** ** List tail *)
  Instance complexity_tl {A} `{Ground A} :
    ComplexityBound (@tl A) (fun (lc : ℂI (list A) unit) => 3 ⋉ tt).
  Proof. cbound. Qed.

  Lemma length_complexity {A} `{Ground A} : ComplexityBound (@length A)
    (fun cl : ℂI (list A) unit => (10 * length (val cl) + 8) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance length_complexity.

  Lemma app_complexity {A} `{Ground A} : ComplexityBound (@app A)
    (fun cl : ℂI (list A) unit => 35 ⋉ fun cm : ℂI (list A) unit =>
       (67 * length (val cl) + 7) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance app_complexity.

  (** [seq] is recursive on its second argument; the first one changes. *)
  Lemma seq_complexity : ComplexityBound seq
    (fun cs : ℂI nat unit => 34 ⋉ fun cn : ℂI nat unit => (46 * val cn + 2) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance seq_complexity.

  (** [fold_left] with a function whose partial and full applications cost at
      most [c1] and [c2] (on ground data): a higher-order bound. *)
  Lemma fold_left_complexity {A B} `{Ground A} `{Ground B} (f : A -> B -> A) (c1 c2 : nat) :
    ComplexityBound f (fun _ : ℂI A unit => c1 ⋉ fun _ : ℂI B unit => c2 ⋉ tt) ->
    ComplexityBound (fold_left f)
      (fun cl : ℂI (list B) unit => 35 ⋉ fun cx : ℂI A unit =>
         ((c1 + c2 + 54) * length (val cl) + 7) ⋉ tt).
  Proof. intro Hf. cbound. Qed.
End ListComplexity.
