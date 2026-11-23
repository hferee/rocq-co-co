(** * Ground types

    The data whose complexities carry no information: numbers, booleans,
    pairs of numbers, ... *)
    
    
(* Note: with this definition, lists of ground type is not ground.
  Let's see later if we need/can set a more general definition. *)

From Complexity Require Export CostModelCore.

Module GroundTypes (Import CM : CostModelAxioms).

  (** It is not clear yet if this is the most relevant definition. *)
  Class IsGround {A CA} (R : Repr A CA) : Type := {
    ground_inhabited :: Inhabited CA;
    ground_indiscrete :: IndiscreteOrder (@bound_order A CA R) }.

  Definition ground_order {A CA} {R : Repr A CA} {G : IsGround R} (c c' : CA) : bound_order c c' :=
    indiscrete c c'.

  Lemma unit_indiscrete {A} (R : Repr A unit) : IndiscreteOrder (@bound_order A unit R).
  Proof. intros [] []. reflexivity. Qed.

  Global Instance unit_ground {A} (R : Repr A unit) : IsGround R :=
    {| ground_inhabited := unit_inhabited; ground_indiscrete := unit_indiscrete R |}.
End GroundTypes.

Module Type GroundCostModel := CostModelCore.CostModelCore <+ GroundTypes.
