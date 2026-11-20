(** * Ground types

    The data whose complexities carry no information: numbers, booleans,
    pairs of numbers, ... ([IsGround]); not lists, whose complexities have
    their lengths ([wf_list]). The data types give their ground
    instances with their axioms ([OptionGround], [ProdGround], ...). *)

From Complexity Require Export CostModelCore.

Module GroundTypes (Import CM : CostModelAxioms).

  (** Ground data, in general: their complexities carry no information. Their
      type is inhabited, and their order is indiscrete: any two are related.
      The data of complexity [unit] are ground; so are the lists, options,
      pairs and sums of ground data ([TimeLists], [TimeDatatypes]). The
      bounds whose result is ground end with [>|]: the complexity of the
      result is then any one ([inhabitant]). *)
  Class IsGround {A CA} (R : Repr A CA) : Type := {
    ground_inhabited :: Inhabited CA;
    ground_indiscrete :: IndiscreteOrder (@bound_order A CA R) }.

  Definition ground_order {A CA} {R : Repr A CA} {G : IsGround R} (c c' : CA) : bound_order c c' :=
    indiscrete c c'.

  (** The complexities [unit] are related by reflexivity, once destructed:
      it applies to any terms of type [unit], such as [res (c ca)], which
      [reflexivity] does not relate to [tt] (there is no eta-rule for
      [unit]). *)
  Lemma unit_indiscrete {A} (R : Repr A unit) : IndiscreteOrder (@bound_order A unit R).
  Proof. intros [] []. reflexivity. Qed.

  Global Instance unit_ground {A} (R : Repr A unit) : IsGround R :=
    {| ground_inhabited := unit_inhabited; ground_indiscrete := unit_indiscrete R |}.
End GroundTypes.

(** The core of the cost model with the ground types: the bounds in the
    sizes ([Bounds], [HOBounds]) are stated over it. *)
Module Type GroundCostModel := CostModelCore.CostModelCore <+ GroundTypes.
