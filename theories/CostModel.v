From Stdlib Require Export Classes.Morphisms Classes.RelationClasses Program.Basics.

(** We axiomatize a notion of complexity and will import it via the module system. *)
Module Type CostModel.

  (** There is a notion of complexity terms to complexity bounds. *)
  Parameter has_complexity  : forall {A B : Type}, A -> B -> Prop.
  (* TODO: for now, we require [has_complexity] to relate elements whose
    types are related by CT. We'll see if this is required. *)

  (** Complexity bounds are preserved by some equivalence relation (on terms)
    and pre-order (on complexity bounds). *)

  Parameter bound_order : forall {B}, B -> B -> Prop.
  Parameter bound_order_po : forall B, PreOrder (@bound_order B).
  Global Existing Instance bound_order_po.

  Parameter has_complexity_ext_eq: forall {A B f},
    Proper ((bound_order) ==> impl) (@has_complexity A B f).
  Global Existing Instance has_complexity_ext_eq.

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  Class ComplexityBound {A B} (f : A) (c : B) := {CB : has_complexity f c}.

  Global Instance ComplexityBound_ext_eq: forall {A B f},
    Proper ((bound_order) ==> impl) (@ComplexityBound A B f).
  Proof. intros ??????[?]. constructor. eapply has_complexity_ext_eq; eauto. Qed.

  (** Useful tactics *)
  (* Replaces the complexity bound with an evar.
   The complexity bound goal will eventually need to be taken from the shelf. *)
  Ltac capply := eapply ComplexityBound_ext_eq; [shelve|].

  (* The ordering on complexity bounds is compatible with the pointwise ordering *)
  Parameter bound_order_ext_eq : forall {A B},
    forall (f g : A -> B), (forall x, bound_order (f x) (g x)) -> bound_order f g.
End CostModel.
