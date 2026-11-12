(** * This files highlights why the unfolding of fixpoints
  should never be free: any function would have any complexity bound ;
  the induced notion of complexity would be pointless. *)

From Complexity Require Import TimeCostModel TimeArith.


Module UnguardedFix (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT CB).

  (** The rule of [TimeFix], without its premise. *)
  Definition unguarded_fix : Prop :=
    forall A B CA CB (RA : Repr A CA) (RB : Repr B CB) (ar : Arity B) (f : A -> B)
      (F : (A -> B) -> A -> B)
      (cF : ℂI (A -> B) (ℂI A CA -> ℂO CB) -> ℂO (ℂI A CA -> ℂO CB))
      (cf : ℂI A CA -> ℂO CB),
      is_fixpoint ar F f ->
      ComplexityBound F cF ->
      bound_order (fun ca : ℂI A CA => c_fix ⊕ pot <$> (F ⋊ cF) · (f ⋊ cf) · ca) cf ->
      ComplexityBound f cf.

  Theorem every_bound : unguarded_fix -> c_fix = 0 -> c_step = 0 ->
    forall {A B CA CB} `{Repr A CA} `{Repr B CB} (f : A -> B) (cf : ℂI A CA -> ℂO CB),
    ComplexityBound f cf.
  Proof.
    intros Hfix Hc Hs A B CA CB RA RB f cf.
    apply (Hfix A B CA CB RA RB (ar_val B) f (fun g => g) (fun cg => c_step +> pot cg) cf).
    - intro a. exact eq_refl.
    - exact (@id_complexity (A -> B) _ _).
    - apply bound_order_arr. intro ca. cbn. rewrite Hc, Hs. split; [lia | reflexivity].
  Qed.
End UnguardedFix.

