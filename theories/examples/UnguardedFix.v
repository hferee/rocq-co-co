(** * This files highlights why the unfolding of fixpoints
  should never be free: any function would have any complexity bound ;
  the induced notion of complexity would be pointless. *)

From Complexity Require Import TimeCostModel TimeArith.


Module UnguardedFix (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT CB).

  (** The rule of [TimeFix], without its premise. *)
  Definition unguarded_fix : Prop :=
    forall E CE A B CA CB (RE : Repr E CE) (RA : Repr A CA) (RB : Repr B CB)
      (ar : Arity B) (f : E -> A -> B)
      (F : env E (A -> B) -> A -> B)
      (cF : ℂI (env E (A -> B)) (CE * (ℂI A CA -> ℂO CB)) -> ℂO (ℂI A CA -> ℂO CB))
      (cf : ℂI E CE -> ℂO (ℂI A CA -> ℂO CB)),
      (forall e, is_fixpoint ar (fun g => F (ECons e g)) (f e)) ->
      ComplexityBound F cF ->
      bound_order
        (fun ce : ℂI E CE => c_clo +> fun ca : ℂI A CA =>
           c_fix ⊕ pot <$> (F ⋊ cF) · (ECons (val ce) (f (val ce)) ⋊ (pot ce, res (cf ce))) · ca)
        cf ->
      ComplexityBound f cf.

  (** Any function [f] is a fixpoint of the functional that reads it in its
      environment ([ehd]): the unfolding only costs this read. *)
  Theorem every_bound : unguarded_fix -> c_fix = 0 -> c_step = 0 ->
    forall {A B CA CB} `{Repr A CA} `{Repr B CB} (f : A -> B) (cf : ℂI A CA -> ℂO CB),
    ComplexityBound f cf.
  Proof.
    intros Hfix Hc Hs A B CA CB RA RB f cf.
    assert (H : ComplexityBound (fun _ : unit => f) (fun _ => c_clo +> cf)).
    { apply (Hfix unit unit A B CA CB _ RA RB (ar_val B) (fun _ => f) (@ehd unit (A -> B))
               (fun ce => c_step +> snd (pot ce)) (fun _ => c_clo +> cf)).
      - intros e a. exact eq_refl.
      - exact ehd_complexity.
      - apply bound_order_arr. intro ce. split; [apply Nat.le_refl |].
        apply bound_order_arr. intro ca. cbn. rewrite Hc, Hs. split; [lia | reflexivity]. }
    exact (apply_complexity _ tt_complexity H).
  Qed.
End UnguardedFix.

