(** * One axiom for all fixpoints

    A Gallina axiom cannot quantify over the syntax of [fix] terms (their
    number of arguments, recursive argument, mutual functions, ...). Instead,
    [fix_complexity] uses the unfolding equation of a recursive function [f]:
    `f a = F f a` (pointwise in all the arguments), where the functional `F`
    is the body of the fixpoint, abstracted over the recursive calls. The
    candidate complexity [cf] of [f] is a bound as soon as it bounds the cost
    of one unfolding, plus [c_fix], where the recursive calls cost what [cf]
    says.

    This covers any structural recursion (any arity, recursive argument in
    any position, matches on other arguments, recursive calls on deeper
    subterms, polymorphic fixpoints) and, through an indexed function, mutual
    recursion.

    Since the axiom holds for every function satisfying the equation,
    [ComplexityBound f c] now means that the function [f] is computable within
    [c], rather than that a particular term defining it is. This is sound
    because each unfolding costs at least one ([c_fix ⊕] below, with
    [1 <= c_fix]): the recurrence cannot be satisfied by an unfolding that
    does not terminate. With free unfoldings, every function would have every
    bound ([UnguardedFix]). The condition is a premise of the rule, not an
    axiom, so that a model where [c_fix] is [0] stays consistent: its
    recursive functions cannot be analysed. *)

From Complexity Require Export TimeCombinators.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** The functional of a recursive function is compiled with the combinators
    ([crec] leaves it to [cbc]): this module type depends on their model. As
    for the combinators, the model of fixpoints ([FixTimeCostModel], at the
    end) is made of its axioms and of the tactics that they justify, in a
    functor ([FixTactics]). *)
Module Type FixTimeCostAxioms
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT).

  (** The cost of an unfolding. *)
  Parameter c_fix : nat.
  #[global] Hint Unfold c_fix : costs.

  Parameter fix_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
    (ar : Arity B) (f : A -> B)
    (F : (A -> B) -> A -> B)
    (cF : ℂI (A -> B) (ℂI A CA -> ℂO CB) -> ℂO (ℂI A CA -> ℂO CB))
    (cf : ℂI A CA -> ℂO CB),
    1 <= c_fix ->
    is_fixpoint ar F f ->
    ComplexityBound F cF ->
    bound_order (fun ca : ℂI A CA => c_fix ⊕ pot <$> (F ⋊ cF) · (f ⋊ cf) · ca) cf ->
    ComplexityBound f cf.
End FixTimeCostAxioms.

Module FixTactics
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import FX : FixTimeCostAxioms CM BT CB).

  (** In a goal [ComplexityBound f cf] where [f] is a recursive function,
      [crec] leaves the goals `ComplexityBound F ?cF` (to be solved by
      [cbc]) and the recurrence on [cf]. [crec_mutual] does the same for
      [fun b => if b then f1 else f2], where [f1] and [f2] are mutually
      recursive. The premise [1 <= c_fix] is proved by [cfix_pos], from
      the value of [c_fix] or from a hypothesis. *)
  Ltac cfix_pos := solve [assumption | autounfold with costs; lia].
  Ltac crec_with eq :=
    let H := fresh "Hunfold" in
    let Hpos := fresh "Hpos" in
    eq; intro H; assert (Hpos : 1 <= c_fix) by cfix_pos;
    eapply (fix_complexity _ _ _ _ _ Hpos H); clear H Hpos.
  Ltac crec := crec_with fix_equation.
  Ltac crec_mutual := crec_with fix_equation_mutual.

  (** ** Proofs of bounds

      [cbound] ([TimeCombinators]) extended to recursive functions: if
      the function is recursive, its functional is compiled and the
      recurrence of [fix_complexity] is reduced to inequalities between
      costs; otherwise, the previous [cbound_start] applies. The extension
      holds in every model with fixpoints, and so in the hint of
      [TimeCombinators] for bounds without instance. [cbound_mutual] does
      the same for mutually recursive functions (see [crec_mutual]). *)
  Ltac2 Set cbound_start as previous := fun () =>
    match Control.case (fun () => ltac1:(crec)) with
    | Val _ => Control.dispatch [(fun () => ltac1:(cbc_found)); (fun () => ())]
    | Err _ => previous ()
    end.
  Ltac cbound_mutual := crec_mutual; [cbc_found | cfinish].
End FixTactics.

Module Type FixTimeCostModel
  (CM : CostModel) (BT : BasicTimeCostModel CM) (CB : CombinatorTimeCostModel CM BT) :=
  FixTimeCostAxioms CM BT CB <+ FixTactics CM BT CB.

