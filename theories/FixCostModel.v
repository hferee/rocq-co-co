(** * One axiom for all fixpoints

    A Gallina axiom cannot quantify over the syntax of [fix] terms (their
    number of arguments, recursive argument, mutual functions, ...). Instead,
    [fix_complexity] uses the unfolding equation of a recursive function [f]:
    [f a = F f a] (pointwise in all the arguments), where the functional [F]
    is the body of the fixpoint, abstracted over the recursive calls. The
    candidate complexity [cf] of [f] is a bound as soon as it bounds the cost
    of one unfolding, plus one, where the recursive calls cost what [cf] says.

    This covers any structural recursion (any arity, recursive argument in
    any position, matches on other arguments, recursive calls on deeper
    subterms, polymorphic fixpoints) and, through an indexed function, mutual
    recursion.

    Since the axiom holds for every function satisfying the equation,
    [ComplexityBound f c] now means that the function [f] is computable within
    [c], rather than that a particular term defining it is. This is sound
    because each unfolding costs at least one (the [1 ⊕] below): the
    recurrence cannot be satisfied by an unfolding that does not
    terminate. *)

From Complexity Require Export Arity.
From Complexity Require Import CostModel HOCostModel Compile.

Module Type FixTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  Parameter fix_complexity : forall {A B CA CB} (ar : Arity B) (f : A -> B)
    (F : (A -> B) -> A -> B)
    (cF : ℂI (A -> B) (ℂI A CA -> ℂO CB) -> ℂO (ℂI A CA -> ℂO CB))
    (cf : ℂI A CA -> ℂO CB),
    is_fixpoint ar F f ->
    ComplexityBound F cF ->
    (forall ca : ℂI A CA,
       bound_order (1 ⊕ ((ca I>>=O ((f ⋊ cf) I>>=I (F ⋊ cF))) >>|)) (cf ca)) ->
    ComplexityBound f cf.

  (** In a goal [ComplexityBound f cf] where [f] is a recursive function,
      [crec] leaves the goals [ComplexityBound F ?cF] (to be solved by
      [cbc]) and the recurrence on [cf]. [crec_mutual] does the same for
      [fun b => if b then f1 else f2], where [f1] and [f2] are mutually
      recursive. *)
  Ltac crec_with eq :=
    let H := fresh "Hunfold" in
    eq; intro H; eapply (fix_complexity _ _ _ _ _ H); clear H.
  Ltac crec := crec_with fix_equation.
  Ltac crec_mutual := crec_with fix_equation_mutual.
End FixTimeCostModel.
