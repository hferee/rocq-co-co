(** * Releases beyond frames: scopes and loops

    Two kinds of rules of the peak space model ([SpaceCostModel]), where a
    cost may free memory, over the generic cost model ([Generic]):
    - a scope whose result is ground data frees the cells of its
      environment after its body, as a ground value cannot reach them: the
      call of a closure ([Lam_ground_complexity]) and the case analyses of
      [nat] and of lists;
    - a tail-recursive function written as a loop ([while_unfold]) runs its
      iterations one after the other ([while_complexity]): an iteration is
      over, frees included, when the next one starts. With the fixpoint
      rule ([FixCosts]), a recursive call is part of the body of its caller,
      whose cells stay allocated during the call.

    These are axioms of the peak space model, which has no instance. *)

From Complexity Require Export DatatypeCosts ListCosts.
From Stdlib Require Import List.

(** [f] is a loop: while [t a] is false, [a] becomes [n a]; then [f a] is
    [s a]. *)
Definition while_unfold {A C} (t : A -> bool) (s : A -> C) (n : A -> A) (f : A -> C) (a : A) : C :=
  if t a then s a else f (n a).

Module Type PeakSpaceAxioms
  (Import CM : CostModel) (Import BT : BasicCostModel CM)
  (Import CB : CombinatorCostModel CM BT)
  (Import BD : BoolData CM) (Import ND : NatData CM) (Import NC : NatCaseCostModel CM BT CB ND)
  (Import LD : ListData CM) (Import LC : ListCaseCostModel CM BT CB LD).

  (** The cells freed at the end of a scope: the argument of a call
      ([c_unLam]), the arguments of a constructor ([c_uncase_nat],
      [c_uncase_list]); and one iteration of a loop ([c_iter]). *)
  Parameter c_unLam c_uncase_nat c_uncase_list c_iter : Cost.
  #[global] Hint Unfold c_unLam c_uncase_nat c_uncase_list c_iter : costs.

  (** ** Scopes with a ground result

      Preferred to the rules of [CombinatorCosts] and [DatatypeCosts]
      (priority [0]) when the result is ground. *)
  #[global] Declare Instance Lam_ground_complexity :
    forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} {RB : Repr B CB} {GB : IsGround RB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => c_clo +>
       fun ce : ℂI E CE => c_clo +>
       fun ca : ℂI A CA =>
         c_Lam ⊕ cost_after (pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))) c_unLam) | 0.

  #[global] Declare Instance nat_case_ground_complexity :
    forall {E CE A CA} `{Repr E CE} {RA : Repr A CA} {GA : IsGround RA},
    ComplexityBound (@nat_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cs : ℂI (env E nat -> A) (ℂI (env E nat) (CE * unit) -> ℂO CA) => c_clo +>
       fun cn : ℂI (E -> nat) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_nat ⊕ framed (pot cn ce) (fun _ =>
         cost_after
           (match val cn (val ce) with
            | O => pot cz ce
            | S k => pot cs (ECons (val ce) k ⋊ (pot ce, tt))
            end) c_uncase_nat)) | 0.

  #[global] Declare Instance list_case_ground_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} {RA : Repr A CA} {GA : IsGround RA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * CX) * list CX) -> ℂO CA) => c_clo +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO (list CX)) => c_clo +>
       fun ce : ℂI E CE => c_case_list ⊕ framed (pot cl ce) (fun _ =>
         cost_after
           (match val cl (val ce) with
            | cons h t =>
                pot cc (ECons (ECons (val ce) h) t
                          ⋊ ((pot ce, hd cdefault (res (pot cl ce))), tl (res (pot cl ce))))
            | nil => pot cz ce
            end) c_uncase_list)) | 0.

  (** ** Loops

      An iteration ([c_iter]), the test in a frame, then the result, or the
      next value in a frame and the next iteration. As [c_fix], an
      iteration is absorbed by no cost: the premise rules out the loops
      that never stop ([UnguardedFix]). *)
  Parameter while_complexity : forall {A CA C CC} `{Repr A CA} `{Repr C CC}
      (t : A -> bool) (s : A -> C) (n : A -> A)
      (ct : ℂI A CA -> ℂO unit) (cs : ℂI A CA -> ℂO CC) (cn : ℂI A CA -> ℂO CA)
      (f : A -> C) (cf : ℂI A CA -> ℂO CC),
    (forall c, ~ cle (c_iter +c c) c) ->
    (forall a, f a = while_unfold t s n f a) ->
    ComplexityBound t ct -> ComplexityBound s cs -> ComplexityBound n cn ->
    bound_order
      (fun ca : ℂI A CA => c_iter ⊕ framed (ct ca) (fun _ =>
         if t (val ca) then cs ca
         else framed (cn ca) (fun cn' => cf (n (val ca) ⋊ cn')))) cf ->
    ComplexityBound f cf.
End PeakSpaceAxioms.
