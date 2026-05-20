From Complexity Require Import SimpleCostModel.
From Stdlib Require Import Program.Basics Lia List.

Module Type ListTimeCostModel
  (Import CM : CostModel) (Import BTM : BasicTimeCostModel CM).

  (* The cost of a list is the list of costs.
    Other possible cost models: the maxiumum cost or the sum of the costs. *)
(*   Parameter CT_list: forall {A CA : Type} `{CT A CA}, CT (list A) (list CA).
  Global Existing Instance CT_list. *)

  (* The complexity of a list is exactly the complexity of its elements *)
  (* This mostly makes sense for lists containing functions, not ground types *)
  (* See GroundListCostModel for a simpler one *)
  Parameter ComplexityBound_list : forall {A CA} (l : list A) (lc : list CA),
    ComplexityBound l lc <-> Forall2 ComplexityBound l lc.

  Lemma ComplexityBound_list_length: forall {A CA} (l : list A) (lc : list CA),
    ComplexityBound l lc -> length l = length lc.
  Proof. now intros * HC%ComplexityBound_list%Forall2_length. Qed.

  (* List constructors *)
  Parameter nil_complexity: forall {A CA : Type},
    ComplexityBound (@nil A) (@nil CA).
  Global Existing Instance nil_complexity.

  (* TODO: annoyingly, this is required for cons_complexity to find the typeclass instance *)
(*   Global Instance CT_cons {A CA : Type}: CT (A -> list A -> list A)
                        (ℂI A -> ℂO (ℂI (list A) -> ℂO (list CA))).
  Proof. typeclasses eauto. Defined. *)

  Parameter cons_complexity: forall {A CA : Type},
    ComplexityBound (@cons A)
                    (fun (h : ℂI A CA) => 1 ⋉ (
                     fun (t : ℂI (list A) (list CA)) => 1 ⋉ (icomp h :: icomp t))).
  Global Existing Instance cons_complexity.

  Parameter list_match_complexity:
    forall {A CA : Type} {B CB} (v : B) (f : A -> list A -> B)
    (cv : CB) (cf : ℂI A CA -> ℂO(ℂI (list A) (list CA) -> ℂO CB)),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun l => match l with
                | nil => v
                | h :: t => f h t
                end)
      (fun (lc : ℂI (list A) (list CA)) => 1 ⊕ (* 1 for the match *)
                match ival lc, icomp lc with
                | h :: t, hc :: tc => 
                    (ret (t ⋊ tc)) O>>=O ((h ⋊ hc) I>>=I (f ⋊ cf)) >>|
                    (* TODO: maybe define this 2-ary monadic function application. *)
                | nil, nil => ret cv
                | _, _ => ret cv (* should not happen *)
                end).
  Global Existing Instance list_match_complexity.
  (* TODO: Recursion operator *)

End ListTimeCostModel.

(* TODO: move *)
(* Tries to solve known complexity bounds *)
Ltac ctac := typeclasses eauto.

(* Example of derived complexity bounds for list operators *)
Module Type ListTimeExamples
  (Import CM : CostModel)
  (Import BTM : BasicTimeCostModel CM)
  (Import LM : ListTimeCostModel CM BTM).

  (** ** List tail *)
  Instance complexity_tl {A CA} :
    ComplexityBound (@tl A) (fun (lc : ℂI (list A) (list CA)) => 3 ⋉ (tl (icomp lc))).
  Proof.
    unfold tl.
    capply.
    apply list_match_complexity.
    - ctac.
    - eapply constant_complexity.
      apply id_complexity.
    Unshelve. apply bound_order_ext_eq. intros [l lc].
    unfold ObindO, IbindI. simpl.
    (* TODO: bound_order is compatible with products *)
    (* TODO in ℂI A, we need to know that the element has the given complexity.
    In our case, we also need that the complexity of a list is exactly the complexity
    of its elements *)
    assert(HCl : ComplexityBound l lc) by admit. (* need to store this in ℂI *)
    assert (Hlen := ComplexityBound_list_length l lc HCl).
    case l as [|h t]; destruct lc as [|hc tc].
    + admit. (* ok with some assumption on bound_order *)
    + inversion Hlen.
    + inversion Hlen.
    +  admit. (* ok with some assumption on bound_order *)
Admitted.

  (** ** List tail *)
  (* TODO: *)

End ListTimeExamples.


