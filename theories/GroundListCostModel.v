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
  Parameter ComplexityBound_list : forall {A} (l : list A), ComplexityBound l tt.
  Existing Instance ComplexityBound_list.
  (* TODO: annoyingly, this is required for cons_complexity to find the typeclass instance *)
(*   Global Instance CT_cons {A CA : Type}: CT (A -> list A -> list A)
                        (ℂI A -> ℂO (ℂI (list A) -> ℂO (list CA))).
  Proof. typeclasses eauto. Defined. *)

  Parameter cons_complexity: forall {A : Type},
    ComplexityBound (@cons A)
                    (fun (h : ℂI A unit) => 1 ⋉ ( (* we may not need so many 1s *)
                     fun (t : ℂI (list A) unit) => 1 ⋉ tt)).
  Global Existing Instance cons_complexity.

  Parameter list_match_complexity:
    forall {A : Type} {B CB} (v : B) (f : A -> list A -> B)
    (cv : CB) (cf : ℂI A unit -> ℂO(ℂI (list A) unit -> ℂO CB)),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun l => match l with
                | nil => v
                | h :: t => f h t
                end)
      (fun (lc : ℂI (list A) unit) => 1 ⊕ (* 1 for the match *)
                match ival lc with
                | h :: t =>
                    (t ⋊ tt) I>>=O ((h ⋊ tt) I>>=I (f ⋊ cf)) >>|
                | nil => ret cv
                end).
  Global Existing Instance list_match_complexity.
  (* TODO: Recursion operator *)

End ListTimeCostModel.

(* Example of derived complexity bounds for list operators *)
Module Type ListTimeExamples
  (Import CM : CostModel)
  (Import BTM : BasicTimeCostModel CM)
  (Import LM : ListTimeCostModel CM BTM).


Ltac ctac := typeclasses eauto.

  (** ** List tail *)
  Instance complexity_tl {A} :
    ComplexityBound (@tl A) (fun (lc : ℂI (list A) unit) => 3 ⋉ tt).
  Proof.
    unfold tl.
    capply. ctac. (* uses list_match_complexity, constant_complexity *)
    Unshelve. apply bound_order_ext_eq. intros [l lc].
    unfold ObindO, IbindI. simpl.
    case l as [|h t].
    + (* TODO: automation *)
      apply bound_order_output; split; simpl.
      * lia.
      * reflexivity.
    + apply bound_order_output; split; simpl.
      * trivial.
      * reflexivity.
Qed.

  (** ** List tail *)
  (* TODO: *)

End ListTimeExamples.


