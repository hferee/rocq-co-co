From Complexity Require Import CostModel HOCostModel Combinators Compile
  CombinatorCostModel UnitCostModel.
From Stdlib Require Import Program.Basics Lia List.

(** ** Case combinator (see [Combinators]) *)

Definition list_case {X A : Type} (z : unit -> A) (c : X -> list X -> A) (l : list X) : A :=
  match l with nil => z tt | cons h t => c h t end.

#[global] Typeclasses Opaque list_case.
#[global] Hint Unfold list_case : comb.

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


  (** Case analysis, as a higher-order constant: matches on any expression,
      with branches using other variables, are compiled to it ([Compile]). *)
  Parameter list_case_complexity : forall {X A CA},
    ComplexityBound (@list_case X A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cc : ℂI (X -> list X -> A) (ℂI X unit -> ℂO (ℂI (list X) unit -> ℂO CA)) => 0 ⋉
       fun cl : ℂI (list X) unit => 1 ⊕
         match ival cl with
         | nil => icomp cz (tt ⋊ tt)
         | cons h t => ((t ⋊ tt) I>>=O ((h ⋊ tt) I>>=I cc)) >>|
         end).
  Global Existing Instance list_case_complexity.

End ListTimeCostModel.

(* Example of derived complexity bounds for list operators *)
Module Type ListTimeExamples
  (Import CM : CostModel)
  (Import BTM : BasicTimeCostModel CM)
  (Import LM : ListTimeCostModel CM BTM)
  (Import CB : CombinatorTimeCostModel CM BTM) (Import UN : UnitTimeCostModel CM).

  (** ** List tail *)
  Instance complexity_tl {A} :
    ComplexityBound (@tl A) (fun (lc : ℂI (list A) unit) => 1 ⋉ tt).
  Proof.
    capply. unfold tl. cbc.
    Unshelve. bo_split; destr_inputs; destruct lc; cbn; lia.
  Qed.

End ListTimeExamples.
