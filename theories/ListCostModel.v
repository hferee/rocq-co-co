From Complexity Require Import SimpleCostModel.
From Stdlib Require Import Program.Basics Lia List.

Module Type ListTimeCostModel
  (Import CM : CostModel) (Import BTM : BasicTimeCostModel CM).

  (* The cost of a list is the list of costs.
    Other possible cost models: the maxiumum cost or the sum of the costs. *)
  Parameter CT_list: forall {A CA : Type} `{CT A CA}, CT (list A) (list CA).
  Global Existing Instance CT_list.

  (* The complexity of a list is exactly the complexity of its elements *)
  Parameter ComplexityBound_list : forall {A CA} `{CT A CA} (l : list A) lc,
    ComplexityBound l lc <-> Forall2 ComplexityBound l lc.

  Lemma ComplexityBound_list_length: forall {A CA} `{CT A CA} (l : list A) lc,
    ComplexityBound l lc -> length l = length lc.
  Proof. now intros * HC%ComplexityBound_list%Forall2_length. Defined.

(*   (* Scott encoding for lists. Useful? *)
  Fixpoint enc {A : Type} (l : list A) 
  : forall {C}, C -> (A -> C -> C) -> C
  := fun {C} n c =>
  match l with
  | nil => n
  | h :: t => c h (enc t n c)
  end.
 *)

  (* List constructors *)
  Parameter nil_complexity: forall {A CA : Type} `{CT A CA},
    ComplexityBound (@nil A) (@nil CA).
  Global Existing Instance nil_complexity.

  (* TODO: annoyingly, this is required for cons_complexity to find the typeclass instance *)
  Global Instance CT_cons {A CA : Type} `{CT A CA}: CT (A -> list A -> list A)
                        (ℂI A -> ℂO (ℂI (list A) -> ℂO (list CA))).
  Proof. typeclasses eauto. Defined.

  Parameter cons_complexity: forall {A CA : Type} `{CT A CA},
    ComplexityBound (@cons A)
                    (fun (h : ℂI A) => 1 ⋉ (fun (t : ℂI (list A)) => 1 ⋉ (icomp h :: icomp t))).
  Global Existing Instance cons_complexity.

  (* TODO: utility. Why Forall2 has'nt got an induction principle in Type? *)
  Lemma Forall2_rect
     : forall (A B : Type) (R : A -> B -> Prop) (P : list A -> list B -> Type),
       P nil nil ->
       (forall (x : A) (y : B) (l : list A) (l' : list B),
        R x y -> Forall2 R l l' -> P l l' -> P (x :: l) (y :: l')) ->
       forall (l : list A) (l0 : list B), Forall2 R l l0 -> P l l0.
  Proof.
  intros A B R P P0 Pind l. induction l as [|h t]; 
  intros [|h0 t0] H0.
  - exact P0.
  - exfalso. inversion H0.
  - exfalso. inversion H0.
  - apply Pind.
    + inversion H0; assumption.
    + inversion H0; assumption.
    + apply IHt. inversion H0; assumption.
  Defined.

  (** From list with its complexity bound, get a list of complexity bounds for its
    elements *)
  Definition ComplexityBound_hd {A CA : Type} `{CT A CA} {h : A} {t : list A} {hc tc}:
    ComplexityBound (h :: t) (hc :: tc) -> ComplexityBound h hc.
  Proof. intros HC%ComplexityBound_list%Forall2_cons_iff. apply HC. Defined.

  Definition ComplexityBound_tl {A CA : Type} `{CT A CA} {h : A} {t : list A} {hc tc}:
    ComplexityBound (h :: t) (hc :: tc) -> ComplexityBound t tc.
  Proof. intros HC%ComplexityBound_list%Forall2_cons_iff.
    apply ComplexityBound_list, HC. Defined.

  Definition list_of_ℂI {A CA : Type} `{CT A CA} (cl : ℂI (list A)) : list (ℂI A).
  Proof.
  case cl. intros l.
  induction l as [|h t]; intros [|hc tc] Hc.
  - exact nil.
  - exact nil.
  - exact nil.
  - exact (ℂI_inj (ComplexityBound_hd Hc) :: IHt _ (ComplexityBound_tl Hc)).
  Defined.

  Lemma list_of_ℂI_cons {A CA : Type} `{CT A CA} (cl : ℂI (list A))
    h t hc tc iproof0:
    list_of_ℂI {| ival := h :: t; icomp := hc :: tc; iproof := iproof0 |}
    = Build_ℂI _ _ _ h hc (ComplexityBound_hd iproof0) ::
      list_of_ℂI (Build_ℂI _ _ _ t tc (ComplexityBound_tl iproof0)).
  Proof. cbv. repeat f_equal. Qed.



  Definition ℂI_of_list {A CA : Type} `{CT A CA} (cl : list (ℂI A)) : ℂI (list A).
  Proof.
  unshelve econstructor.
  - exact (map ival cl).
  - exact (map icomp cl).
  - apply ComplexityBound_list.
    induction cl as [|ch ct IHct]; constructor.
    + now destruct ch.
    + exact IHct.
  Defined.

  Parameter list_match_complexity:
    forall {A CA : Type} `{CT A CA} {B CB} `{CT B CB} (v : B) (f : A -> list A -> B)
    (cv : CB) (cf : ℂI A -> ℂO(ℂI (list A) -> ℂO CB))
    `{!ComplexityBound v cv} `{Hf: !ComplexityBound f cf},
    ComplexityBound 
      (fun l => match l with
                | nil => v
                | h :: t => f h t
                end)
      (fun (lc : ℂI (list A)) => 1 ⊕ (* 1 for the match *)
                match list_of_ℂI lc with
                | hc :: tc => 
                    (ℂI_of_list tc) I>>=O (hc I>>=I (ℂI_inj Hf)) >>|
                    (* TODO: maybe define this 2-ary monadic function application. *)
                | nil => ret cv
                end).
  Global Existing Instance list_match_complexity.
  (* TODO: Recursion operator *)

  (* Inversion lemma for Complexity bounds for lists *)
  Lemma list_Complexity_Bound_inv {A CA : Type} `{CT A CA} {l : list A} {lc}
    (HC : ComplexityBound l lc):
    (l = nil /\ lc = nil (* /\ list_of_ℂI Hc = nil *)) +
    { h & {hc & {t & {tc & l = h :: t /\ lc = hc :: tc}}}}.
  Proof.
  apply ComplexityBound_list_length in HC. destruct l as [|h t]; destruct lc as [|hc tc].
  - now left.
  - inversion HC.
  - inversion HC.
  - right. now exists h, hc, t, tc.
  Qed.

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
  Instance complexity_tl {A CA} `{CT A CA} :
    ComplexityBound (@tl A) (fun (lc : ℂI(list A)) => 3 ⋉ (tl (icomp lc))).
  Proof.
    unfold tl.
    capply.
    refine (list_match_complexity _ _ _ _).
    eapply constant_complexity, id_complexity.
    Unshelve. apply bound_order_ext_eq. intros [l lc].
(*     unfold ObindO, IbindI, IbindO; simpl. *)
    destruct (list_Complexity_Bound_inv iproof0)
      as [(h1 & h2)|(h & hc & t & tc & h1 & h2)]; subst.
    - cbn. admit. (* 1 <= 3. bound_order stuff *)
    - rewrite list_of_ℂI_cons.
      (* TODO  ℂI_of_list is not exactly the inverse of list_of_ℂI *)
    simpl. unfold Forall2_length. simpl icomp.
    cbn.
    (* TODO: bound_order is compatible with products *)
    (* TODO in ℂI A, we need to know that the element has the given complexity.
    In our case, we also need that the complexity of a list is exactly the complexity
    of its elements *)
    case list_of_ℂI.
    - unfold ret. simpl. 
    -
    assert (Hlen := ComplexityBound_list_length l lc iproof0).
    case l as [|h t]; destruct lc as [|hc tc].
    + admit. (* ok with some assumption on bound_order *)
    + inversion Hlen.
    + inversion Hlen.
    +  admit. (* ok with some assumption on bound_order *)
Admitted.

  (** ** List tail *)
  (* TODO: *)

End ListTimeExamples.


