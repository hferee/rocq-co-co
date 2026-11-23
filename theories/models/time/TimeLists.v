(** * Cost model for lists

    Lists of any data: the elements of a list may be functions, or other
    data with complexities. As for the other datatypes ([TimeDatatypes]),
    the model has three layers: the data, the constructors and the case
    analysis, compiled to the case combinator [list_case]. *)

From Complexity Require Export TimeCombinators.
From Stdlib Require Import List.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Local Open Scope nat_scope.

(** The sums of lists as the computation leaves them ([list_sum (x :: l)]
    into [x + fold_right Nat.add 0 l]), folded back for [lia]
    ([cnorm_types]). *)
Ltac2 Set cnorm_hook as previous := fun () =>
  previous ();
  ltac1:(repeat match goal with
         | |- context [fold_right Nat.add 0 ?l] => change (fold_right Nat.add 0 l) with (list_sum l)
         | H : context [fold_right Nat.add 0 ?l] |- _ => change (fold_right Nat.add 0 l) with (list_sum l) in H
         end).

(** Case combinator (see [Combinators]). *)

Definition list_case {X E A : Type} (z : E -> A) (c : env (env E X) (list X) -> A)
  (l : E -> list X) (e : E) : A :=
  match l e with nil => z e | cons h t => c (ECons (ECons e h) t) end.

#[global] Typeclasses Opaque list_case.
#[global] Hint Unfold list_case : comb.

(** The empty list, the complexity of a ground result ([>|]). *)
#[global] Instance list_inhabited {C} : Inhabited (list C) := populate nil.

(** ** Lists

    A list of [A], with complexities [CA], has the list of the complexities
    of its elements, in [list CA], as its complexity. [cons] adds the
    complexity of the head, and the case analysis gives the head and the
    tail their complexities, so that the costs of a function of a list are
    functions of the complexities of its elements: the costs of their
    applications for a list of functions ([HOListComplexity]).

    A well-formed complexity of a list has one well-formed complexity for
    each element ([wf_list]; in L, the instance, a list is realised by the
    realisers of its elements, with these complexities). Since the
    complexities of functions are compared at the well-formed inputs
    ([bound_order_arr]), the bounds of the functions of lists may ignore
    the others, for instance [tl (pot cl)] for [tl]. The case analysis
    gives the default complexity to a missing head ([cdefault]), which only
    happens at the inputs that are not well-formed. *)

(** The order on the complexities of lists ([Forall2]). *)
Section ListOrder.
  Context {C : Type} (R : C -> C -> Prop).

  Lemma Forall2_refl_ : Reflexive R -> forall c, Forall2 R c c.
  Proof. intros HR c. induction c as [| x c IH]; constructor; [exact (HR x) | exact IH]. Qed.

  Lemma Forall2_trans_ : Transitive R ->
    forall c1 c2 c3, Forall2 R c1 c2 -> Forall2 R c2 c3 -> Forall2 R c1 c3.
  Proof.
    intros HT c1 c2 c3 H12. revert c3.
    induction H12 as [| x y c1 c2 Hxy H12 IH]; intros c3 H23; inversion H23; subst; constructor.
    - exact (HT _ _ _ Hxy H1).
    - exact (IH _ H3).
  Qed.
End ListOrder.

Module Type ListData (Import CM : CostModel).
  Local Abbreviation ℂO := (ℂO' Cost).
  #[global] Declare Instance Repr_list : forall {A CA}, Repr A CA -> Repr (list A) (list CA).

  #[global] Declare Instance Size_list : forall {A}, Size A -> Size (list A).
  Parameter size_nil : forall {A} `{Size A}, size (@nil A) = 1.
  Parameter size_cons : forall {A} `{Size A} (a : A) l, size (a :: l) = 1 + size a + size l.

  (** A complexity of a list is well-formed when it has one well-formed
      complexity for each element. *)
  Parameter wf_list : forall {A CA} `{Repr A CA} (l : list A) (c : list CA),
    wf l c <-> Forall2 wf l c.

  (** The order on the complexities of lists: element by element. *)
  Parameter bound_order_list : forall {A CA} `{Repr A CA} (c c' : list CA),
    Forall2 (@bound_order A CA _) c c' -> bound_order c c'.

  #[global] Declare Instance nil_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nil A) (@nil CA).
End ListData.

(** The well-formed complexities of the empty and non-empty lists. *)
Module ListWf (Import CM : CostModel) (Import LD : ListData CM).
  Local Abbreviation ℂO := (ℂO' Cost).
  Lemma wf_nil {A CA} `{Repr A CA} (c : list CA) : wf (@nil A) c -> c = nil.
  Proof. intro Hw. apply wf_list in Hw. inversion Hw. reflexivity. Qed.

  Lemma wf_cons {A CA} `{Repr A CA} (x : A) (l : list A) (c : list CA) :
    wf (x :: l) c -> exists h t, c = h :: t /\ wf x h /\ wf l t.
  Proof.
    intro Hw. apply wf_list in Hw. inversion Hw; subst. exists y, l'.
    split; [reflexivity | split; [assumption | apply wf_list; assumption]].
  Qed.

  Lemma wf_length {A CA} `{Repr A CA} (l : list A) (c : list CA) : wf l c -> length c = length l.
  Proof. intro Hw. apply wf_list in Hw. symmetry. exact (Forall2_length Hw). Qed.
End ListWf.

(* Broken by the order on the complexities of lists ([Forall2]):
   [[tt] ≤ []] is not derivable, so lists of ground data are not ground.
(** Lists of ground data are ground: their complexities are related index
    by index. *)
Module ListGround (Import CM : CostModel) (Import LD : ListData CM).
  Local Abbreviation ℂO := (ℂO' Cost).
  Global Instance list_ground {A CA} {R : Repr A CA} {G : IsGround R} : IsGround (Repr_list R) :=
    {| ground_indiscrete := fun c c' => bound_order_list c c' (fun i => ground_order _ _) |}.
End ListGround.
*)

Module Type ListCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import LD : ListData CM).
  Local Abbreviation ℂO := (ℂO' Cost).

  Parameter c_cons : Cost.
  #[global] Hint Unfold c_cons : costs.

  #[global] Declare Instance cons_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@cons A) (fun ch => c_clo +> fun ct => c_cons +> (pot ch :: pot ct)).
End ListCtorTimeCostModel.

Module Type ListCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import LD : ListData CM).
  Local Abbreviation ℂO := (ℂO' Cost).

  Parameter c_case_list : Cost.
  #[global] Hint Unfold c_case_list : costs.

  (** The branch of [cons] receives the head and the tail with their
      complexities (the default one for a missing head). *)
  #[global] Declare Instance list_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * CX) * list CX) -> ℂO CA) => c_clo +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO (list CX)) => c_clo +>
       fun ce : ℂI E CE => c_case_list ⊕ caround c_frame (cost (pot cl ce)) ⊕
         match val cl (val ce) with
         | cons h t =>
             pot cc (ECons (ECons (val ce) h) t
                       ⋊ ((pot ce, hd cdefault (res (pot cl ce))), tl (res (pot cl ce))))
         | nil => pot cz ce
         end).
End ListCaseTimeCostModel.

Module Type ListTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  ListData CM <+ ListCtorTimeCostModel CM BT <+ ListCaseTimeCostModel CM BT CB.
