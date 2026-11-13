(** * Cost models for lists

    Two models: lists of ground data ([ListTimeCostModel]), themselves
    ground data, and lists of any data ([HListTimeCostModel]), whose
    complexity is the list of the complexities of their elements. A cost
    model chooses one of them ([TimeCostModel] and [HOTimeCostModel]). As
    for the other datatypes ([TimeDatatypes]), each one has three layers:
    the data, the constructors and the case analysis, compiled to the case
    combinator [list_case], common to both models. *)

From Complexity Require Export TimeCombinators.
From Stdlib Require Import List.
Local Open Scope nat_scope.

(** Case combinator (see [Combinators]), for both models. *)

Definition list_case {X E A : Type} (z : E -> A) (c : env (env E X) (list X) -> A)
  (l : E -> list X) (e : E) : A :=
  match l e with nil => z e | cons h t => c (ECons (ECons e h) t) end.

#[global] Typeclasses Opaque list_case.
#[global] Hint Unfold list_case : comb.

(** ** Lists of ground data

    A list of ground data is ground data: its complexity is [tt]. *)
Module Type ListData (Import CM : CostModel).
  #[global] Declare Instance Repr_list : forall {A}, Ground A -> Ground (list A).

  #[global] Declare Instance Size_list : forall {A}, Size A -> Size (list A).
  Parameter size_nil : forall {A} `{Size A}, 0 < size (@nil A).
  Parameter size_cons : forall {A} `{Size A} (a : A) l, size a + size l < size (a :: l).

  (** The empty list is a value; the other lists are built with [cons]. *)
  #[global] Declare Instance nil_complexity : forall {A} `{Ground A}, ComplexityBound (@nil A) tt.
End ListData.

Module Type ListCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import LD : ListData CM).

  Parameter c_cons : nat.
  #[global] Hint Unfold c_cons : costs.

  #[global] Declare Instance cons_complexity: forall {A : Type} `{Ground A},
    ComplexityBound (@cons A)
                    (fun h => c_clo +> (
                     fun t => c_cons >|)).
End ListCtorTimeCostModel.

Module Type ListCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import LD : ListData CM).

  Parameter c_case_list : nat.
  #[global] Hint Unfold c_case_list : costs.

  (** Case analysis, as a higher-order constant: matches on any expression,
      with branches using other variables, are compiled to it ([Compile]). *)
  #[global] Declare Instance list_case_complexity :
    forall {X E CE A CA} `{Ground X} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * unit) * unit) -> ℂO CA) => c_clo +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_list ⊕ c_frame ⊕ cost (pot cl ce) ⊕
         match val cl (val ce) with
         | nil => pot cz ce
         | cons h t => pot cc (ECons (ECons (val ce) h) t ⋊ ((pot ce, tt), tt))
         end).
End ListCaseTimeCostModel.

Module Type ListTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  ListData CM <+ ListCtorTimeCostModel CM BT <+ ListCaseTimeCostModel CM BT CB.

(** ** Lists of any data

    The elements of a list may be functions, or other data with
    complexities: a list of [A], with complexities [CA], has the list of
    the complexities of its elements, in [list CA], as its complexity.
    [cons] adds the complexity of the head, and the case analysis gives the
    head and the tail their complexities, so that the costs of a function
    of a list are functions of the complexities of its elements: the costs
    of their applications for a list of functions ([HOListComplexity]).

    A list and its complexity have the same length (in L, the instance, a
    list is realised by the realisers of its elements, with their
    complexities). The case analysis treats a list whose complexity is
    shorter as its prefix (the other cases do not happen): the costs of the
    functions of lists follow it ([HOListComplexity]). The order on the
    complexities of lists compares them element by element. *)

Module Type HListData (Import CM : CostModel).
  #[global] Declare Instance Repr_list : forall {A CA}, Repr A CA -> Repr (list A) (list CA).

  #[global] Declare Instance Size_list : forall {A}, Size A -> Size (list A).
  Parameter size_nil : forall {A} `{Size A}, 0 < size (@nil A).
  Parameter size_cons : forall {A} `{Size A} (a : A) l, size a + size l < size (a :: l).

  (** The order on the complexities of lists: element by element. *)
  Parameter bound_order_list : forall {A CA} `{Repr A CA} (c c' : list CA),
    Forall2 bound_order c c' -> bound_order c c'.

  #[global] Declare Instance nil_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nil A) (@nil CA).
End HListData.

Module Type HListCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import LD : HListData CM).

  Parameter c_cons : nat.
  #[global] Hint Unfold c_cons : costs.

  #[global] Declare Instance cons_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@cons A) (fun ch => c_clo +> fun ct => c_cons +> (pot ch :: pot ct)).
End HListCtorTimeCostModel.

Module Type HListCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import LD : HListData CM).

  Parameter c_case_list : nat.
  #[global] Hint Unfold c_case_list : costs.

  (** The branch of [cons] receives the head and the tail with their
      complexities. *)
  #[global] Declare Instance list_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * CX) * list CX) -> ℂO CA) => c_clo +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO (list CX)) => c_clo +>
       fun ce : ℂI E CE => c_case_list ⊕ c_frame ⊕ cost (pot cl ce) ⊕
         match val cl (val ce), res (pot cl ce) with
         | cons h t, cons ch ct => pot cc (ECons (ECons (val ce) h) t ⋊ ((pot ce, ch), ct))
         | _, _ => pot cz ce
         end).
End HListCaseTimeCostModel.

Module Type HListTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  HListData CM <+ HListCtorTimeCostModel CM BT <+ HListCaseTimeCostModel CM BT CB.
