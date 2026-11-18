(** * Cost model for lists

    Lists of any data: the elements of a list may be functions, or other
    data with complexities. As for the other datatypes ([TimeDatatypes]),
    the model has three layers: the data, the constructors and the case
    analysis, compiled to the case combinator [list_case]. *)

From Complexity Require Export TimeCombinators.
From Stdlib Require Import List.
Local Open Scope nat_scope.

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

    The value gives the shape: a list whose complexity is shorter has the
    default complexity for the missing elements ([cdefault]; in L, the
    instance, a list is realised by the realisers of its elements, with
    these complexities). The order on the complexities of lists compares
    them index by index, the missing ones being the default one. A list of
    ground data is therefore ground ([ListGround]): its complexities carry
    no information. *)

Module Type ListData (Import CM : CostModel).
  #[global] Declare Instance Repr_list : forall {A CA}, Repr A CA -> Repr (list A) (list CA).

  #[global] Declare Instance Size_list : forall {A}, Size A -> Size (list A).
  Parameter size_nil : forall {A} `{Size A}, size (@nil A) = 1.
  Parameter size_cons : forall {A} `{Size A} (a : A) l, size (a :: l) = 1 + size a + size l.

  (** The order on the complexities of lists: index by index, the missing
      ones being the default one. *)
  Parameter bound_order_list : forall {A CA} `{Repr A CA} (c c' : list CA),
    (forall i, bound_order (nth i c cdefault) (nth i c' cdefault)) -> bound_order c c'.

  #[global] Declare Instance nil_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nil A) (@nil CA).
End ListData.

(** Lists of ground data are ground: their complexities are related index
    by index. *)
Module ListGround (Import CM : CostModel) (Import LD : ListData CM).
  Global Instance list_ground {A CA} {R : Repr A CA} {G : IsGround R} : IsGround (Repr_list R) :=
    {| ground_indiscrete := fun c c' => bound_order_list c c' (fun i => ground_order _ _) |}.
End ListGround.

Module Type ListCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import LD : ListData CM).

  Parameter c_cons : nat.
  #[global] Hint Unfold c_cons : costs.

  #[global] Declare Instance cons_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@cons A) (fun ch => c_clo +> fun ct => c_cons +> (pot ch :: pot ct)).
End ListCtorTimeCostModel.

Module Type ListCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import LD : ListData CM).

  Parameter c_case_list : nat.
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
       fun ce : ℂI E CE => c_case_list ⊕ c_frame ⊕ cost (pot cl ce) ⊕
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
