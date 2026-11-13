(** * Cost models for the basic datatypes

    Booleans, natural numbers, options (of ground data, and of any data) and
    pairs of ground data, and binary numbers (lists are in [TimeLists]). Values are ground data, with sizes ([Size]); constructors
    and case analyses are primitive. Each case analysis is compiled to a case
    combinator ([Combinators]), defined here with its datatype. Recursion is
    covered by [TimeFix]: the functions of the standard library are analysed
    as they are defined ([stdlib]).

    The case combinators work on environments, as the code of closures
    ([Combinators]): their branches and the matched value are code, functions
    of the environment [e] of the match, and the branch of a constructor with
    arguments runs in [e] extended with them. The code of a match is thus
    closed, built once; its evaluation builds no closure: it pays the case
    analysis, the matched value and the selected branch.

    Each datatype has up to three layers, so that a cost model can choose its
    primitives: the data ([NatData]: representation, sizes and values, with
    no cost), the constructors ([NatCtorTimeCostModel]) and the case analysis
    ([NatCaseTimeCostModel]). A model without the case layer of [nat] has no
    known cost for matches on [nat]: [cbc] fails on them. The constructor and
    case layers declare their constants (the cost of a partial application
    is [c_clo], from [BasicTimeCostModel]). [NatTimeCostModel] gathers the
    three layers. *)

From Complexity Require Export TimeCombinators.
From Stdlib Require Import List PArith NArith ZArith QArith.
Local Open Scope nat_scope.


(** ** Booleans *)

(** Case combinator (see [Combinators]). *)

Definition bool_case {E A : Type} (t f : E -> A) (b : E -> bool) (e : E) : A :=
  match b e with true => t e | false => f e end.

#[global] Typeclasses Opaque bool_case.
#[global] Hint Unfold bool_case : comb.

(** Booleans are ground data. *)
Module Type BoolData (Import CM : CostModel).
  #[global] Declare Instance Repr_bool : Ground bool.

  #[global] Declare Instance Size_bool : Size bool.
  Parameter size_bool : forall b : bool, 0 < size b.

  #[global] Declare Instance bool_complexity : forall b : bool, ComplexityBound b tt.
End BoolData.

Module Type BoolCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import BD : BoolData CM).

  Parameter c_case_bool : nat.
  #[global] Hint Unfold c_case_bool : costs.

  (** Case analysis, in an environment: only the selected branch is
      evaluated. [if] and every match on a boolean are compiled to it. *)
  #[global] Declare Instance bool_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@bool_case E A)
      (fun ct : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cf : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cb : ℂI (E -> bool) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_bool ⊕ c_frame ⊕ cost (pot cb ce) ⊕
         if val cb (val ce) then pot ct ce else pot cf ce).
End BoolCaseTimeCostModel.

Module Type BoolTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  BoolData CM <+ BoolCaseTimeCostModel CM BT CB.

(** ** Natural numbers *)

(** Case combinator (see [Combinators]). *)

Definition nat_case {E A : Type} (z : E -> A) (s : env E nat -> A) (n : E -> nat) (e : E) : A :=
  match n e with O => z e | S k => s (ECons e k) end.

#[global] Typeclasses Opaque nat_case.
#[global] Hint Unfold nat_case : comb.

Definition ℂI_nat_inj (n : nat) := n ⋊ tt.
Coercion ℂI_nat_inj : nat >-> ℂI.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)

(** Natural numbers are ground data. *)
Module Type NatData (Import CM : CostModel).
  #[global] Declare Instance Repr_nat : Ground nat.

  #[global] Declare Instance Size_nat : Size nat.
  Parameter size_O : 0 < size 0.
  Parameter size_S : forall n, size n < size (S n).

  #[global] Declare Instance nat_complexity : forall n : nat, ComplexityBound n tt.
End NatData.

Module Type NatCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import ND : NatData CM).

  Parameter c_S : nat.
  #[global] Hint Unfold c_S : costs.

  Parameter S_complexity : ComplexityBound S (fun x => c_S >|).
  Existing Instance S_complexity.
End NatCtorTimeCostModel.

Module Type NatCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import ND : NatData CM).

  Parameter c_case_nat : nat.
  #[global] Hint Unfold c_case_nat : costs.

  (** [nat_case] is a higher-order constant: matches on any expression, with
      branches using other variables, are compiled to it ([Compile]).
      Recursion is covered by the generic fixpoint axiom of [TimeFix]. *)
  #[global] Declare Instance nat_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@nat_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cs : ℂI (env E nat -> A) (ℂI (env E nat) (CE * unit) -> ℂO CA) => c_clo +>
       fun cn : ℂI (E -> nat) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_nat ⊕ c_frame ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | O => pot cz ce
         | S k => pot cs (ECons (val ce) k ⋊ (pot ce, tt))
         end).
End NatCaseTimeCostModel.

Module Type NatTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  NatData CM <+ NatCtorTimeCostModel CM BT <+ NatCaseTimeCostModel CM BT CB.

(* See NatComplexity.v for examples. *)

(** ** Options (of ground data) *)

(** Case combinator (see [Combinators]). *)

Definition option_case {X E A : Type} (s : env E X -> A) (z : E -> A) (o : E -> option X) (e : E) : A :=
  match o e with Some x => s (ECons e x) | None => z e end.

#[global] Typeclasses Opaque option_case.
#[global] Hint Unfold option_case : comb.

(** Options of ground data are ground data. *)
Module Type OptionData (Import CM : CostModel).
  #[global] Declare Instance Repr_option : forall {A}, Ground A -> Ground (option A).

  #[global] Declare Instance Size_option : forall {A}, Size A -> Size (option A).
  Parameter size_None : forall {A} `{Size A}, 0 < size (@None A).
  Parameter size_Some : forall {A} `{Size A} (a : A), size a < size (Some a).

  (** [None] is a value; the other options are built with [Some]. *)
  #[global] Declare Instance None_complexity : forall {A} `{Ground A}, ComplexityBound (@None A) tt.
End OptionData.

Module Type OptionCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import OD : OptionData CM).

  Parameter c_Some : nat.
  #[global] Hint Unfold c_Some : costs.

  #[global] Declare Instance Some_complexity : forall {A} `{Ground A},
    ComplexityBound (@Some A) (fun _ => c_Some >|).
End OptionCtorTimeCostModel.

Module Type OptionCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import OD : OptionData CM).

  Parameter c_case_option : nat.
  #[global] Hint Unfold c_case_option : costs.

  #[global] Declare Instance option_case_complexity :
    forall {X E CE A CA} `{Ground X} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * unit) -> ℂO CA) => c_clo +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_option ⊕ c_frame ⊕ cost (pot co ce) ⊕
         match val co (val ce) with
         | Some x => pot cs (ECons (val ce) x ⋊ (pot ce, tt))
         | None => pot cz ce
         end).
End OptionCaseTimeCostModel.

Module Type OptionTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  OptionData CM <+ OptionCtorTimeCostModel CM BT <+ OptionCaseTimeCostModel CM BT CB.

(** ** Options of any data

    As for lists of any data ([TimeLists]): the element of an option may be
    a function, or other data with complexities. An option of [A], with
    complexities [CA], has an option of [CA] as its complexity: that of its
    element. [Some] keeps the complexity of its argument, and the case
    analysis gives it to the branch of [Some]. An option and its complexity
    are both [Some] or both [None] (in L, the instance); the case analysis
    treats [Some] without a complexity as [None] (this does not happen).
    The order compares the complexities of the elements ([option_le]). A
    cost model chooses one of the two models of options ([TimeCostModel],
    [HOTimeCostModel]). *)

(** The order on options: both [None], or both [Some] with related elements. *)
Definition option_le {C} (R : C -> C -> Prop) (o o' : option C) : Prop :=
  match o, o' with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.

Module Type HOptionData (Import CM : CostModel).
  #[global] Declare Instance Repr_option : forall {A CA}, Repr A CA -> Repr (option A) (option CA).

  #[global] Declare Instance Size_option : forall {A}, Size A -> Size (option A).
  Parameter size_None : forall {A} `{Size A}, 0 < size (@None A).
  Parameter size_Some : forall {A} `{Size A} (a : A), size a < size (Some a).

  Parameter bound_order_option : forall {A CA} `{Repr A CA} (c c' : option CA),
    option_le bound_order c c' -> bound_order c c'.

  #[global] Declare Instance None_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@None A) (@None CA).
End HOptionData.

Module Type HOptionCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import OD : HOptionData CM).

  Parameter c_Some : nat.
  #[global] Hint Unfold c_Some : costs.

  #[global] Declare Instance Some_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Some A) (fun ca => c_Some +> Some (pot ca)).
End HOptionCtorTimeCostModel.

Module Type HOptionCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import OD : HOptionData CM).

  Parameter c_case_option : nat.
  #[global] Hint Unfold c_case_option : costs.

  (** The branch of [Some] receives the element with its complexity. *)
  #[global] Declare Instance option_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => c_clo +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO (option CX)) => c_clo +>
       fun ce : ℂI E CE => c_case_option ⊕ c_frame ⊕ cost (pot co ce) ⊕
         match val co (val ce), res (pot co ce) with
         | Some x, Some cx => pot cs (ECons (val ce) x ⋊ (pot ce, cx))
         | _, _ => pot cz ce
         end).
End HOptionCaseTimeCostModel.

Module Type HOptionTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  HOptionData CM <+ HOptionCtorTimeCostModel CM BT <+ HOptionCaseTimeCostModel CM BT CB.

(** ** Pairs (of ground data)

    Pairs were missing from the higher-order models: [let (x, y) := p in e]
    and the projections are compiled to [prod_case]. *)

(** Case combinator (see [Combinators]). *)

Definition prod_case {X Y E A : Type} (f : env (env E X) Y -> A) (p : E -> X * Y) (e : E) : A :=
  match p e with pair x y => f (ECons (ECons e x) y) end.

#[global] Typeclasses Opaque prod_case.
#[global] Hint Unfold prod_case : comb.

Module Type ProdData (Import CM : CostModel).
  #[global] Declare Instance Repr_prod : forall {A B}, Ground A -> Ground B -> Ground (A * B).

  #[global] Declare Instance Size_prod : forall {A B}, Size A -> Size B -> Size (A * B).
  Parameter size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    size a + size b < size (a, b).
End ProdData.

(* Pairs are built with [pair]. *)
Module Type ProdCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import PD : ProdData CM).

  Parameter c_pair : nat.
  #[global] Hint Unfold c_pair : costs.

  #[global] Declare Instance pair_complexity : forall {A B} `{Ground A} `{Ground B},
    ComplexityBound (@pair A B) (fun _ => c_clo +> fun _ => c_pair >|).
End ProdCtorTimeCostModel.

Module Type ProdCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import PD : ProdData CM).

  Parameter c_case_prod : nat.
  #[global] Hint Unfold c_case_prod : costs.

  #[global] Declare Instance prod_case_complexity :
    forall {X Y E CE A CA} `{Ground X} `{Ground Y} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@prod_case X Y E A)
      (fun cf : ℂI (env (env E X) Y -> A) (ℂI (env (env E X) Y) ((CE * unit) * unit) -> ℂO CA) =>
         c_clo +>
       fun cp : ℂI (E -> X * Y) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_prod ⊕ c_frame ⊕ cost (pot cp ce) ⊕
         let (x, y) := val cp (val ce) in
         pot cf (ECons (ECons (val ce) x) y ⋊ ((pot ce, tt), tt))).
End ProdCaseTimeCostModel.

Module Type ProdTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  ProdData CM <+ ProdCtorTimeCostModel CM BT <+ ProdCaseTimeCostModel CM BT CB.

(** ** Binary numbers: [positive], [N], [Z], and [Q] *)

(** Case combinators (see [Combinators]). *)

Definition positive_case {E A : Type} (fI fO : env E positive -> A) (fH : E -> A)
  (p : E -> positive) (e : E) : A :=
  match p e with xI q => fI (ECons e q) | xO q => fO (ECons e q) | xH => fH e end.
Definition N_case {E A : Type} (z : E -> A) (f : env E positive -> A) (n : E -> N) (e : E) : A :=
  match n e with N0 => z e | Npos p => f (ECons e p) end.
Definition Z_case {E A : Type} (z : E -> A) (fp fn : env E positive -> A) (x : E -> Z) (e : E) : A :=
  match x e with Z0 => z e | Zpos p => fp (ECons e p) | Zneg p => fn (ECons e p) end.
Definition comparison_case {E A : Type} (eq lt gt : E -> A) (c : E -> comparison) (e : E) : A :=
  match c e with Eq => eq e | Lt => lt e | Gt => gt e end.
Definition Q_case {E A : Type} (f : env (env E Z) positive -> A) (q : E -> Q) (e : E) : A :=
  match q e with Qmake n d => f (ECons (ECons e n) d) end.

#[global] Typeclasses Opaque positive_case N_case Z_case comparison_case Q_case.
#[global] Hint Unfold positive_case N_case Z_case comparison_case Q_case : comb.

(** ** Values, constructors, case analysis *)

Module Type ZData (Import CM : CostModel).
  #[global] Declare Instance Repr_positive : Ground positive.
  #[global] Declare Instance Repr_N : Ground N.
  #[global] Declare Instance Repr_Z : Ground Z.
  #[global] Declare Instance Repr_Q : Ground Q.
  #[global] Declare Instance Repr_comparison : Ground comparison.

  #[global] Declare Instance Size_positive : Size positive.
  #[global] Declare Instance Size_N : Size N.
  #[global] Declare Instance Size_Z : Size Z.
  #[global] Declare Instance Size_Q : Size Q.
  #[global] Declare Instance Size_comparison : Size comparison.
  Parameter size_xH : (0 < size xH)%nat.
  Parameter size_xO : (forall p, size p < size (xO p))%nat.
  Parameter size_xI : (forall p, size p < size (xI p))%nat.
  Parameter size_N0 : (0 < size N0)%nat.
  Parameter size_Npos : (forall p, size p < size (Npos p))%nat.
  Parameter size_Z0 : (0 < size Z0)%nat.
  Parameter size_Zpos : (forall p, size p < size (Zpos p))%nat.
  Parameter size_Zneg : (forall p, size p < size (Zneg p))%nat.
  Parameter size_Qmake : (forall n d, size n + size d < size (Qmake n d))%nat.
  Parameter size_comparison : (forall c : comparison, 0 < size c)%nat.

  #[global] Declare Instance positive_complexity : forall p : positive, ComplexityBound p tt.
  #[global] Declare Instance N_complexity : forall n : N, ComplexityBound n tt.
  #[global] Declare Instance Z_complexity : forall z : Z, ComplexityBound z tt.
  #[global] Declare Instance Q_complexity : forall q : Q, ComplexityBound q tt.
  #[global] Declare Instance comparison_complexity : forall c : comparison, ComplexityBound c tt.
End ZData.

(** One constant for the constructors of all the binary numbers, one for
    their case analyses. *)
Module Type ZCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import ZD : ZData CM).

  Parameter c_ctor_Z : nat.
  #[global] Hint Unfold c_ctor_Z : costs.

  #[global] Declare Instance xI_complexity : ComplexityBound xI (fun _ => c_ctor_Z >|).
  #[global] Declare Instance xO_complexity : ComplexityBound xO (fun _ => c_ctor_Z >|).
  #[global] Declare Instance Npos_complexity : ComplexityBound Npos (fun _ => c_ctor_Z >|).
  #[global] Declare Instance Zpos_complexity : ComplexityBound Zpos (fun _ => c_ctor_Z >|).
  #[global] Declare Instance Zneg_complexity : ComplexityBound Zneg (fun _ => c_ctor_Z >|).
  #[global] Declare Instance Qmake_complexity :
    ComplexityBound Qmake (fun _ => c_clo +> fun _ => c_ctor_Z >|).
End ZCtorTimeCostModel.

Module Type ZCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import ZD : ZData CM).

  Parameter c_case_Z : nat.
  #[global] Hint Unfold c_case_Z : costs.

  #[global] Declare Instance positive_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@positive_case E A)
      (fun cI : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => c_clo +>
       fun cO : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => c_clo +>
       fun cH : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cp : ℂI (E -> positive) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_Z ⊕ c_frame ⊕ cost (pot cp ce) ⊕
         match val cp (val ce) with
         | xI q => pot cI (ECons (val ce) q ⋊ (pot ce, tt))
         | xO q => pot cO (ECons (val ce) q ⋊ (pot ce, tt))
         | xH => pot cH ce
         end).

  #[global] Declare Instance N_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@N_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => c_clo +>
       fun cn : ℂI (E -> N) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_Z ⊕ c_frame ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | N0 => pot cz ce
         | Npos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         end).

  #[global] Declare Instance Z_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Z_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => c_clo +>
       fun cn : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => c_clo +>
       fun cx : ℂI (E -> Z) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_Z ⊕ c_frame ⊕ cost (pot cx ce) ⊕
         match val cx (val ce) with
         | Z0 => pot cz ce
         | Zpos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         | Zneg p => pot cn (ECons (val ce) p ⋊ (pot ce, tt))
         end).

  #[global] Declare Instance comparison_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@comparison_case E A)
      (fun cq : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cl : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cg : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun cc : ℂI (E -> comparison) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_Z ⊕ c_frame ⊕ cost (pot cc ce) ⊕
         match val cc (val ce) with
         | Eq => pot cq ce
         | Lt => pot cl ce
         | Gt => pot cg ce
         end).

  #[global] Declare Instance Q_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Q_case E A)
      (fun cf : ℂI (env (env E Z) positive -> A)
                   (ℂI (env (env E Z) positive) ((CE * unit) * unit) -> ℂO CA) => c_clo +>
       fun cq : ℂI (E -> Q) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_Z ⊕ c_frame ⊕ cost (pot cq ce) ⊕
         match val cq (val ce) with
         | Qmake n d => pot cf (ECons (ECons (val ce) n) d ⋊ ((pot ce, tt), tt))
         end).
End ZCaseTimeCostModel.

Module Type ZTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  ZData CM <+ ZCtorTimeCostModel CM BT <+ ZCaseTimeCostModel CM BT CB.
