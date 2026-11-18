(** * Cost models for the basic datatypes

    Booleans, natural numbers, options (of ground data, and of any data),
    pairs of ground data, sums of any data, and binary numbers (lists are in
    [TimeLists]). Values are ground data, with sizes ([Size]); constructors
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
  #[global] Declare Instance Repr_bool : Repr bool unit.

  #[global] Declare Instance Size_bool : Size bool.
  Parameter size_bool : forall b : bool, size b = 1.

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
  #[global] Declare Instance Repr_nat : Repr nat unit.

  #[global] Declare Instance Size_nat : Size nat.
  Parameter size_O : size 0 = 1.
  Parameter size_S : forall n, size (S n) = 1 + size n.

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

(** ** Options *)

(** Case combinator (see [Combinators]). *)

Definition option_case {X E A : Type} (s : env E X -> A) (z : E -> A) (o : E -> option X) (e : E) : A :=
  match o e with Some x => s (ECons e x) | None => z e end.

#[global] Typeclasses Opaque option_case.
#[global] Hint Unfold option_case : comb.

(** [None], the complexity of a ground result ([>|]). *)
#[global] Instance option_inhabited {C} : Inhabited (option C) := populate None.

(** The element of an option may be a function, or other data with
    complexities: an option of [A], with complexities [CA], has an option
    of [CA] as its complexity: that of its element. [Some] keeps the
    complexity of its argument, and the case analysis gives it to the
    branch of [Some]. As for lists ([TimeLists]), the value gives the
    shape: [Some] without a complexity has the default one ([cdefault]).
    The order compares the complexities of the elements, the missing one
    being the default one; an option of ground data is ground
    ([OptionGround]). *)

(** The complexity of the element of an option, or a default one. *)
Definition option_dflt {C} (d : C) (o : option C) : C := match o with Some x => x | None => d end.

Module Type OptionData (Import CM : CostModel).
  #[global] Declare Instance Repr_option : forall {A CA}, Repr A CA -> Repr (option A) (option CA).

  #[global] Declare Instance Size_option : forall {A}, Size A -> Size (option A).
  Parameter size_None : forall {A} `{Size A}, size (@None A) = 1.
  Parameter size_Some : forall {A} `{Size A} (a : A), size (Some a) = 1 + size a.

  Parameter bound_order_option : forall {A CA} `{Repr A CA} (c c' : option CA),
    bound_order (option_dflt cdefault c) (option_dflt cdefault c') -> bound_order c c'.

  #[global] Declare Instance None_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@None A) (@None CA).
End OptionData.

(** Options of ground data are ground. *)
Module OptionGround (Import CM : CostModel) (Import OD : OptionData CM).
  Global Instance option_ground {A CA} {R : Repr A CA} {G : IsGround R} :
    IsGround (Repr_option R) :=
    {| ground_indiscrete := fun c c' => bound_order_option c c' (ground_order _ _) |}.
End OptionGround.

Module Type OptionCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import OD : OptionData CM).

  Parameter c_Some : nat.
  #[global] Hint Unfold c_Some : costs.

  #[global] Declare Instance Some_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Some A) (fun ca => c_Some +> Some (pot ca)).
End OptionCtorTimeCostModel.

Module Type OptionCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import OD : OptionData CM).

  Parameter c_case_option : nat.
  #[global] Hint Unfold c_case_option : costs.

  (** The branch of [Some] receives the element with its complexity (the
      default one if it is missing). *)
  #[global] Declare Instance option_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => c_clo +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => c_clo +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO (option CX)) => c_clo +>
       fun ce : ℂI E CE => c_case_option ⊕ c_frame ⊕ cost (pot co ce) ⊕
         match val co (val ce) with
         | Some x => pot cs (ECons (val ce) x ⋊ (pot ce, option_dflt cdefault (res (pot co ce))))
         | None => pot cz ce
         end).
End OptionCaseTimeCostModel.

Module Type OptionTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  OptionData CM <+ OptionCtorTimeCostModel CM BT <+ OptionCaseTimeCostModel CM BT CB.

(** ** Pairs

    [let (x, y) := p in e] and the projections are compiled to
    [prod_case]. *)

(** Case combinator (see [Combinators]). *)

Definition prod_case {X Y E A : Type} (f : env (env E X) Y -> A) (p : E -> X * Y) (e : E) : A :=
  match p e with pair x y => f (ECons (ECons e x) y) end.

#[global] Typeclasses Opaque prod_case.
#[global] Hint Unfold prod_case : comb.

#[global] Instance prod_inhabited {C D} `{Inhabited C} `{Inhabited D} : Inhabited (C * D) :=
  populate (inhabitant, inhabitant).

(** The elements of a pair may be functions, or other data with
    complexities: a pair of [A] and [B], with complexities [CA] and [CB], has
    the pair of their complexities as its complexity. The case analysis
    gives the complexities of the elements to its branch. The order compares
    the elements; a pair of ground data is ground ([ProdGround]). *)
Module Type ProdData (Import CM : CostModel).
  #[global] Declare Instance Repr_prod :
    forall {A CA B CB}, Repr A CA -> Repr B CB -> Repr (A * B) (CA * CB).

  #[global] Declare Instance Size_prod : forall {A B}, Size A -> Size B -> Size (A * B).
  Parameter size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    size (a, b) = 1 + size a + size b.

  Parameter bound_order_prod : forall {A CA B CB} `{Repr A CA} `{Repr B CB} (c c' : CA * CB),
    bound_order (fst c) (fst c') -> bound_order (snd c) (snd c') -> bound_order c c'.
End ProdData.

(** Pairs of ground data are ground. *)
Module ProdGround (Import CM : CostModel) (Import PD : ProdData CM).
  Global Instance prod_ground {A CA B CB} {RA : Repr A CA} {RB : Repr B CB}
    {GA : IsGround RA} {GB : IsGround RB} : IsGround (Repr_prod RA RB) :=
    {| ground_indiscrete := fun c c' => bound_order_prod c c' (ground_order _ _) (ground_order _ _) |}.
End ProdGround.

Module Type ProdCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import PD : ProdData CM).

  Parameter c_pair : nat.
  #[global] Hint Unfold c_pair : costs.

  #[global] Declare Instance pair_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@pair A B) (fun ca => c_clo +> fun cb => c_pair +> (pot ca, pot cb)).
End ProdCtorTimeCostModel.

Module Type ProdCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import PD : ProdData CM).

  Parameter c_case_prod : nat.
  #[global] Hint Unfold c_case_prod : costs.

  (** The branch receives the elements with their complexities. *)
  #[global] Declare Instance prod_case_complexity :
    forall {X CX Y CY E CE A CA} `{Repr X CX} `{Repr Y CY} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@prod_case X Y E A)
      (fun cf : ℂI (env (env E X) Y -> A) (ℂI (env (env E X) Y) ((CE * CX) * CY) -> ℂO CA) =>
         c_clo +>
       fun cp : ℂI (E -> X * Y) (ℂI E CE -> ℂO (CX * CY)) => c_clo +>
       fun ce : ℂI E CE => c_case_prod ⊕ c_frame ⊕ cost (pot cp ce) ⊕
         let (x, y) := val cp (val ce) in
         let (cx, cy) := res (pot cp ce) in
         pot cf (ECons (ECons (val ce) x) y ⋊ ((pot ce, cx), cy))).
End ProdCaseTimeCostModel.

Module Type ProdTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  ProdData CM <+ ProdCtorTimeCostModel CM BT <+ ProdCaseTimeCostModel CM BT CB.

(** ** Sums (of any data)

    The sum [A + B] of the standard library, built with [inl] and [inr]. A
    match on a sum is compiled to [sum_case]; each branch receives the
    argument of its constructor, in its environment, as the branch of
    [Some] does.

    As for options ([OptionTimeCostModel]), the elements may
    be functions, or other data with complexities: a sum of [A] and [B],
    with complexities [CA] and [CB], has a sum of [CA] and [CB] as its
    complexity, that of its element, both [inl] or both [inr] (in L, the
    instance). The case analysis gives the complexity of the element to its
    branch. As for lists, the value gives the shape: when the value and its
    complexity disagree, the element has the default complexity
    ([cdefault]). The order compares the complexities of each side, the
    missing one being the default one ([sum_left], [sum_right]); a sum of
    ground data is ground ([SumGround]). *)

(** Case combinator (see [Combinators]). *)

Definition sum_case {X Y E A : Type} (l : env E X -> A) (r : env E Y -> A) (s : E -> X + Y)
  (e : E) : A :=
  match s e with inl x => l (ECons e x) | inr y => r (ECons e y) end.

#[global] Typeclasses Opaque sum_case.
#[global] Hint Unfold sum_case : comb.

#[global] Instance sum_inhabited {C D} `{Inhabited C} : Inhabited (C + D) := populate (inl inhabitant).

(** The complexity of each side of a sum, or a default one. *)
Definition sum_left {C D} (d : C) (s : C + D) : C := match s with inl x => x | inr _ => d end.
Definition sum_right {C D} (d : D) (s : C + D) : D := match s with inl _ => d | inr y => y end.

Module Type SumData (Import CM : CostModel).
  #[global] Declare Instance Repr_sum :
    forall {A CA B CB}, Repr A CA -> Repr B CB -> Repr (A + B) (CA + CB).

  #[global] Declare Instance Size_sum : forall {A B}, Size A -> Size B -> Size (A + B).
  (** The size of a sum is the size of its element, plus one. *)
  Parameter size_inl : forall {A B} `{Size A} `{Size B} (a : A), size (@inl A B a) = 1 + size a.
  Parameter size_inr : forall {A B} `{Size A} `{Size B} (b : B), size (@inr A B b) = 1 + size b.

  Parameter bound_order_sum : forall {A CA B CB} `{Repr A CA} `{Repr B CB} (c c' : CA + CB),
    bound_order (sum_left cdefault c) (sum_left cdefault c') ->
    bound_order (sum_right cdefault c) (sum_right cdefault c') -> bound_order c c'.
End SumData.

(** Sums of ground data are ground. *)
Module SumGround (Import CM : CostModel) (Import SD : SumData CM).
  Global Instance sum_ground {A CA B CB} {RA : Repr A CA} {RB : Repr B CB}
    {GA : IsGround RA} {GB : IsGround RB} : IsGround (Repr_sum RA RB) :=
    {| ground_indiscrete := fun c c' => bound_order_sum c c' (ground_order _ _) (ground_order _ _) |}.
End SumGround.

(** Both constructors cost [c_ctor_sum], as the constructors of the binary
    numbers cost [c_ctor_Z]. *)
Module Type SumCtorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM) (Import SD : SumData CM).

  Parameter c_ctor_sum : nat.
  #[global] Hint Unfold c_ctor_sum : costs.

  #[global] Declare Instance inl_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@inl A B) (fun ca => c_ctor_sum +> @inl CA CB (pot ca)).
  #[global] Declare Instance inr_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@inr A B) (fun cb => c_ctor_sum +> @inr CA CB (pot cb)).
End SumCtorTimeCostModel.

Module Type SumCaseTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import SD : SumData CM).

  Parameter c_case_sum : nat.
  #[global] Hint Unfold c_case_sum : costs.

  (** The branch of the value receives the element with its complexity (the
      default one if the complexity is of the other side). *)
  #[global] Declare Instance sum_case_complexity :
    forall {X CX Y CY E CE A CA} `{Repr X CX} `{Repr Y CY} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@sum_case X Y E A)
      (fun cl : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => c_clo +>
       fun cr : ℂI (env E Y -> A) (ℂI (env E Y) (CE * CY) -> ℂO CA) => c_clo +>
       fun cs : ℂI (E -> X + Y) (ℂI E CE -> ℂO (CX + CY)) => c_clo +>
       fun ce : ℂI E CE => c_case_sum ⊕ c_frame ⊕ cost (pot cs ce) ⊕
         match val cs (val ce), res (pot cs ce) with
         | inl x, inl cx => pot cl (ECons (val ce) x ⋊ (pot ce, cx))
         | inl x, inr _ => pot cl (ECons (val ce) x ⋊ (pot ce, cdefault))
         | inr y, inr cy => pot cr (ECons (val ce) y ⋊ (pot ce, cy))
         | inr y, inl _ => pot cr (ECons (val ce) y ⋊ (pot ce, cdefault))
         end).
End SumCaseTimeCostModel.

Module Type SumTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM)
  (CB : CombinatorTimeCostModel CM BT) :=
  SumData CM <+ SumCtorTimeCostModel CM BT <+ SumCaseTimeCostModel CM BT CB.

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
  #[global] Declare Instance Repr_positive : Repr positive unit.
  #[global] Declare Instance Repr_N : Repr N unit.
  #[global] Declare Instance Repr_Z : Repr Z unit.
  #[global] Declare Instance Repr_Q : Repr Q unit.
  #[global] Declare Instance Repr_comparison : Repr comparison unit.

  #[global] Declare Instance Size_positive : Size positive.
  #[global] Declare Instance Size_N : Size N.
  #[global] Declare Instance Size_Z : Size Z.
  #[global] Declare Instance Size_Q : Size Q.
  #[global] Declare Instance Size_comparison : Size comparison.
  (** The size of a [positive] is its number of binary digits
      ([Pos.size_nat]); [N] and [Z] have one more, for the sign or zero. *)
  Parameter size_xH : (size xH = 1)%nat.
  Parameter size_xO : (forall p, size (xO p) = 1 + size p)%nat.
  Parameter size_xI : (forall p, size (xI p) = 1 + size p)%nat.
  Parameter size_N0 : (size N0 = 1)%nat.
  Parameter size_Npos : (forall p, size (Npos p) = 1 + size p)%nat.
  Parameter size_Z0 : (size Z0 = 1)%nat.
  Parameter size_Zpos : (forall p, size (Zpos p) = 1 + size p)%nat.
  Parameter size_Zneg : (forall p, size (Zneg p) = 1 + size p)%nat.
  Parameter size_Qmake : (forall n d, size (Qmake n d) = 1 + size n + size d)%nat.
  Parameter size_comparison : (forall c : comparison, size c = 1)%nat.

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
