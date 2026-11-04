(** * Cost models for the basic datatypes

    One module type for each datatype: booleans, natural numbers, lists,
    options and pairs of ground data, and binary numbers. Values are ground
    data, with sizes ([Size]); constructors and case analyses are primitive.
    Each case analysis is compiled to a case combinator ([Combinators]),
    defined here with its datatype. Recursion is covered by [FixCostModel]:
    the functions of the standard library are analysed as they are defined
    ([StdlibComplexity]). *)

From Complexity Require Import CostModel HOCostModel Combinators Compile
  CombinatorCostModel FixCostModel.
From Stdlib Require Import Program.Basics Lia List PArith NArith ZArith QArith.
Local Open Scope nat_scope.


(** ** Booleans *)

(** Case combinator (see [Combinators]). *)

Definition bool_case {A : Type} (t f : unit -> A) (b : bool) : A :=
  match b with true => t tt | false => f tt end.

#[global] Typeclasses Opaque bool_case.
#[global] Hint Unfold bool_case : comb.

Module Type BoolTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** Booleans are ground data. *)
  #[global] Declare Instance Repr_bool : Ground bool.

  #[global] Declare Instance Size_bool : Size bool.
  Parameter size_bool : forall b : bool, 0 < size b.

  #[global] Declare Instance bool_complexity : forall b : bool, ComplexityBound b tt.

  (** Case analysis, with the branches as thunks: only the selected branch is
      evaluated. [if] and every match on a boolean are compiled to it. *)
  #[global] Declare Instance bool_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@bool_case A)
      (fun ct : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cf : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cb : ℂI bool unit => 1 ⊕
         if val cb then pot ct (tt ⋊ tt) else pot cf (tt ⋊ tt)).
End BoolTimeCostModel.

(** ** Natural numbers *)

(** Case combinator (see [Combinators]). *)

Definition nat_case {A : Type} (z : unit -> A) (s : nat -> A) (n : nat) : A :=
  match n with O => z tt | S k => s k end.

#[global] Typeclasses Opaque nat_case.
#[global] Hint Unfold nat_case : comb.

Definition ℂI_nat_inj (n : nat) := n ⋊ tt.
Coercion ℂI_nat_inj : nat >-> ℂI.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

(*   Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat. *)
  
  (** ** Values and constructors

      Natural numbers are ground data. *)
  #[global] Declare Instance Repr_nat : Ground nat.

  #[global] Declare Instance Size_nat : Size nat.
  Parameter size_O : 0 < size 0.
  Parameter size_S : forall n, size n < size (S n).

  #[global] Declare Instance nat_complexity : forall n : nat, ComplexityBound n tt.

  Parameter S_complexity : ComplexityBound S (fun x => 1 ⋉ tt).
  Existing Instance S_complexity.



  (** ** Case analysis

      [nat_case] is a higher-order constant: matches on any expression, with
      branches using other variables, are compiled to it ([Compile]).
      Recursion is covered by the generic fixpoint axiom of [FixCostModel]. *)

  #[global] Declare Instance nat_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nat_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cs : ℂI (nat -> A) (ℂI nat unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI nat unit => 1 ⊕
         match val cn with O => pot cz (tt ⋊ tt) | S k => pot cs (k ⋊ tt) end).
End NatTimeCostModel.

(* See NatComplexity.v for examples. *)

(** ** Lists (of ground data) *)

(** Case combinator (see [Combinators]). *)

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
  #[global] Declare Instance Repr_list : forall {A}, Ground A -> Ground (list A).

  #[global] Declare Instance Size_list : forall {A}, Size A -> Size (list A).
  Parameter size_nil : forall {A} `{Size A}, 0 < size (@nil A).
  Parameter size_cons : forall {A} `{Size A} (a : A) l, size a + size l < size (a :: l).

  (** The empty list is a value; the other lists are built with [cons]. *)
  #[global] Declare Instance nil_complexity : forall {A} `{Ground A}, ComplexityBound (@nil A) tt.
  (* TODO: annoyingly, this is required for cons_complexity to find the typeclass instance *)
(*   Global Instance CT_cons {A CA : Type}: CT (A -> list A -> list A)
                        (ℂI A -> ℂO (ℂI (list A) -> ℂO (list CA))).
  Proof. typeclasses eauto. Defined. *)

  #[global] Declare Instance cons_complexity: forall {A : Type} `{Ground A},
    ComplexityBound (@cons A)
                    (fun h => 1 ⋉ ( (* we may not need so many 1s *)
                     fun t => 1 ⋉ tt)).


  (** Case analysis, as a higher-order constant: matches on any expression,
      with branches using other variables, are compiled to it ([Compile]). *)
  #[global] Declare Instance list_case_complexity : forall {X A CA} `{Ground X} `{Repr A CA},
    ComplexityBound (@list_case X A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cc : ℂI (X -> list X -> A) (ℂI X unit -> ℂO (ℂI (list X) unit -> ℂO CA)) => 1 ⋉
       fun cl : ℂI (list X) unit => 1 ⊕
         match val cl with
         | nil => pot cz (tt ⋊ tt)
         | cons h t => pot <$> cc · (h ⋊ tt) · (t ⋊ tt)
         end).

End ListTimeCostModel.

(** ** Options (of ground data) *)

(** Case combinator (see [Combinators]). *)

Definition option_case {X A : Type} (s : X -> A) (z : unit -> A) (o : option X) : A :=
  match o with Some x => s x | None => z tt end.

#[global] Typeclasses Opaque option_case.
#[global] Hint Unfold option_case : comb.

Module Type OptionTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** Options of ground data are ground data. *)
  #[global] Declare Instance Repr_option : forall {A}, Ground A -> Ground (option A).

  #[global] Declare Instance Size_option : forall {A}, Size A -> Size (option A).
  Parameter size_None : forall {A} `{Size A}, 0 < size (@None A).
  Parameter size_Some : forall {A} `{Size A} (a : A), size a < size (Some a).

  (** [None] is a value; the other options are built with [Some]. *)
  #[global] Declare Instance None_complexity : forall {A} `{Ground A}, ComplexityBound (@None A) tt.

  #[global] Declare Instance Some_complexity : forall {A} `{Ground A},
    ComplexityBound (@Some A) (fun _ => 1 ⋉ tt).

  #[global] Declare Instance option_case_complexity : forall {X A CA} `{Ground X} `{Repr A CA},
    ComplexityBound (@option_case X A)
      (fun cs : ℂI (X -> A) (ℂI X unit -> ℂO CA) => 1 ⋉
       fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun co : ℂI (option X) unit => 1 ⊕
         match val co with
         | Some x => pot cs (x ⋊ tt)
         | None => pot cz (tt ⋊ tt)
         end).
End OptionTimeCostModel.

(** ** Pairs (of ground data)

    Pairs were missing from the higher-order models: [let (x, y) := p in e]
    and the projections are compiled to [prod_case]. *)

(** Case combinator (see [Combinators]). *)

Definition prod_case {X Y A : Type} (f : X -> Y -> A) (p : X * Y) : A :=
  match p with pair x y => f x y end.

#[global] Typeclasses Opaque prod_case.
#[global] Hint Unfold prod_case : comb.

Module Type ProdTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  #[global] Declare Instance Repr_prod : forall {A B}, Ground A -> Ground B -> Ground (A * B).

  #[global] Declare Instance Size_prod : forall {A B}, Size A -> Size B -> Size (A * B).
  Parameter size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    size a + size b < size (a, b).

  (* Pairs are built with [pair]. *)

  #[global] Declare Instance pair_complexity : forall {A B} `{Ground A} `{Ground B},
    ComplexityBound (@pair A B) (fun _ => 1 ⋉ fun _ => 1 ⋉ tt).

  #[global] Declare Instance prod_case_complexity :
    forall {X Y A CA} `{Ground X} `{Ground Y} `{Repr A CA},
    ComplexityBound (@prod_case X Y A)
      (fun cf : ℂI (X -> Y -> A) (ℂI X unit -> ℂO (ℂI Y unit -> ℂO CA)) => 1 ⋉
       fun cp : ℂI (X * Y) unit => 1 ⊕
         let (x, y) := val cp in
         pot <$> cf · (x ⋊ tt) · (y ⋊ tt)).
End ProdTimeCostModel.

(** ** Binary numbers: [positive], [N], [Z], and [Q] *)

(** Case combinators (see [Combinators]). *)

Definition positive_case {A : Type} (fI fO : positive -> A) (fH : unit -> A) (p : positive) : A :=
  match p with xI q => fI q | xO q => fO q | xH => fH tt end.
Definition N_case {A : Type} (z : unit -> A) (f : positive -> A) (n : N) : A :=
  match n with N0 => z tt | Npos p => f p end.
Definition Z_case {A : Type} (z : unit -> A) (fp fn : positive -> A) (x : Z) : A :=
  match x with Z0 => z tt | Zpos p => fp p | Zneg p => fn p end.
Definition comparison_case {A : Type} (eq lt gt : unit -> A) (c : comparison) : A :=
  match c with Eq => eq tt | Lt => lt tt | Gt => gt tt end.
Definition Q_case {A : Type} (f : Z -> positive -> A) (q : Q) : A :=
  match q with Qmake n d => f n d end.

#[global] Typeclasses Opaque positive_case N_case Z_case comparison_case Q_case.
#[global] Hint Unfold positive_case N_case Z_case comparison_case Q_case : comb.

Module Type ZTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** ** Values, constructors, case analysis *)

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

  #[global] Declare Instance xI_complexity : ComplexityBound xI (fun _ => 1 ⋉ tt).
  #[global] Declare Instance xO_complexity : ComplexityBound xO (fun _ => 1 ⋉ tt).
  #[global] Declare Instance Npos_complexity : ComplexityBound Npos (fun _ => 1 ⋉ tt).
  #[global] Declare Instance Zpos_complexity : ComplexityBound Zpos (fun _ => 1 ⋉ tt).
  #[global] Declare Instance Zneg_complexity : ComplexityBound Zneg (fun _ => 1 ⋉ tt).
  #[global] Declare Instance Qmake_complexity :
    ComplexityBound Qmake (fun _ => 1 ⋉ fun _ => 1 ⋉ tt).

  #[global] Declare Instance positive_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@positive_case A)
      (fun cI : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cO : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cH : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI positive unit => 1 ⊕
         match val cp with
         | xI q => pot cI (q ⋊ tt)
         | xO q => pot cO (q ⋊ tt)
         | xH => pot cH (tt ⋊ tt)
         end).

  #[global] Declare Instance N_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@N_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI N unit => 1 ⊕
         match val cn with N0 => pot cz (tt ⋊ tt) | Npos p => pot cp (p ⋊ tt) end).

  #[global] Declare Instance Z_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Z_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cx : ℂI Z unit => 1 ⊕
         match val cx with
         | Z0 => pot cz (tt ⋊ tt)
         | Zpos p => pot cp (p ⋊ tt)
         | Zneg p => pot cn (p ⋊ tt)
         end).

  #[global] Declare Instance comparison_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@comparison_case A)
      (fun ce : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cl : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cg : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cc : ℂI comparison unit => 1 ⊕
         match val cc with
         | Eq => pot ce (tt ⋊ tt)
         | Lt => pot cl (tt ⋊ tt)
         | Gt => pot cg (tt ⋊ tt)
         end).

  #[global] Declare Instance Q_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Q_case A)
      (fun cf : ℂI (Z -> positive -> A) (ℂI Z unit -> ℂO (ℂI positive unit -> ℂO CA)) => 1 ⋉
       fun cq : ℂI Q unit => 1 ⊕
         match val cq with
         | Qmake n d => pot <$> cf · (n ⋊ tt) · (d ⋊ tt)
         end).
End ZTimeCostModel.

(** ** Examples *)

(** Derived complexity bounds for list operators. *)
Module Type ListTimeExamples
  (Import CM : CostModel)
  (Import BTM : BasicTimeCostModel CM)
  (Import LM : ListTimeCostModel CM BTM)
  (Import CB : CombinatorTimeCostModel CM BTM).

  (** ** List tail *)
  Instance complexity_tl {A} `{Ground A} :
    ComplexityBound (@tl A) (fun lc => 4 ⋉ tt).
  Proof. cbound. Qed.

End ListTimeExamples.
