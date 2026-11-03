(** * Cost model for binary numbers: [positive], [N], [Z], and [Q]

    Values are ground data. Constructors and case analyses are primitive, as
    for [nat]. Recursion is covered by [FixCostModel]: the operations of the
    standard library are analysed as they are defined ([PosComplexity],
    [ZComplexity]). *)

From Complexity Require Import CostModel HOCostModel Combinators.
From Stdlib Require Import PArith NArith ZArith QArith.

(** ** Case combinators (see [Combinators]) *)

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

  Parameter positive_complexity : forall p : positive, ComplexityBound p tt.
  Global Existing Instance positive_complexity.
  Parameter N_complexity : forall n : N, ComplexityBound n tt.
  Global Existing Instance N_complexity.
  Parameter Z_complexity : forall z : Z, ComplexityBound z tt.
  Global Existing Instance Z_complexity.
  Parameter Q_complexity : forall q : Q, ComplexityBound q tt.
  Global Existing Instance Q_complexity.
  Parameter comparison_complexity : forall c : comparison, ComplexityBound c tt.
  Global Existing Instance comparison_complexity.

  Parameter xI_complexity : ComplexityBound xI (fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance xI_complexity.
  Parameter xO_complexity : ComplexityBound xO (fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance xO_complexity.
  Parameter Npos_complexity : ComplexityBound Npos (fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance Npos_complexity.
  Parameter Zpos_complexity : ComplexityBound Zpos (fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance Zpos_complexity.
  Parameter Zneg_complexity : ComplexityBound Zneg (fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance Zneg_complexity.
  Parameter Qmake_complexity :
    ComplexityBound Qmake (fun _ : ℂI Z unit => 1 ⋉ fun _ : ℂI positive unit => 1 ⋉ tt).
  Global Existing Instance Qmake_complexity.

  Parameter positive_case_complexity : forall {A CA},
    ComplexityBound (@positive_case A)
      (fun cI : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 0 ⋉
       fun cO : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 0 ⋉
       fun cH : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cp : ℂI positive unit => 1 ⊕
         match ival cp with
         | xI q => icomp cI (q ⋊ tt)
         | xO q => icomp cO (q ⋊ tt)
         | xH => icomp cH (tt ⋊ tt)
         end).
  Global Existing Instance positive_case_complexity.

  Parameter N_case_complexity : forall {A CA},
    ComplexityBound (@N_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 0 ⋉
       fun cn : ℂI N unit => 1 ⊕
         match ival cn with N0 => icomp cz (tt ⋊ tt) | Npos p => icomp cp (p ⋊ tt) end).
  Global Existing Instance N_case_complexity.

  Parameter Z_case_complexity : forall {A CA},
    ComplexityBound (@Z_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 0 ⋉
       fun cn : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 0 ⋉
       fun cx : ℂI Z unit => 1 ⊕
         match ival cx with
         | Z0 => icomp cz (tt ⋊ tt)
         | Zpos p => icomp cp (p ⋊ tt)
         | Zneg p => icomp cn (p ⋊ tt)
         end).
  Global Existing Instance Z_case_complexity.

  Parameter comparison_case_complexity : forall {A CA},
    ComplexityBound (@comparison_case A)
      (fun ce : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cl : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cg : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cc : ℂI comparison unit => 1 ⊕
         match ival cc with
         | Eq => icomp ce (tt ⋊ tt)
         | Lt => icomp cl (tt ⋊ tt)
         | Gt => icomp cg (tt ⋊ tt)
         end).
  Global Existing Instance comparison_case_complexity.

  Parameter Q_case_complexity : forall {A CA},
    ComplexityBound (@Q_case A)
      (fun cf : ℂI (Z -> positive -> A) (ℂI Z unit -> ℂO (ℂI positive unit -> ℂO CA)) => 0 ⋉
       fun cq : ℂI Q unit => 1 ⊕
         match ival cq with
         | Qmake n d => ((d ⋊ tt) I>>=O ((n ⋊ tt) I>>=I cf)) >>|
         end).
  Global Existing Instance Q_case_complexity.
End ZTimeCostModel.
