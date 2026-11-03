(** * Cost model for pairs (of ground data)

    Pairs were missing from the higher-order models: [let (x, y) := p in e]
    and the projections are compiled to [prod_case]. *)

From Complexity Require Import CostModel HOCostModel Combinators.

(** ** Case combinator (see [Combinators]) *)

Definition prod_case {X Y A : Type} (f : X -> Y -> A) (p : X * Y) : A :=
  match p with pair x y => f x y end.

#[global] Typeclasses Opaque prod_case.
#[global] Hint Unfold prod_case : comb.

Module Type ProdTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  Parameter prod_complexity : forall {A B} (p : A * B), ComplexityBound p tt.
  Global Existing Instance prod_complexity.

  Parameter pair_complexity : forall {A B},
    ComplexityBound (@pair A B) (fun _ : ℂI A unit => 1 ⋉ fun _ : ℂI B unit => 1 ⋉ tt).
  Global Existing Instance pair_complexity.

  Parameter prod_case_complexity : forall {X Y A CA},
    ComplexityBound (@prod_case X Y A)
      (fun cf : ℂI (X -> Y -> A) (ℂI X unit -> ℂO (ℂI Y unit -> ℂO CA)) => 0 ⋉
       fun cp : ℂI (X * Y) unit => 1 ⊕
         let (x, y) := ival cp in
         ((y ⋊ tt) I>>=O ((x ⋊ tt) I>>=I (ival cf ⋊ icomp cf))) >>|).
  Global Existing Instance prod_case_complexity.
End ProdTimeCostModel.
