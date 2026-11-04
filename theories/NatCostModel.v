From Complexity Require Import CostModel HOCostModel Combinators Compile
  CombinatorCostModel UnitCostModel FixCostModel.
From Stdlib Require Import Program.Basics Lia.

(** ** Case combinator (see [Combinators]) *)

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
  Parameter Repr_nat : Ground nat.
  Global Existing Instance Repr_nat.

  Parameter nat_complexity : forall n : nat, ComplexityBound n tt.
  Global Existing Instance nat_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : ℂI nat unit) => 1 ⋉ tt).
  Existing Instance S_complexity.



  (** ** Case analysis

      [nat_case] is a higher-order constant: matches on any expression, with
      branches using other variables, are compiled to it ([Compile]).
      Recursion is covered by the generic fixpoint axiom of [FixCostModel]. *)

  Parameter nat_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nat_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cs : ℂI (nat -> A) (ℂI nat unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI nat unit => 1 ⊕
         match val cn with O => pot cz (tt ⋊ tt) | S k => pot cs (k ⋊ tt) end).
  Global Existing Instance nat_case_complexity.
End NatTimeCostModel.

(* See NatComplexity.v for examples. *)
