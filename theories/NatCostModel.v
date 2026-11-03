From Complexity Require Import CostModel HOCostModel Combinators Compile
  CombinatorCostModel UnitCostModel FixCostModel.
From Stdlib Require Import Program.Basics Lia.

(** ** Case combinator (see [Combinators]) *)

Definition nat_case {A : Type} (z : unit -> A) (s : nat -> A) (n : nat) : A :=
  match n with O => z tt | S k => s k end.

#[global] Typeclasses Opaque nat_case.
#[global] Hint Unfold nat_case : comb.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

(*   Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat. *)
  
  (** ** Values and constructors

      Natural numbers are ground data. *)
  Parameter nat_complexity : forall n : nat, ComplexityBound n tt.
  Global Existing Instance nat_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : ℂI nat unit) => 1 ⋉ tt).
  Existing Instance S_complexity.

  Definition ℂI_nat_inj (n : nat) := n ⋊ tt.
  Coercion ℂI_nat_inj : nat >-> ℂI.

  Parameter bound_order_nat : forall (n m : nat),
    bound_order n m <-> n <= m.


  (** ** Case analysis

      [nat_case] is a higher-order constant: matches on any expression, with
      branches using other variables, are compiled to it ([Compile]).
      Recursion is covered by the generic fixpoint axiom of [FixCostModel]. *)

  Parameter nat_case_complexity : forall {A CA},
    ComplexityBound (@nat_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cs : ℂI (nat -> A) (ℂI nat unit -> ℂO CA) => 0 ⋉
       fun cn : ℂI nat unit => 1 ⊕
         match ival cn with O => icomp cz (tt ⋊ tt) | S k => icomp cs (k ⋊ tt) end).
  Global Existing Instance nat_case_complexity.
End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel)
  (Import BT : BasicTimeCostModel CM) (Import B: NatTimeCostModel CM BT)
  (Import CB : CombinatorTimeCostModel CM BT) (Import UN : UnitTimeCostModel CM)
  (Import FX : FixTimeCostModel CM BT).

  Example plus2 (n : nat) := S (S n).

  Example plus2_complexity: ComplexityBound plus2 (fun (n : ℂI nat unit) => 2 ⋉ tt).
  Proof.
  capply.
  (* TODO: explicit type annotations are annoying *)
  eapply compose_complexity; apply S_complexity.
  Unshelve. apply bound_order_ext_eq. intros. unfold OIbindO. reflexivity.
  Qed.

  (** Recursive functions: [crec] states the unfolding equation of the
      fixpoint, [cbc] finds the complexity of its functional, and the
      recurrence remains. The constants are the smallest ones for the shape
      of the bound (see [NatComplexity], which proves the same bounds). *)
  Example plus_complexity:
    ComplexityBound Nat.add (fun (n : ℂI nat unit) => 2 ⋉
                          fun (m : ℂI nat unit) => (5 * ival n + 2) ⋉ tt).
  Proof.
  crec; [cbc |].
  intro n; bo_split; destr_inputs; [cbn; lia |].
  destruct n; cbn -[Nat.mul]; lia.
  Qed.
  Existing Instance plus_complexity.

  Example mult_complexity:
    ComplexityBound Nat.mul (fun (n : ℂI nat unit) => 2 ⋉
                             fun (m : ℂI nat unit) => (ival n * (5 * ival m + 9) + 2) ⋉ tt).
  Proof.
  crec; [cbc |].
  intro n; bo_split; destr_inputs; [cbn; lia |].
  destruct n; cbn -[Nat.mul]; lia.
  Qed.
End NatTimeExamples.
