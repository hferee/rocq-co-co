(** * Complexity of functions over [positive] from the standard library

    As in [NatComplexity]: each function is analysed as defined, with
    [cbound] (or [cbound_mutual] for [Pos.add] and [Pos.add_carry]) and the
    smallest constants for the shape of the bound. Costs are linear in the
    bit size [Pos.size_nat] ([BitSize]). *)

From Complexity Require Export NatComplexity.
From Complexity Require Import BitSize.
From Stdlib Require Import PArith.

Module PosComplexity (Import Time : TimeNat).


  (** ** Sizes *)
  Lemma size_nat_le_size (p : positive) : Pos.size_nat p <= size p.
  Proof.
    induction p; cbn; [pose proof (size_xI p) | pose proof (size_xO p) | pose proof size_xH]; lia.
  Qed.
  Global Instance positive_size_fact (p : positive) : SizeFact p (Pos.size_nat p <= size p) :=
    size_nat_le_size p.

  (** ** Bounds *)

  Global Instance Pos_succ_complexity : Time.ComplexityBound Pos.succ
    (fun cp => (18 * Pos.size_nat (val cp)) ⋉ tt) := _.

  Global Instance Pos_pred_double_complexity : Time.ComplexityBound Pos.pred_double
    (fun cp => (16 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. all: size_facts; lia. Qed.

  Global Instance Pos_eqb_complexity : Time.ComplexityBound Pos.eqb
    (fun cp => 5 ⋉ fun cq =>
       (50 * Pos.size_nat (val cp)) ⋉ tt) := _.

  (** [Pos.compare_cont] is recursive on its third argument. *)
  Global Instance Pos_compare_cont_complexity : Time.ComplexityBound Pos.compare_cont
    (fun cr => 5 ⋉ fun cp => 2 ⋉
     fun cq => (86 * Pos.size_nat (val cq)) ⋉ tt) := _.

  (** [Pos.add] and [Pos.add_carry] are mutually recursive: the recursion is
      analysed on the function [fun b => if b then Pos.add else
      Pos.add_carry], from which both bounds follow. *)
  Lemma Pos_add_mutual_complexity :
    Time.ComplexityBound (fun b : bool => if b then Pos.add else Pos.add_carry)
      (fun cb => 14 ⋉ fun cx => 2 ⋉
       fun cy =>
         (34 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt).
  Proof. cbound_mutual. Qed.

  Global Instance Pos_add_complexity : Time.ComplexityBound Pos.add
    (fun cx => 2 ⋉ fun cy =>
       (34 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt) :=
    ltac:(exact (apply_complexity (v := true) _ _ Pos_add_mutual_complexity)).

  Global Instance Pos_add_carry_complexity : Time.ComplexityBound Pos.add_carry
    (fun cx => 2 ⋉ fun cy =>
       (34 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) ⋉ tt) :=
    ltac:(exact (apply_complexity (v := false) _ _ Pos_add_mutual_complexity)).

  (** [Pos.compare] is [Pos.compare_cont Eq]. *)
  Global Instance Pos_compare_complexity : Time.ComplexityBound Pos.compare
    (fun cx => 2 ⋉ fun cy =>
       (86 * Pos.size_nat (val cy)) ⋉ tt) := _.

  (** The recursive step of [Pos.mul] adds [y] to the doubled product: its
      cost depends on the size of the product. *)
  Global Instance Pos_mul_complexity : Time.ComplexityBound Pos.mul
    (fun cx => 5 ⋉ fun cy =>
       (Pos.size_nat (val cx) *
          (68 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)))) ⋉ tt).
  Proof. cbound. all: try pose proof (size_nat_mul cx cy); size_facts; nia. Qed.

  (** [Pos.of_succ_nat n] calls [Pos.succ] [n] times, on numbers of size at
      most the size of the result. *)
  Global Instance Pos_of_succ_nat_complexity : Time.ComplexityBound Pos.of_succ_nat
    (fun cn =>
       (val cn * (31 * Pos.size_nat (Pos.of_succ_nat (val cn))) + 7) ⋉ tt).
  Proof. cbound. all: pose proof (size_nat_succ (Pos.of_succ_nat cn)); size_facts; nia. Qed.

  Global Instance Pos_of_nat_complexity : Time.ComplexityBound Pos.of_nat
    (fun cn =>
       (val cn * (42 * Pos.size_nat (Pos.of_nat (val cn))) + 7) ⋉ tt).
  Proof.
    cbound. pose proof (size_nat_succ (Pos.of_nat (S cn))).
    pose proof (size_nat_pos (Pos.of_nat (S cn))). cbn [Pos.of_nat] in *. nia.
  Qed.

  (** [Pos.to_nat] is [Pos.iter_op Nat.add p 1]: on unary numbers, the
      accumulator doubles at each step, and so does the cost of the
      additions. *)
  Global Instance Pos_iter_op_add_complexity : Time.ComplexityBound (Pos.iter_op Nat.add)
    (fun cp => 5 ⋉ fun ca =>
       (36 * (Pos.to_nat (val cp) - 1) * val ca + 83 * Pos.size_nat (val cp)) ⋉ tt).
  Proof.
    cbound. all: pose proof (Pos2Nat.is_pos cp);
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *; nia.
  Qed.

  Global Instance Pos_to_nat_complexity : Time.ComplexityBound Pos.to_nat
    (fun cp =>
       (36 * Pos.to_nat (val cp) + 83 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. cbound. all: pose proof (Pos2Nat.is_pos cp); lia. Qed.

  (** ** Bounds in the size of the arguments

      [Pos.iter_op Nat.add] and [Pos.to_nat] are exponential in the size of
      their argument: their results are unary numbers. *)
  Global Instance Pos_succ_linear_bound : Time.LinearBound Pos.succ := _.
  Global Instance Pos_pred_double_linear_bound : Time.LinearBound Pos.pred_double := _.
  Global Instance Pos_eqb_linear_bound : Time.LinearBound Pos.eqb := _.
  Global Instance Pos_compare_cont_linear_bound : Time.LinearBound Pos.compare_cont := _.
  Global Instance Pos_add_linear_bound : Time.LinearBound Pos.add := _.
  Global Instance Pos_add_carry_linear_bound : Time.LinearBound Pos.add_carry := _.
  Global Instance Pos_compare_linear_bound : Time.LinearBound Pos.compare := _.
  Global Instance Pos_mul_polynomial_bound : Time.PolynomialBound Pos.mul := _.

  (** The size of the result is bounded by the argument. *)
  Global Instance Pos_of_succ_nat_polynomial_bound : Time.PolynomialBound Pos.of_succ_nat.
  Proof.
    cpolynomial.
    all: match goal with |- context [Pos.of_succ_nat ?n] => pose proof (size_nat_of_succ_nat n) end.
    all: nia.
  Qed.
  Global Instance Pos_of_nat_polynomial_bound : Time.PolynomialBound Pos.of_nat.
  Proof.
    cpolynomial.
    all: match goal with |- context [Pos.of_nat ?n] => pose proof (size_nat_of_nat n) end.
    all: nia.
  Qed.
End PosComplexity.

(** The time cost model with the analyses of [nat] and [positive]. *)
Module Type TimePos := TimeNat <+ PosComplexity.
