(** * Complexity of functions over [positive] from the standard library

    As in [NatComplexity]: each function is analysed as defined, with
    [cbound] (or [cbound_mutual] for [Pos.add] and [Pos.add_carry]) and the
    smallest constants for the shape of the bound. Costs are linear in the
    bit size [Pos.size_nat] ([BitSize]). *)

From Complexity Require Export NatComplexity.
From Complexity Require Import BitSize.
From Stdlib Require Import PArith.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

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
    (fun cp => (14 * Pos.size_nat (val cp)) >|) := _.

  Global Instance Pos_pred_double_complexity : Time.ComplexityBound Pos.pred_double
    (fun cp => (14 * Pos.size_nat (val cp)) >|).
  Proof. cbound. all: size_facts; lia. Qed.

  Global Instance Pos_eqb_complexity : Time.ComplexityBound Pos.eqb
    (fun cp => 4 +> fun cq =>
       (28 * Pos.size_nat (val cp)) >|) := _.

  (** [Pos.compare_cont] is recursive on its third argument. *)
  Global Instance Pos_compare_cont_complexity : Time.ComplexityBound Pos.compare_cont
    (fun cr => 4 +> fun cp => 2 +>
     fun cq => (42 * Pos.size_nat (val cq)) >|) := _.

  (** [Pos.add] and [Pos.add_carry] are mutually recursive: the recursion is
      analysed on the function [fun b => if b then Pos.add else
      Pos.add_carry], from which both bounds follow ([cproject]). *)
  Lemma Pos_add_mutual_complexity :
    Time.ComplexityBound (fun b : bool => if b then Pos.add else Pos.add_carry)
      (fun cb => 6 +> fun cx => 2 +>
       fun cy =>
         (19 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) >|).
  Proof. cbound_mutual. Qed.

  Global Instance Pos_add_complexity : Time.ComplexityBound Pos.add
    (fun cx => 2 +> fun cy =>
       (19 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) >|).
  Proof. cproject Pos_add_mutual_complexity true. Qed.

  Global Instance Pos_add_carry_complexity : Time.ComplexityBound Pos.add_carry
    (fun cx => 2 +> fun cy =>
       (19 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) >|).
  Proof. cproject Pos_add_mutual_complexity false. Qed.

  (** [Pos.compare] is [Pos.compare_cont Eq]. *)
  Global Instance Pos_compare_complexity : Time.ComplexityBound Pos.compare
    (fun cx => 2 +> fun cy =>
       (42 * Pos.size_nat (val cy)) >|) := _.

  (** The recursive step of [Pos.mul] adds [y] to the doubled product: its
      cost depends on the size of the product. *)
  Global Instance Pos_mul_complexity : Time.ComplexityBound Pos.mul
    (fun cx => 1 +> fun cy =>
       (Pos.size_nat (val cx) *
          (38 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)))) >|).
  Proof. cbound. all: try pose proof (size_nat_mul cx cy); size_facts; nia. Qed.

  (** [Pos.of_succ_nat n] calls [Pos.succ] [n] times, on numbers of size at
      most the size of the result. *)
  Global Instance Pos_of_succ_nat_complexity : Time.ComplexityBound Pos.of_succ_nat
    (fun cn =>
       (val cn * (27 * Pos.size_nat (Pos.of_succ_nat (val cn))) + 6) >|).
  Proof. cbound. all: pose proof (size_nat_succ (Pos.of_succ_nat cn)); size_facts; nia. Qed.

  Global Instance Pos_of_nat_complexity : Time.ComplexityBound Pos.of_nat
    (fun cn =>
       (val cn * (33 * Pos.size_nat (Pos.of_nat (val cn))) + 6) >|).
  Proof.
    cbound. pose proof (size_nat_succ (Pos.of_nat (S cn))).
    pose proof (size_nat_pos (Pos.of_nat (S cn))). cbn [Pos.of_nat] in *. nia.
  Qed.

  (** [Pos.to_nat] is [Pos.iter_op Nat.add p 1]: on unary numbers, the
      accumulator doubles at each step, and so does the cost of the
      additions. *)
  Global Instance Pos_iter_op_add_complexity : Time.ComplexityBound (Pos.iter_op Nat.add)
    (fun cp => 4 +> fun ca =>
       (14 * (Pos.to_nat (val cp) - 1) * val ca + 54 * Pos.size_nat (val cp)) >|).
  Proof.
    cbound. all: pose proof (Pos2Nat.is_pos cp);
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *; nia.
  Qed.

  Global Instance Pos_to_nat_complexity : Time.ComplexityBound Pos.to_nat
    (fun cp =>
       (14 * Pos.to_nat (val cp) + 54 * Pos.size_nat (val cp)) >|).
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
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma Pos_succ_size_complexity :
    Time.ComplexityBound Pos.succ
      (fun (cp : ℂI positive _) => (14 * #|val cp|) >|).
  Proof. csize_using Pos_succ_complexity. Qed.

  Lemma Pos_pred_double_size_complexity :
    Time.ComplexityBound Pos.pred_double
      (fun (cp : ℂI positive _) => (14 * #|val cp|) >|).
  Proof. csize_using Pos_pred_double_complexity. Qed.

  Lemma Pos_eqb_size_complexity :
    Time.ComplexityBound Pos.eqb
      (fun (cp : ℂI positive _) => 4 +> fun cq => (28 * #|val cp|) >|).
  Proof. csize_using Pos_eqb_complexity. Qed.

  Lemma Pos_compare_cont_size_complexity :
    Time.ComplexityBound Pos.compare_cont
      (fun cr => 4 +> fun cp => 2 +> fun (cq : ℂI positive _) => (42 * #|val cq|) >|).
  Proof. csize_using Pos_compare_cont_complexity. Qed.

  Lemma Pos_add_mutual_size_complexity :
    Time.ComplexityBound (fun b : bool => if b then Pos.add else Pos.add_carry)
      (fun cb => 6 +> fun (cx : ℂI positive _) => 2 +> fun (cy : ℂI positive _) => (19 * (#|val cx| + #|val cy|)) >|).
  Proof. csize_using Pos_add_mutual_complexity. Qed.

  Lemma Pos_add_size_complexity :
    Time.ComplexityBound Pos.add
      (fun (cx : ℂI positive _) => 2 +> fun (cy : ℂI positive _) => (19 * (#|val cx| + #|val cy|)) >|).
  Proof. csize_using Pos_add_complexity. Qed.

  Lemma Pos_add_carry_size_complexity :
    Time.ComplexityBound Pos.add_carry
      (fun (cx : ℂI positive _) => 2 +> fun (cy : ℂI positive _) => (19 * (#|val cx| + #|val cy|)) >|).
  Proof. csize_using Pos_add_carry_complexity. Qed.

  Lemma Pos_compare_size_complexity :
    Time.ComplexityBound Pos.compare
      (fun cx => 2 +> fun (cy : ℂI positive _) => (42 * #|val cy|) >|).
  Proof. csize_using Pos_compare_complexity. Qed.

  Lemma Pos_mul_size_complexity :
    Time.ComplexityBound Pos.mul
      (fun (cx : ℂI positive _) => 1 +> fun (cy : ℂI positive _) => (#|val cx| * (38 * (#|val cx| + #|val cy|))) >|).
  Proof. csize_using Pos_mul_complexity. Qed.

End PosComplexity.

(** The time cost model with the analyses of [nat] and [positive]. *)
Module Type TimePos := TimeNat <+ PosComplexity.
