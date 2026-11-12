(** * Complexity of functions over [nat] from the standard library

    Each function is analysed as defined in the standard library, by
    [cbound] ([TimeFix]).

    The constants are the smallest ones for the shape of each bound: they
    were found by stating the bound with abstract constants, which [cbound]
    turns into the inequalities that the recurrence requires. The first cost
    ([5] for [Nat.add]) is the cost of the partial application to the first
    argument; the cost of a step of the recursion includes it, since the
    recursive call is a partial application too. *)

From Complexity Require Export TimeCostModel.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module NatComplexity (Import Time : TimeCostModel).

  (** ** Sizes *)
  Lemma nat_lt_size (n : nat) : n < size n.
  Proof. induction n; [apply size_O | pose proof (size_S n); lia]. Qed.
  Global Instance nat_size_fact (n : nat) : SizeFact n (n < size n) := nat_lt_size n.

  (** ** Bounds *)

  Global Instance Nat_add_complexity : Time.ComplexityBound Nat.add
    (fun cn => 4 +> fun cm => (22 * val cn + 6) >|) := _.

  (** [Nat.sub] is recursive on its first argument and matches on the second
      one. *)
  Global Instance Nat_sub_complexity : Time.ComplexityBound Nat.sub
    (fun cn => 4 +> fun cm => (26 * val cn + 8) >|) := _.

  Global Instance Nat_eqb_complexity : Time.ComplexityBound Nat.eqb
    (fun cn => 4 +> fun cm => (26 * val cn + 8) >|) := _.

  Global Instance Nat_leb_complexity : Time.ComplexityBound Nat.leb
    (fun cn => 4 +> fun cm => (26 * val cn + 6) >|) := _.

  (** [Nat.ltb] is not recursive: its complexity follows from the one of
      [Nat.leb] by compilation alone. *)
  Global Instance Nat_ltb_complexity : Time.ComplexityBound Nat.ltb
    (fun cn => 1 +> fun cm => (26 * val cn + 43) >|) := _.

  (** The recursive branch of [Nat.mul] calls [Nat.add]. *)
  Global Instance Nat_mul_complexity : Time.ComplexityBound Nat.mul
    (fun cn => 4 +> fun cm =>
       (val cn * (22 * val cm + 35) + 6) >|) := _.

  (** [Nat.pow] is recursive on its second argument, and the step [m] calls
      [Nat.mul] on [n ^ m]: the sum of the [n ^ i] is bounded by
      [m * n ^ m]. *)
  Global Instance Nat_pow_complexity : Time.ComplexityBound Nat.pow
    (fun cn => 4 +> fun cm =>
       (22 * val cm * val cn ^ val cm + val cm * (35 * val cn + 37) + 4) >|).
  Proof. cbound. destruct cn; [destruct cm; cbn; lia | nia]. Qed.

  (** ** Bounds in the size of the arguments

      [Nat.pow] is exponential in the size of its second argument. *)
  Global Instance Nat_add_linear_bound : Time.LinearBound Nat.add := _.
  Global Instance Nat_sub_linear_bound : Time.LinearBound Nat.sub := _.
  Global Instance Nat_eqb_linear_bound : Time.LinearBound Nat.eqb := _.
  Global Instance Nat_leb_linear_bound : Time.LinearBound Nat.leb := _.
  Global Instance Nat_ltb_linear_bound : Time.LinearBound Nat.ltb := _.
  Global Instance Nat_mul_polynomial_bound : Time.PolynomialBound Nat.mul := _.
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma Nat_add_size_complexity :
    Time.ComplexityBound Nat.add
      (fun (cn : ℂI nat _) => 4 +> fun cm => (22 * #|val cn| + 6) >|).
  Proof. csize_using Nat_add_complexity. Qed.

  Lemma Nat_sub_size_complexity :
    Time.ComplexityBound Nat.sub
      (fun (cn : ℂI nat _) => 4 +> fun cm => (26 * #|val cn| + 8) >|).
  Proof. csize_using Nat_sub_complexity. Qed.

  Lemma Nat_eqb_size_complexity :
    Time.ComplexityBound Nat.eqb
      (fun (cn : ℂI nat _) => 4 +> fun cm => (26 * #|val cn| + 8) >|).
  Proof. csize_using Nat_eqb_complexity. Qed.

  Lemma Nat_leb_size_complexity :
    Time.ComplexityBound Nat.leb
      (fun (cn : ℂI nat _) => 4 +> fun cm => (26 * #|val cn| + 6) >|).
  Proof. csize_using Nat_leb_complexity. Qed.

  Lemma Nat_ltb_size_complexity :
    Time.ComplexityBound Nat.ltb
      (fun (cn : ℂI nat _) => 1 +> fun cm => (26 * #|val cn| + 43) >|).
  Proof. csize_using Nat_ltb_complexity. Qed.

  Lemma Nat_mul_size_complexity :
    Time.ComplexityBound Nat.mul
      (fun (cn : ℂI nat _) => 4 +> fun (cm : ℂI nat _) => (#|val cn| * (22 * #|val cm| + 35) + 6) >|).
  Proof. csize_using Nat_mul_complexity. Qed.

End NatComplexity.

(** The time cost model with the analyses of [nat]. *)
Module Type TimeNat := TimeCostModel.TimeCostModel <+ NatComplexity.
