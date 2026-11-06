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

Module NatComplexity (Import M : TimeCostModel).

  (** ** Sizes *)
  Lemma nat_lt_size (n : nat) : n < size n.
  Proof. induction n; [apply size_O | pose proof (size_S n); lia]. Qed.
  Global Instance nat_size_fact (n : nat) : SizeFact n (n < size n) := nat_lt_size n.

  (** ** Bounds *)

  Global Instance Nat_add_complexity : ComplexityBound Nat.add
    (fun cn => 5 ⋉ fun cm => (36 * val cn + 14) ⋉ tt) := _.

  (** [Nat.sub] is recursive on its first argument and matches on the second
      one. *)
  Global Instance Nat_sub_complexity : ComplexityBound Nat.sub
    (fun cn => 5 ⋉ fun cm => (56 * val cn + 16) ⋉ tt) := _.

  Global Instance Nat_eqb_complexity : ComplexityBound Nat.eqb
    (fun cn => 5 ⋉ fun cm => (37 * val cn + 14) ⋉ tt) := _.

  Global Instance Nat_leb_complexity : ComplexityBound Nat.leb
    (fun cn => 5 ⋉ fun cm => (39 * val cn + 10) ⋉ tt) := _.

  (** [Nat.ltb] is not recursive: its complexity follows from the one of
      [Nat.leb] by compilation alone. *)
  Global Instance Nat_ltb_complexity : ComplexityBound Nat.ltb
    (fun cn => 2 ⋉ fun cm => (39 * val cn + 63) ⋉ tt) := _.

  (** The recursive branch of [Nat.mul] calls [Nat.add]. *)
  Global Instance Nat_mul_complexity : ComplexityBound Nat.mul
    (fun cn => 5 ⋉ fun cm =>
       (val cn * (36 * val cm + 52) + 10) ⋉ tt) := _.

  (** [Nat.pow] is recursive on its second argument, and the step [m] calls
      [Nat.mul] on [n ^ m]: the sum of the [n ^ i] is bounded by
      [m * n ^ m]. *)
  Global Instance Nat_pow_complexity : ComplexityBound Nat.pow
    (fun cn => 7 ⋉ fun cm =>
       (36 * val cm * val cn ^ val cm + val cm * (52 * val cn + 40) + 2) ⋉ tt).
  Proof. cbound. destruct cn; [destruct cm; cbn; lia | nia]. Qed.

  (** ** Bounds in the size of the arguments

      [Nat.pow] is exponential in the size of its second argument. *)
  Global Instance Nat_add_linear_bound : LinearBound Nat.add := _.
  Global Instance Nat_sub_linear_bound : LinearBound Nat.sub := _.
  Global Instance Nat_eqb_linear_bound : LinearBound Nat.eqb := _.
  Global Instance Nat_leb_linear_bound : LinearBound Nat.leb := _.
  Global Instance Nat_ltb_linear_bound : LinearBound Nat.ltb := _.
  Global Instance Nat_mul_polynomial_bound : PolynomialBound Nat.mul := _.
End NatComplexity.

(** The time cost model with the analyses of [nat]. *)
Module Type TimeNat := TimeCostModel.TimeCostModel <+ NatComplexity.
