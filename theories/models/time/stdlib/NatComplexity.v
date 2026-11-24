(** * Functions on [nat]

    Each function is analysed as defined in the standard library, by
    [cbound], with the smallest constants. *)

From Complexity Require Export TimeCostModel BoolComplexity PairComplexity.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

(** The model with the booleans ([Nat.odd] is [negb (Nat.even n)]) and the
    projections of pairs ([Nat.div] and [Nat.modulo] project
    [Nat.divmod]). *)
Module Type TimeBoolPair := TimeCostModel.TimeCostModel <+ BoolComplexity <+ PairComplexity.

Module NatComplexity (Import Time : TimeBoolPair).

  (** ** Sizes *)
  Lemma nat_lt_size (n : nat) : n < size n.
  Proof. induction n; [rewrite size_O | rewrite size_S]; lia. Qed.
  Global Instance nat_size_fact (n : nat) : SizeFact n (n < size n) := nat_lt_size n.

  (** ** Bounds

      The first cost of a bound is that of the partial application to the
      first argument. *)

  Global Instance Nat_add_complexity : Time.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (12 * val cn + 9) >|) := _.

  (** [Nat.sub] is recursive on its first argument and matches on the second
      one. *)
  Global Instance Nat_sub_complexity : Time.ComplexityBound Nat.sub
    (fun cn => 4 +> fun cm => (21 * val cn + 6) >|) := _.

  Global Instance Nat_eqb_complexity : Time.ComplexityBound Nat.eqb
    (fun cn => 4 +> fun cm => (21 * val cn + 7) >|) := _.

  Global Instance Nat_leb_complexity : Time.ComplexityBound Nat.leb
    (fun cn => 4 +> fun cm => (21 * val cn + 5) >|) := _.

  (** [Nat.ltb] is not recursive: its complexity follows from the one of
      [Nat.leb] by compilation alone. *)
  Global Instance Nat_ltb_complexity : Time.ComplexityBound Nat.ltb
    (fun cn => 1 +> fun cm => (21 * val cn + 36) >|) := _.

  (** The recursive branch of [Nat.mul] calls [Nat.add]. *)
  Global Instance Nat_mul_complexity : Time.ComplexityBound Nat.mul
    (fun cn => 1 +> fun cm =>
       (val cn * (12 * val cm + 24) + 10) >|) := _.

  (** [Nat.pow] is recursive on its second argument, and the step [m] calls
      [Nat.mul] on [n ^ m]: the sum of the [n ^ i] is bounded by
      [m * n ^ m]. *)
  Global Instance Nat_pow_complexity : Time.ComplexityBound Nat.pow
    (fun cn => 1 +> fun cm =>
       (12 * val cm * val cn ^ val cm + val cm * (24 * val cn + 25) + 8) >|).
  Proof. cbound. destruct cn; [destruct cm; cbn; lia | nia]. Qed.

  Global Instance Nat_pred_complexity : Time.ComplexityBound Nat.pred (fun cn => 3 >|) := _.

  (** [Nat.max] and [Nat.min] recurse on both arguments and stop at the
      smaller one: a bound in the first one is enough. *)
  Global Instance Nat_max_complexity : Time.ComplexityBound Nat.max
    (fun cn => 4 +> fun cm => (23 * val cn + 5) >|) := _.
  Global Instance Nat_min_complexity : Time.ComplexityBound Nat.min
    (fun cn => 4 +> fun cm => (23 * val cn + 5) >|) := _.

  (** [Nat.div2] and [Nat.even] go down by two; [Nat.odd] is [negb
      (Nat.even n)]. *)
  Global Instance Nat_div2_complexity : Time.ComplexityBound Nat.div2
    (fun cn => (8 * val cn + 6) >|) := _.
  Global Instance Nat_even_complexity : Time.ComplexityBound Nat.even
    (fun cn => (7 * val cn + 6) >|) := _.
  Global Instance Nat_odd_complexity : Time.ComplexityBound Nat.odd
    (fun cn => (7 * val cn + 12) >|) := _.

  (** [Nat.log2], [Nat.sqrt] and [Nat.div] are loops ([log2_iter],
      [sqrt_iter], [divmod]) on their first argument. *)
  Global Instance Nat_log2_iter_complexity : Time.ComplexityBound Nat.log2_iter
    (fun ck => 4 +> fun cp => 2 +> fun cq => 2 +> fun cr => (42 * val ck + 9) >|) := _.
  Global Instance Nat_log2_complexity : Time.ComplexityBound Nat.log2
    (fun cn => (42 * val cn + 26) >|).
  Proof. cbound. Qed.
  Global Instance Nat_sqrt_iter_complexity : Time.ComplexityBound Nat.sqrt_iter
    (fun ck => 4 +> fun cp => 2 +> fun cq => 2 +> fun cr => (48 * val ck + 9) >|) := _.
  Global Instance Nat_sqrt_complexity : Time.ComplexityBound Nat.sqrt
    (fun cn => (48 * val cn + 22) >|) := _.
  Global Instance Nat_divmod_complexity : Time.ComplexityBound Nat.divmod
    (fun cx => 4 +> fun cy => 2 +> fun cq => 2 +> fun cu => (41 * val cx + 13) >|) := _.
  Global Instance Nat_div_complexity : Time.ComplexityBound Nat.div
    (fun cx => 1 +> fun cy => (41 * val cx + 37) >|) := _.
  (** [Nat.modulo] subtracts the remainder from the divisor. *)
  Global Instance Nat_modulo_complexity : Time.ComplexityBound Nat.modulo
    (fun cx => 1 +> fun cy => (41 * val cx + 21 * val cy + 27) >|) := _.

  (** [Nat.testbit a n] halves [a] [n] times ([Nat.div2 a <= a]). *)
  Global Instance Nat_testbit_complexity : Time.ComplexityBound Nat.testbit
    (fun ca => 4 +> fun cn => (val cn * (8 * val ca + 24) + 7 * val ca + 19) >|).
  Proof. cbound. pose proof (Nat.div2_decr ca ca ltac:(lia)). nia. Qed.

  (** ** Bounds in the sizes

      [Nat.pow] is exponential in the size of its second argument. *)
  Global Instance Nat_add_linear_bound : Time.LinearBound Nat.add := _.
  Global Instance Nat_sub_linear_bound : Time.LinearBound Nat.sub := _.
  Global Instance Nat_eqb_linear_bound : Time.LinearBound Nat.eqb := _.
  Global Instance Nat_leb_linear_bound : Time.LinearBound Nat.leb := _.
  Global Instance Nat_ltb_linear_bound : Time.LinearBound Nat.ltb := _.
  Global Instance Nat_mul_polynomial_bound : Time.PolynomialBound Nat.mul := _.
  Global Instance Nat_pred_constant_bound : Time.ConstantBound Nat.pred := _.
  Global Instance Nat_max_linear_bound : Time.LinearBound Nat.max := _.
  Global Instance Nat_min_linear_bound : Time.LinearBound Nat.min := _.
  Global Instance Nat_div2_linear_bound : Time.LinearBound Nat.div2 := _.
  Global Instance Nat_even_linear_bound : Time.LinearBound Nat.even := _.
  Global Instance Nat_odd_linear_bound : Time.LinearBound Nat.odd := _.
  Global Instance Nat_log2_linear_bound : Time.LinearBound Nat.log2 := _.
  Global Instance Nat_sqrt_linear_bound : Time.LinearBound Nat.sqrt := _.
  Global Instance Nat_div_linear_bound : Time.LinearBound Nat.div := _.
  Global Instance Nat_modulo_linear_bound : Time.LinearBound Nat.modulo := _.
  Global Instance Nat_testbit_polynomial_bound : Time.PolynomialBound Nat.testbit := _.

  (** ** Bounds in the sizes, with their constants

      From the bounds above: a value is at most its size ([SizeFact]). *)

  Lemma Nat_add_size_complexity :
    Time.ComplexityBound Nat.add
      (fun (cn : ℂI nat _) => 1 +> fun cm => (12 * #|val cn| + 0) >|).
  Proof. csize_using Nat_add_complexity. Qed.

  Lemma Nat_sub_size_complexity :
    Time.ComplexityBound Nat.sub
      (fun (cn : ℂI nat _) => 4 +> fun cm => (21 * #|val cn| + 0) >|).
  Proof. csize_using Nat_sub_complexity. Qed.

  Lemma Nat_eqb_size_complexity :
    Time.ComplexityBound Nat.eqb
      (fun (cn : ℂI nat _) => 4 +> fun cm => (21 * #|val cn| + 0) >|).
  Proof. csize_using Nat_eqb_complexity. Qed.

  Lemma Nat_leb_size_complexity :
    Time.ComplexityBound Nat.leb
      (fun (cn : ℂI nat _) => 4 +> fun cm => (21 * #|val cn| + 0) >|).
  Proof. csize_using Nat_leb_complexity. Qed.

  Lemma Nat_ltb_size_complexity :
    Time.ComplexityBound Nat.ltb
      (fun (cn : ℂI nat _) => 1 +> fun cm => (21 * #|val cn| + 15) >|).
  Proof. csize_using Nat_ltb_complexity. Qed.

  Lemma Nat_mul_size_complexity :
    Time.ComplexityBound Nat.mul
      (fun (cn : ℂI nat _) => 1 +> fun (cm : ℂI nat _) =>
         (#|val cn| * (12 * #|val cm| + 12) + 0) >|).
  Proof. csize_using Nat_mul_complexity. Qed.

End NatComplexity.

(** The model with the analyses of [nat]. *)
Module Type TimeNat := TimeBoolPair <+ NatComplexity.
