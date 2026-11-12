(** * Complexity of functions over [Z] from the standard library

    These bounds were axiomatised in [TimeDatatypes] (trusted base); they are
    now proved from the case analyses of [TimeDatatypes], the generic fixpoint
    axiom of [TimeFix], and [PosComplexity], as in [NatComplexity], with
    the smallest constants for the shape of each bound. Sizes are bit sizes
    ([zsize], in [BitSize]). Addition and subtraction get two bounds: a
    quadratic one, from a direct analysis, and a linear one, from an
    amortised analysis (at the end of the file). *)

From Complexity Require Export PosComplexity.
From Complexity Require Import BitSize.
From Stdlib Require Import PArith ZArith.

(** ** Trailing zeros

    [Pos.pred_double] only recurses over the trailing zeros of its
    argument: they give the amortised analysis of [Z.pos_sub] below. *)

Fixpoint ptz (p : positive) : nat := match p with xO q => S (ptz q) | _ => 0 end.

Definition ztz (z : Z) : nat := match z with Z0 => 0 | Zpos p | Zneg p => ptz p end.

Lemma ptz_lt_size p : ptz p < Pos.size_nat p.
Proof. induction p; cbn; lia. Qed.

Lemma ztz_le_zsize z : ztz z <= zsize z.
Proof. destruct z; cbn; try pose proof (ptz_lt_size p); lia. Qed.

Lemma ptz_pred_double p : ptz (Pos.pred_double p) = 0.
Proof. destruct p; reflexivity. Qed.

Lemma ztz_double z : ztz (Z.double z) <= S (ztz z).
Proof. destruct z; cbn; lia. Qed.

Lemma ztz_succ_double z : ztz (Z.succ_double z) = 0.
Proof. destruct z; cbn; try apply ptz_pred_double; reflexivity. Qed.

Lemma ztz_pred_double z : ztz (Z.pred_double z) = 0.
Proof. destruct z; cbn; try apply ptz_pred_double; reflexivity. Qed.

Module ZComplexity (Import Time : TimePos).


  (** ** Sizes *)
  Lemma zsize_le_size (z : Z) : zsize z <= size z.
  Proof.
    destruct z as [|p|p]; cbn; [pose proof size_Z0 | pose proof (size_Zpos p) | pose proof (size_Zneg p)];
      try pose proof (size_nat_le_size p); lia.
  Qed.
  Global Instance Z_size_fact (z : Z) : SizeFact z (zsize z <= size z) := zsize_le_size z.

  (** ** Bounds *)

  (** Facts on the sizes of the goal. *)
  Ltac zfacts := rewrite ?zsize_opp in *; size_facts.

  (** ** Constant-time functions *)

  Global Instance Z_opp_complexity : Time.ComplexityBound Z.opp (fun cz => 5 ⋉ tt) := _.

  Global Instance Z_abs_complexity : Time.ComplexityBound Z.abs (fun cz => 5 ⋉ tt) := _.

  Global Instance Z_double_complexity : Time.ComplexityBound Z.double (fun cz => 7 ⋉ tt) := _.

  Global Instance Z_succ_double_complexity : Time.ComplexityBound Z.succ_double
    (fun cz => (12 * zsize (val cz) + 6) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_pred_double_complexity : Time.ComplexityBound Z.pred_double
    (fun cz => (12 * zsize (val cz) + 6) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Subtraction of positive numbers

      [Z.pos_sub] is recursive on its second argument. Each step may apply
      [Z.pred_double] or [Z.succ_double] to the result of the recursive call,
      at a cost linear in its size: the bound is quadratic. *)
  Global Instance Z_pos_sub_complexity : Time.ComplexityBound Z.pos_sub
    (fun cx => 4 ⋉ fun cy =>
       (Pos.size_nat (val cy) *
          (12 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)))) ⋉ tt).
  Proof. cbound. all: try pose proof (zsize_pos_sub cx cy); size_facts; nia. Qed.

  (** ** Arithmetic *)

  (** Additions of numbers of different signs use [Z.pos_sub]. *)
  Global Instance Z_add_complexity : Time.ComplexityBound Z.add
    (fun cx => 1 ⋉ fun cy =>
       (14 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy))) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_sub_complexity : Time.ComplexityBound Z.sub
    (fun cx => 1 ⋉ fun cy =>
       (14 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 12) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_mul_complexity : Time.ComplexityBound Z.mul
    (fun cx => 1 ⋉ fun cy =>
       (zsize (val cx) * (36 * (zsize (val cx) + zsize (val cy))) + 19) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  (** ** Comparisons *)

  Global Instance CompOpp_complexity : Time.ComplexityBound CompOpp
    (fun cc => 3 ⋉ tt) := _.

  Global Instance Z_compare_complexity : Time.ComplexityBound Z.compare
    (fun cx => 1 ⋉ fun cy => (40 * zsize (val cy) + 19) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_eqb_complexity : Time.ComplexityBound Z.eqb
    (fun cx => 1 ⋉ fun cy => (26 * zsize (val cx) + 17) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** The cost of the case analysis of the result of the comparison depends
      on its value. *)
  Global Instance Z_ltb_complexity : Time.ComplexityBound Z.ltb
    (fun cx => 1 ⋉ fun cy => (40 * zsize (val cy) + 27) ⋉ tt) := _.

  Global Instance Z_leb_complexity : Time.ComplexityBound Z.leb
    (fun cx => 1 ⋉ fun cy => (40 * zsize (val cy) + 27) ⋉ tt) := _.

  (** ** Conversions *)

  Global Instance Z_of_nat_complexity : Time.ComplexityBound Z.of_nat
    (fun cn => (val cn * (23 * zsize (Z.of_nat (val cn))) + 3) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_to_nat_complexity : Time.ComplexityBound Z.to_nat
    (fun cz => (22 * Z.to_nat (val cz) + 53 * zsize (val cz) + 1) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Linear bounds for addition and subtraction (amortised)

      The bounds of [pos_sub], [add] and [sub] above are quadratic: each
      step of [Z.pos_sub] applies [Z.succ_double] or [Z.pred_double] to the
      result of the recursive call, at a cost bounded by its size. The real
      cost is linear: these functions call [Pos.pred_double], which only
      walks over the trailing zeros of the result, and each of these zeros
      was produced by an earlier step ([Z.double]) and is consumed once.
      The bound of [Z.pos_sub] below is the classical potential argument:
      its cost plus [15] times the number of trailing zeros of its result is
      linear. These bounds are preferred by typeclass search (priority 0). *)

  Global Instance Pos_pred_double_tz_complexity : Time.ComplexityBound Pos.pred_double
    (fun cp => (12 * ptz (val cp) + 10) ⋉ tt) | 0 := _.

  Global Instance Z_succ_double_tz_complexity : Time.ComplexityBound Z.succ_double
    (fun cz => (12 * ztz (val cz) + 16) ⋉ tt) | 0 := _.

  Global Instance Z_pred_double_tz_complexity : Time.ComplexityBound Z.pred_double
    (fun cz => (12 * ztz (val cz) + 16) ⋉ tt) | 0 := _.

  Global Instance Z_pos_sub_linear_complexity : Time.ComplexityBound Z.pos_sub
    (fun cx => 4 ⋉ fun cy =>
       (25 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))
          - 15 * ztz (Z.pos_sub (val cx) (val cy))) ⋉ tt) | 0.
  Proof.
    cbound. all: try pose proof (zsize_pos_sub cx cy);
      try pose proof (ztz_le_zsize (Z.pos_sub cx cy));
      try pose proof (ztz_double (Z.pos_sub cx cy));
      rewrite ?ztz_succ_double, ?ztz_pred_double, ?ptz_pred_double;
      try pose proof (ptz_lt_size cx); try pose proof (ptz_lt_size cy); size_facts; lia.
  Qed.

  Global Instance Z_add_linear_complexity : Time.ComplexityBound Z.add
    (fun cx => 1 ⋉ fun cy =>
       (25 * (zsize (val cx) + zsize (val cy)) + 17) ⋉ tt) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_sub_linear_complexity : Time.ComplexityBound Z.sub
    (fun cx => 1 ⋉ fun cy =>
       (25 * (zsize (val cx) + zsize (val cy)) + 29) ⋉ tt) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Bounds in the size of the arguments

      From the linear bounds of [Z.pos_sub], [Z.add] and [Z.sub], and from
      the bounds of [Z.succ_double] and [Z.pred_double] in the size (not in
      the trailing zeros). [Z.to_nat] is exponential in the size of its
      argument: its result is a unary number. *)
  Global Instance Z_opp_linear_bound : Time.LinearBound Z.opp := _.
  Global Instance Z_abs_linear_bound : Time.LinearBound Z.abs := _.
  Global Instance Z_double_linear_bound : Time.LinearBound Z.double := _.
  Global Instance Z_succ_double_linear_bound : Time.LinearBound Z.succ_double :=
    ltac:(clinear_using Z_succ_double_complexity).
  Global Instance Z_pred_double_linear_bound : Time.LinearBound Z.pred_double :=
    ltac:(clinear_using Z_pred_double_complexity).
  Global Instance Z_pos_sub_linear_bound : Time.LinearBound Z.pos_sub := _.
  Global Instance Z_add_linear_bound : Time.LinearBound Z.add := _.
  Global Instance Z_sub_linear_bound : Time.LinearBound Z.sub := _.
  Global Instance Z_mul_polynomial_bound : Time.PolynomialBound Z.mul := _.
  Global Instance CompOpp_linear_bound : Time.LinearBound CompOpp := _.
  Global Instance Z_compare_linear_bound : Time.LinearBound Z.compare := _.
  Global Instance Z_eqb_linear_bound : Time.LinearBound Z.eqb := _.
  Global Instance Z_ltb_linear_bound : Time.LinearBound Z.ltb := _.
  Global Instance Z_leb_linear_bound : Time.LinearBound Z.leb := _.

  Global Instance Z_of_nat_polynomial_bound : Time.PolynomialBound Z.of_nat.
  Proof.
    cpolynomial.
    all: match goal with |- context [Z.of_nat ?n] => pose proof (zsize_of_nat n) end.
    all: nia.
  Qed.
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma Z_succ_double_size_complexity :
    Time.ComplexityBound Z.succ_double
      (fun (cz : ℂI Z _) => (12 * #|val cz| + 6) ⋉ tt).
  Proof. csize_using Z_succ_double_complexity. Qed.

  Lemma Z_pred_double_size_complexity :
    Time.ComplexityBound Z.pred_double
      (fun (cz : ℂI Z _) => (12 * #|val cz| + 6) ⋉ tt).
  Proof. csize_using Z_pred_double_complexity. Qed.

  Lemma Z_pos_sub_size_complexity :
    Time.ComplexityBound Z.pos_sub
      (fun (cx : ℂI positive _) => 4 ⋉ fun (cy : ℂI positive _) => (#|val cy| * (12 * (#|val cx| + #|val cy|))) ⋉ tt).
  Proof. csize_using Z_pos_sub_complexity. Qed.

  Lemma Z_add_size_complexity :
    Time.ComplexityBound Z.add
      (fun (cx : ℂI Z _) => 1 ⋉ fun (cy : ℂI Z _) => (14 * (#|val cx| + #|val cy|) * (#|val cx| + #|val cy|)) ⋉ tt).
  Proof. csize_using Z_add_complexity. Qed.

  Lemma Z_sub_size_complexity :
    Time.ComplexityBound Z.sub
      (fun (cx : ℂI Z _) => 1 ⋉ fun (cy : ℂI Z _) => (14 * (#|val cx| + #|val cy|) * (#|val cx| + #|val cy|) + 12) ⋉ tt).
  Proof. csize_using Z_sub_complexity. Qed.

  Lemma Z_mul_size_complexity :
    Time.ComplexityBound Z.mul
      (fun (cx : ℂI Z _) => 1 ⋉ fun (cy : ℂI Z _) => (#|val cx| * (36 * (#|val cx| + #|val cy|)) + 19) ⋉ tt).
  Proof. csize_using Z_mul_complexity. Qed.

  Lemma Z_compare_size_complexity :
    Time.ComplexityBound Z.compare
      (fun cx => 1 ⋉ fun (cy : ℂI Z _) => (40 * #|val cy| + 19) ⋉ tt).
  Proof. csize_using Z_compare_complexity. Qed.

  Lemma Z_eqb_size_complexity :
    Time.ComplexityBound Z.eqb
      (fun (cx : ℂI Z _) => 1 ⋉ fun cy => (26 * #|val cx| + 17) ⋉ tt).
  Proof. csize_using Z_eqb_complexity. Qed.

  Lemma Z_ltb_size_complexity :
    Time.ComplexityBound Z.ltb
      (fun cx => 1 ⋉ fun (cy : ℂI Z _) => (40 * #|val cy| + 27) ⋉ tt).
  Proof. csize_using Z_ltb_complexity. Qed.

  Lemma Z_leb_size_complexity :
    Time.ComplexityBound Z.leb
      (fun cx => 1 ⋉ fun (cy : ℂI Z _) => (40 * #|val cy| + 27) ⋉ tt).
  Proof. csize_using Z_leb_complexity. Qed.

  Lemma Z_add_linear_size_complexity :
    Time.ComplexityBound Z.add
      (fun (cx : ℂI Z _) => 1 ⋉ fun (cy : ℂI Z _) => (25 * (#|val cx| + #|val cy|) + 17) ⋉ tt).
  Proof. csize_using Z_add_linear_complexity. Qed.

  Lemma Z_sub_linear_size_complexity :
    Time.ComplexityBound Z.sub
      (fun (cx : ℂI Z _) => 1 ⋉ fun (cy : ℂI Z _) => (25 * (#|val cx| + #|val cy|) + 29) ⋉ tt).
  Proof. csize_using Z_sub_linear_complexity. Qed.

End ZComplexity.
