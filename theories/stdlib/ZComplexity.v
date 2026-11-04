(** * Complexity of functions over [Z] from the standard library

    These bounds were axiomatised in [TimeDatatypes] (trusted base); they are
    now proved from the case analyses of [TimeDatatypes], the generic fixpoint
    axiom of [TimeFix], and [PosComplexity], as in [NatComplexity], with
    the smallest constants for the shape of each bound. Sizes are bit sizes
    ([zsize], in [BitSize]). Addition and subtraction get two bounds: a
    quadratic one, from a direct analysis, and a linear one, from an
    amortised analysis (at the end of the file). *)

From Complexity Require Import TimeCostModel CostModel TimeBasic TimeDatatypes Combinators
  Compile TimeCombinators TimeFix.
From Complexity Require Import NatComplexity PosComplexity BitSize.
From Stdlib Require Import Program.Basics Arith PArith ZArith Lia.

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

Module ZComplexity (Import M : TimePos).


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

  Global Instance Z_opp_complexity : ComplexityBound Z.opp (fun cz => 2 ⋉ tt) := ltac:(cbound).

  Global Instance Z_abs_complexity : ComplexityBound Z.abs (fun cz => 2 ⋉ tt) := ltac:(cbound).

  Global Instance Z_double_complexity : ComplexityBound Z.double (fun cz => 7 ⋉ tt) := ltac:(cbound).

  Global Instance Z_succ_double_complexity : ComplexityBound Z.succ_double
    (fun cz => (16 * zsize (val cz) + 6) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_pred_double_complexity : ComplexityBound Z.pred_double
    (fun cz => (16 * zsize (val cz) + 6) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Subtraction of positive numbers

      [Z.pos_sub] is recursive on its second argument. Each step may apply
      [Z.pred_double] or [Z.succ_double] to the result of the recursive call,
      at a cost linear in its size: the bound is quadratic. *)
  Global Instance Z_pos_sub_complexity : ComplexityBound Z.pos_sub
    (fun cx => 5 ⋉ fun cy =>
       (Pos.size_nat (val cy) *
          (16 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) + 7) ⋉ tt).
  Proof. cbound. all: try pose proof (zsize_pos_sub cx cy); size_facts; nia. Qed.

  (** ** Arithmetic *)

  (** Additions of numbers of different signs use [Z.pos_sub]. *)
  Global Instance Z_add_complexity : ComplexityBound Z.add
    (fun cx => 2 ⋉ fun cy =>
       (16 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 53) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_sub_complexity : ComplexityBound Z.sub
    (fun cx => 2 ⋉ fun cy =>
       (16 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 65) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_mul_complexity : ComplexityBound Z.mul
    (fun cx => 2 ⋉ fun cy =>
       (zsize (val cx) * (68 * (zsize (val cx) + zsize (val cy))) + 38) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  (** ** Comparisons *)

  Global Instance CompOpp_complexity : ComplexityBound CompOpp
    (fun cc => 2 ⋉ tt) := ltac:(cbound).

  Global Instance Z_compare_complexity : ComplexityBound Z.compare
    (fun cx => 2 ⋉ fun cy => (86 * zsize (val cy) + 36) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_eqb_complexity : ComplexityBound Z.eqb
    (fun cx => 2 ⋉ fun cy => (50 * zsize (val cx) + 38) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** The cost of the case analysis of the result of the comparison depends
      on its value. *)
  Global Instance Z_ltb_complexity : ComplexityBound Z.ltb
    (fun cx => 2 ⋉ fun cy => (86 * zsize (val cy) + 48) ⋉ tt) := ltac:(cbound).

  Global Instance Z_leb_complexity : ComplexityBound Z.leb
    (fun cx => 2 ⋉ fun cy => (86 * zsize (val cy) + 48) ⋉ tt) := ltac:(cbound).

  (** ** Conversions *)

  Global Instance Z_of_nat_complexity : ComplexityBound Z.of_nat
    (fun cn => (val cn * (31 * zsize (Z.of_nat (val cn))) + 2) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_to_nat_complexity : ComplexityBound Z.to_nat
    (fun cz => (36 * Z.to_nat (val cz) + 83 * zsize (val cz) + 1) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Linear bounds for addition and subtraction (amortised)

      The bounds of [pos_sub], [add] and [sub] above are quadratic: each
      step of [Z.pos_sub] applies [Z.succ_double] or [Z.pred_double] to the
      result of the recursive call, at a cost bounded by its size. The real
      cost is linear: these functions call [Pos.pred_double], which only
      walks over the trailing zeros of the result, and each of these zeros
      was produced by an earlier step ([Z.double]) and is consumed once.
      The bound of [Z.pos_sub] below is the classical potential argument:
      its cost plus [16] times the number of trailing zeros of its result is
      linear. These bounds are preferred by typeclass search (priority 0). *)

  Global Instance Pos_pred_double_tz_complexity : ComplexityBound Pos.pred_double
    (fun cp => (16 * ptz (val cp) + 14) ⋉ tt) | 0 := ltac:(cbound).

  Global Instance Z_succ_double_tz_complexity : ComplexityBound Z.succ_double
    (fun cz => (16 * ztz (val cz) + 20) ⋉ tt) | 0 := ltac:(cbound).

  Global Instance Z_pred_double_tz_complexity : ComplexityBound Z.pred_double
    (fun cz => (16 * ztz (val cz) + 20) ⋉ tt) | 0 := ltac:(cbound).

  Global Instance Z_pos_sub_linear_complexity : ComplexityBound Z.pos_sub
    (fun cx => 5 ⋉ fun cy =>
       (39 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))
          - 16 * ztz (Z.pos_sub (val cx) (val cy))) ⋉ tt) | 0.
  Proof.
    cbound. all: try pose proof (zsize_pos_sub cx cy);
      try pose proof (ztz_le_zsize (Z.pos_sub cx cy));
      try pose proof (ztz_double (Z.pos_sub cx cy));
      rewrite ?ztz_succ_double, ?ztz_pred_double, ?ptz_pred_double;
      try pose proof (ptz_lt_size cx); try pose proof (ptz_lt_size cy); size_facts; lia.
  Qed.

  Global Instance Z_add_linear_complexity : ComplexityBound Z.add
    (fun cx => 2 ⋉ fun cy =>
       (39 * (zsize (val cx) + zsize (val cy)) + 50) ⋉ tt) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_sub_linear_complexity : ComplexityBound Z.sub
    (fun cx => 2 ⋉ fun cy =>
       (39 * (zsize (val cx) + zsize (val cy)) + 62) ⋉ tt) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Bounds in the size of the arguments

      From the linear bounds of [Z.pos_sub], [Z.add] and [Z.sub], and from
      the bounds of [Z.succ_double] and [Z.pred_double] in the size (not in
      the trailing zeros). [Z.to_nat] is exponential in the size of its
      argument: its result is a unary number. *)
  Global Instance Z_opp_linear_bound : LinearBound Z.opp := _.
  Global Instance Z_abs_linear_bound : LinearBound Z.abs := _.
  Global Instance Z_double_linear_bound : LinearBound Z.double := _.
  Global Instance Z_succ_double_linear_bound : LinearBound Z.succ_double :=
    ltac:(clinear_using Z_succ_double_complexity).
  Global Instance Z_pred_double_linear_bound : LinearBound Z.pred_double :=
    ltac:(clinear_using Z_pred_double_complexity).
  Global Instance Z_pos_sub_linear_bound : LinearBound Z.pos_sub := _.
  Global Instance Z_add_linear_bound : LinearBound Z.add := _.
  Global Instance Z_sub_linear_bound : LinearBound Z.sub := _.
  Global Instance Z_mul_polynomial_bound : PolynomialBound Z.mul := _.
  Global Instance CompOpp_linear_bound : LinearBound CompOpp := _.
  Global Instance Z_compare_linear_bound : LinearBound Z.compare := _.
  Global Instance Z_eqb_linear_bound : LinearBound Z.eqb := _.
  Global Instance Z_ltb_linear_bound : LinearBound Z.ltb := _.
  Global Instance Z_leb_linear_bound : LinearBound Z.leb := _.

  Global Instance Z_of_nat_polynomial_bound : PolynomialBound Z.of_nat.
  Proof.
    cpolynomial.
    all: match goal with |- context [Z.of_nat ?n] => pose proof (zsize_of_nat n) end.
    all: nia.
  Qed.
End ZComplexity.
