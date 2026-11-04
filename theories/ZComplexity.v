(** * Complexity of functions over [Z] from the standard library

    These bounds were axiomatised in [ZCostModel] (trusted base); they are
    now proved from the case analyses of [ZCostModel], the generic fixpoint
    axiom of [FixCostModel], and [PosComplexity], as in [NatComplexity], with
    the smallest constants for the shape of each bound. Sizes are bit sizes
    ([zsize], in [BitSize]). Addition and subtraction get two bounds: a
    quadratic one, from a direct analysis, and a linear one, from an
    amortised analysis (at the end of the file). *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel ZCostModel FixCostModel NatComplexity
  PosComplexity BitSize.
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

Module ZComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT)
  (Import ZM : ZTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT CB).

  Module PC := PosComplexity CM BT NT CB UN BO ZM FX.
  Import PC PC.NC.

  (** Facts on the sizes of the goal. *)
  Ltac zfacts := rewrite ?zsize_opp in *; size_facts.

  (** ** Constant-time functions *)

  Lemma opp_complexity : ComplexityBound Z.opp (fun cz : ℂI Z unit => 2 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance opp_complexity.

  Lemma abs_complexity : ComplexityBound Z.abs (fun cz : ℂI Z unit => 2 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance abs_complexity.

  Lemma double_complexity : ComplexityBound Z.double (fun cz : ℂI Z unit => 4 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance double_complexity.

  Lemma succ_double_complexity : ComplexityBound Z.succ_double
    (fun cz : ℂI Z unit => (9 * zsize (val cz) + 3) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance succ_double_complexity.

  Lemma pred_double_complexity : ComplexityBound Z.pred_double
    (fun cz : ℂI Z unit => (9 * zsize (val cz) + 3) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance pred_double_complexity.

  (** ** Subtraction of positive numbers

      [Z.pos_sub] is recursive on its second argument. Each step may apply
      [Z.pred_double] or [Z.succ_double] to the result of the recursive call,
      at a cost linear in its size: the bound is quadratic. *)
  Lemma pos_sub_complexity : ComplexityBound Z.pos_sub
    (fun cx : ℂI positive unit => 13 ⋉ fun cy : ℂI positive unit =>
       (Pos.size_nat (val cy) *
          (12 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))) + 1) ⋉ tt).
  Proof. cbound. all: try pose proof (zsize_pos_sub cx cy); size_facts; nia. Qed.
  Global Existing Instance pos_sub_complexity.

  (** ** Arithmetic *)

  (** Additions of numbers of different signs use [Z.pos_sub]. *)
  Lemma add_complexity : ComplexityBound Z.add
    (fun cx : ℂI Z unit => 37 ⋉ fun cy : ℂI Z unit =>
       (12 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 66) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.
  Global Existing Instance add_complexity.

  Lemma sub_complexity : ComplexityBound Z.sub
    (fun cx : ℂI Z unit => 7 ⋉ fun cy : ℂI Z unit =>
       (12 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 108) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.
  Global Existing Instance sub_complexity.

  Lemma mul_complexity : ComplexityBound Z.mul
    (fun cx : ℂI Z unit => 1 ⋉ fun cy : ℂI Z unit =>
       (zsize (val cx) * (64 * (zsize (val cx) + zsize (val cy))) + 51) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.
  Global Existing Instance mul_complexity.

  (** ** Comparisons *)

  Lemma CompOpp_complexity : ComplexityBound CompOpp
    (fun cc : ℂI comparison unit => 2 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance CompOpp_complexity.

  Lemma compare_complexity : ComplexityBound Z.compare
    (fun cx : ℂI Z unit => 1 ⋉ fun cy : ℂI Z unit => (101 * zsize (val cy) + 48) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance compare_complexity.

  Lemma eqb_complexity : ComplexityBound Z.eqb
    (fun cx : ℂI Z unit => 1 ⋉ fun cy : ℂI Z unit => (60 * zsize (val cx) + 43) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance eqb_complexity.

  (** The cost of the case analysis of the result of the comparison depends
      on its value. *)
  Lemma ltb_complexity : ComplexityBound Z.ltb
    (fun cx : ℂI Z unit => 9 ⋉ fun cy : ℂI Z unit => (101 * zsize (val cy) + 56) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance ltb_complexity.

  Lemma leb_complexity : ComplexityBound Z.leb
    (fun cx : ℂI Z unit => 9 ⋉ fun cy : ℂI Z unit => (101 * zsize (val cy) + 56) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance leb_complexity.

  (** ** Conversions *)

  Lemma of_nat_complexity : ComplexityBound Z.of_nat
    (fun cn : ℂI nat unit => (val cn * (17 * zsize (Z.of_nat (val cn))) + 2) ⋉ tt).
  Proof. cbound. all: zfacts; nia. Qed.
  Global Existing Instance of_nat_complexity.

  Lemma to_nat_complexity : ComplexityBound Z.to_nat
    (fun cz : ℂI Z unit => (55 * Z.to_nat (val cz) + 138 * zsize (val cz) + 1) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance to_nat_complexity.

  (** ** Linear bounds for addition and subtraction (amortised)

      The bounds of [pos_sub], [add] and [sub] above are quadratic: each
      step of [Z.pos_sub] applies [Z.succ_double] or [Z.pred_double] to the
      result of the recursive call, at a cost bounded by its size. The real
      cost is linear: these functions call [Pos.pred_double], which only
      walks over the trailing zeros of the result, and each of these zeros
      was produced by an earlier step ([Z.double]) and is consumed once.
      The bound of [Z.pos_sub] below is the classical potential argument:
      its cost plus [9] times the number of trailing zeros of its result is
      linear. These bounds are preferred by typeclass search (priority 0). *)

  Lemma pred_double_tz_complexity : ComplexityBound Pos.pred_double
    (fun cp : ℂI positive unit => (9 * ptz (val cp) + 10) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance pred_double_tz_complexity | 0.

  Lemma succ_double_tz_complexity : ComplexityBound Z.succ_double
    (fun cz : ℂI Z unit => (9 * ztz (val cz) + 13) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance succ_double_tz_complexity | 0.

  Lemma pred_double_z_tz_complexity : ComplexityBound Z.pred_double
    (fun cz : ℂI Z unit => (9 * ztz (val cz) + 13) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance pred_double_z_tz_complexity | 0.

  Lemma pos_sub_linear_complexity : ComplexityBound Z.pos_sub
    (fun cx : ℂI positive unit => 13 ⋉ fun cy : ℂI positive unit =>
       (30 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))
          - 9 * ztz (Z.pos_sub (val cx) (val cy))) ⋉ tt).
  Proof.
    cbound. all: try pose proof (zsize_pos_sub cx cy);
      try pose proof (ztz_le_zsize (Z.pos_sub cx cy));
      try pose proof (ztz_double (Z.pos_sub cx cy));
      rewrite ?ztz_succ_double, ?ztz_pred_double, ?ptz_pred_double;
      try pose proof (ptz_lt_size cx); try pose proof (ptz_lt_size cy); size_facts; lia.
  Qed.
  Global Existing Instance pos_sub_linear_complexity | 0.

  Lemma add_linear_complexity : ComplexityBound Z.add
    (fun cx : ℂI Z unit => 37 ⋉ fun cy : ℂI Z unit =>
       (32 * (zsize (val cx) + zsize (val cy)) + 50) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance add_linear_complexity | 0.

  Lemma sub_linear_complexity : ComplexityBound Z.sub
    (fun cx : ℂI Z unit => 7 ⋉ fun cy : ℂI Z unit =>
       (32 * (zsize (val cx) + zsize (val cy)) + 92) ⋉ tt).
  Proof. cbound. all: zfacts; lia. Qed.
  Global Existing Instance sub_linear_complexity | 0.
End ZComplexity.
