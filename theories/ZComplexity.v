(** * Complexity of functions over [Z] from the standard library

    These bounds were axiomatised in [ZCostModel] (trusted base); they are
    now proved from the case analyses of [ZCostModel], the generic fixpoint
    axiom of [FixCostModel], and [PosComplexity], as in [NatComplexity], with
    the smallest constants for the shape of each bound. Sizes are bit sizes
    ([zsize]). *)

From Complexity Require Import CostModel HOCostModel NatCostModel Combinators Compile
  CombinatorCostModel UnitCostModel BoolCostModel ZCostModel FixCostModel NatComplexity
  PosComplexity.
From Stdlib Require Import Program.Basics Arith PArith ZArith Lia.

(** ** Bit sizes *)

Definition zsize (z : Z) : nat :=
  match z with Z0 => 1 | Zpos p | Zneg p => Pos.size_nat p end.

Lemma size_nat_pred_double p : Pos.size_nat (Pos.pred_double p) <= S (Pos.size_nat p).
Proof. induction p; cbn; lia. Qed.

Lemma zsize_double z : zsize (Z.double z) <= S (zsize z).
Proof. destruct z; cbn; lia. Qed.

Lemma zsize_succ_double z : zsize (Z.succ_double z) <= S (zsize z).
Proof. destruct z; cbn; try apply size_nat_pred_double; lia. Qed.

Lemma zsize_pred_double z : zsize (Z.pred_double z) <= S (zsize z).
Proof. destruct z; cbn; try apply size_nat_pred_double; lia. Qed.

Lemma zsize_pos_sub x y : zsize (Z.pos_sub x y) <= Pos.size_nat x + Pos.size_nat y.
Proof.
  revert x; induction y as [y IH | y IH |]; intros [x | x |]; cbn [Z.pos_sub];
    try specialize (IH x);
    try pose proof (size_nat_pred_double x); try pose proof (size_nat_pred_double y);
    try pose proof (zsize_double (Z.pos_sub x y));
    try pose proof (zsize_succ_double (Z.pos_sub x y));
    try pose proof (zsize_pred_double (Z.pos_sub x y));
    cbn [zsize Pos.size_nat] in *; lia.
Qed.

Module ZComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT)
  (Import ZM : ZTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT).

  Module PC := PosComplexity CM BT NT CB UN BO ZM FX.
  Import PC PC.NC.

  (** ** Constant-time functions *)

  Lemma opp_complexity : ComplexityBound Z.opp (fun cz : ℂI Z unit => 2 ⋉ tt).
  Proof.
    capply. unfold Z.opp. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz; cbn; lia.
  Qed.
  Global Existing Instance opp_complexity.

  Lemma abs_complexity : ComplexityBound Z.abs (fun cz : ℂI Z unit => 2 ⋉ tt).
  Proof.
    capply. unfold Z.abs. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz; cbn; lia.
  Qed.
  Global Existing Instance abs_complexity.

  Lemma double_complexity : ComplexityBound Z.double (fun cz : ℂI Z unit => 3 ⋉ tt).
  Proof.
    capply. unfold Z.double. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz; cbn; lia.
  Qed.
  Global Existing Instance double_complexity.

  Lemma succ_double_complexity : ComplexityBound Z.succ_double
    (fun cz : ℂI Z unit => (4 * zsize (ival cz) + 2) ⋉ tt).
  Proof.
    capply. unfold Z.succ_double. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz as [|p|p];
      cbn -[Nat.mul]; unfold_comb; try pose proof (size_nat_pos p); lia.
  Qed.
  Global Existing Instance succ_double_complexity.

  Lemma pred_double_complexity : ComplexityBound Z.pred_double
    (fun cz : ℂI Z unit => (4 * zsize (ival cz) + 2) ⋉ tt).
  Proof.
    capply. unfold Z.pred_double. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz as [|p|p];
      cbn -[Nat.mul]; unfold_comb; try pose proof (size_nat_pos p); lia.
  Qed.
  Global Existing Instance pred_double_complexity.

  (** ** Subtraction of positive numbers

      [Z.pos_sub] is recursive on its second argument. Each step may apply
      [Z.pred_double] or [Z.succ_double] to the result of the recursive call,
      at a cost linear in its size: the bound is quadratic. *)
  Lemma pos_sub_complexity : ComplexityBound Z.pos_sub
    (fun cx : ℂI positive unit => 2 ⋉ fun cy : ℂI positive unit =>
       (Pos.size_nat (ival cy) *
          (4 * (Pos.size_nat (ival cx) + Pos.size_nat (ival cy)))) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cx; bo_split; destr_inputs; [cbn; lia |].
    destruct cx, cy; cbn -[Nat.mul zsize]; unfold_comb;
      try pose proof (size_nat_pos cx); try pose proof (size_nat_pos cy);
      try pose proof (zsize_pos_sub cx cy); nia.
  Qed.
  Global Existing Instance pos_sub_complexity.

  (** ** Arithmetic *)

  (** Additions of numbers of different signs use [Z.pos_sub]. *)
  Lemma add_complexity : ComplexityBound Z.add
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit =>
       (4 * (zsize (ival cx) + zsize (ival cy)) * (zsize (ival cx) + zsize (ival cy)) + 2) ⋉ tt).
  Proof.
    capply. unfold Z.add. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul]; unfold_comb;
      try pose proof (size_nat_pos p); try pose proof (size_nat_pos q); nia.
  Qed.
  Global Existing Instance add_complexity.

  Lemma sub_complexity : ComplexityBound Z.sub
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit =>
       (4 * (zsize (ival cx) + zsize (ival cy)) * (zsize (ival cx) + zsize (ival cy)) + 5) ⋉ tt).
  Proof.
    capply. unfold Z.sub. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul]; unfold_comb;
      try pose proof (size_nat_pos p); try pose proof (size_nat_pos q); nia.
  Qed.
  Global Existing Instance sub_complexity.

  Lemma mul_complexity : ComplexityBound Z.mul
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit =>
       (zsize (ival cx) * (8 * (zsize (ival cx) + zsize (ival cy))) + 8) ⋉ tt).
  Proof.
    capply. unfold Z.mul. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul]; unfold_comb;
      try pose proof (size_nat_pos p); try pose proof (size_nat_pos q); nia.
  Qed.
  Global Existing Instance mul_complexity.

  (** ** Comparisons *)

  Lemma CompOpp_complexity : ComplexityBound CompOpp
    (fun cc : ℂI comparison unit => 1 ⋉ tt).
  Proof.
    capply. unfold CompOpp. cbc.
    Unshelve. bo_split; destr_inputs; destruct cc; cbn; lia.
  Qed.
  Global Existing Instance CompOpp_complexity.

  Lemma compare_complexity : ComplexityBound Z.compare
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit => (6 * zsize (ival cy) + 7) ⋉ tt).
  Proof.
    capply. unfold Z.compare. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul]; unfold_comb; lia.
  Qed.
  Global Existing Instance compare_complexity.

  Lemma eqb_complexity : ComplexityBound Z.eqb
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit => (5 * zsize (ival cx) + 7) ⋉ tt).
  Proof.
    capply. unfold Z.eqb. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul]; unfold_comb; lia.
  Qed.
  Global Existing Instance eqb_complexity.

  (** The cost of the case analysis of the result of the comparison depends
      on its value. *)
  Lemma ltb_complexity : ComplexityBound Z.ltb
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit => (6 * zsize (ival cy) + 9) ⋉ tt).
  Proof.
    capply. unfold Z.ltb. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul zsize]; unfold_comb;
      try destruct (p ?= q)%positive; cbn -[Nat.mul zsize]; lia.
  Qed.
  Global Existing Instance ltb_complexity.

  Lemma leb_complexity : ComplexityBound Z.leb
    (fun cx : ℂI Z unit => 0 ⋉ fun cy : ℂI Z unit => (6 * zsize (ival cy) + 9) ⋉ tt).
  Proof.
    capply. unfold Z.leb. cbc.
    Unshelve. bo_split; destr_inputs; [cbn; lia |].
    destruct cx as [|p|p], cy as [|q|q]; cbn -[Nat.mul zsize]; unfold_comb;
      try destruct (p ?= q)%positive; cbn -[Nat.mul zsize]; lia.
  Qed.
  Global Existing Instance leb_complexity.

  (** ** Conversions *)

  Lemma of_nat_complexity : ComplexityBound Z.of_nat
    (fun cn : ℂI nat unit => (ival cn * (7 * zsize (Z.of_nat (ival cn))) + 1) ⋉ tt).
  Proof.
    capply. unfold Z.of_nat. cbc.
    Unshelve. bo_split; destr_inputs; destruct cn; cbn -[Nat.mul Pos.size_nat]; [lia |].
    pose proof (size_nat_pos (Pos.of_succ_nat cn)). nia.
  Qed.
  Global Existing Instance of_nat_complexity.

  Lemma to_nat_complexity : ComplexityBound Z.to_nat
    (fun cz : ℂI Z unit => (5 * Z.to_nat (ival cz) + 14 * zsize (ival cz) + 1) ⋉ tt).
  Proof.
    capply. unfold Z.to_nat. cbc.
    Unshelve. bo_split; destr_inputs; destruct cz as [|p|p];
      cbn -[Nat.mul Pos.size_nat Pos.to_nat]; unfold_comb; unfold Pos.to_nat in *;
      try pose proof (size_nat_pos p); lia.
  Qed.
  Global Existing Instance to_nat_complexity.
End ZComplexity.
