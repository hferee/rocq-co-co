(** * Bit sizes of binary numbers

    The costs of the functions over [positive] and [Z] are stated in terms of
    the bit sizes of their arguments ([PosComplexity], [ZComplexity]). The
    standard library only proves the monotonicity of [Pos.size_nat]
    ([Pos.size_nat_monotone]) and its characterisation by powers of [2]
    ([Zpower2_Psize]); the facts below follow from them, or by case
    analysis. *)

From Stdlib Require Import Arith PArith ZArith Zpow_facts Lia.

(** ** Positive numbers *)

Lemma size_nat_pos p : 1 <= Pos.size_nat p.
Proof. destruct p; cbn; lia. Qed.

Lemma size_nat_succ p : Pos.size_nat p <= Pos.size_nat (Pos.succ p).
Proof. apply Pos.size_nat_monotone, Pos.lt_succ_diag_r. Qed.

Lemma size_nat_pred_double p : Pos.size_nat (Pos.pred_double p) <= S (Pos.size_nat p).
Proof. induction p; cbn; lia. Qed.

Lemma size_nat_mul p q : Pos.size_nat (p * q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  apply Zpower2_Psize. rewrite Pos2Z.inj_mul, Nat2Z.inj_add, Z.pow_add_r by lia.
  apply Z.mul_lt_mono_nonneg; try lia; apply Zpower2_Psize; reflexivity.
Qed.

(** The bit size is at most the value: the sizes of conversions from [nat]. *)
Lemma size_nat_le_to_nat p : Pos.size_nat p <= Pos.to_nat p.
Proof. induction p; cbn [Pos.size_nat]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO; lia. Qed.

Lemma size_nat_of_succ_nat n : Pos.size_nat (Pos.of_succ_nat n) <= S n.
Proof. pose proof (size_nat_le_to_nat (Pos.of_succ_nat n)). rewrite SuccNat2Pos.id_succ in H. exact H. Qed.

Lemma size_nat_of_nat n : Pos.size_nat (Pos.of_nat n) <= S n.
Proof. pose proof (size_nat_le_to_nat (Pos.of_nat n)). rewrite Nat2Pos.id_max in H. lia. Qed.

(** Add [1 <= Pos.size_nat p] for the sizes [Pos.size_nat p] of the goal. *)
Ltac size_facts :=
  repeat match goal with
  | |- context [Pos.size_nat ?p] =>
      lazymatch goal with
      | _ : 1 <= Pos.size_nat p |- _ => fail
      | _ => pose proof (size_nat_pos p)
      end
  end.

(** ** Integers *)

Definition zsize (z : Z) : nat :=
  match z with Z0 => 1 | Zpos p | Zneg p => Pos.size_nat p end.

Lemma zsize_opp z : zsize (- z) = zsize z.
Proof. destruct z; reflexivity. Qed.

Lemma zsize_double z : zsize (Z.double z) <= S (zsize z).
Proof. destruct z; cbn; lia. Qed.

Lemma zsize_succ_double z : zsize (Z.succ_double z) <= S (zsize z).
Proof. destruct z; cbn; try apply size_nat_pred_double; lia. Qed.

Lemma zsize_pred_double z : zsize (Z.pred_double z) <= S (zsize z).
Proof. destruct z; cbn; try apply size_nat_pred_double; lia. Qed.

Lemma zsize_of_nat n : zsize (Z.of_nat n) <= S n.
Proof. destruct n; cbn; [lia | pose proof (size_nat_of_succ_nat n); lia]. Qed.

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
