(** * Polynomials

    Polynomials with natural coefficients in variables [pvar i], evaluated
    on the list of the values of the variables, [0] for those that are
    missing. They are the bounds of [Bounds] (in the sizes of the arguments
    of a function), and they are higher-order polynomials ([HOPoly]). *)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Inductive poly : Type :=
| pconst (k : nat)
| pvar (i : nat)
| padd (p q : poly)
| pmul (p q : poly)
| ppow (p : poly) (d : nat).

Fixpoint peval (p : poly) (ss : list nat) : nat :=
  match p with
  | pconst k => k
  | pvar i => nth i ss 0
  | padd p q => peval p ss + peval q ss
  | pmul p q => peval p ss * peval q ss
  | ppow p d => peval p ss ^ d
  end.

Fixpoint pdeg (p : poly) : nat :=
  match p with
  | pconst _ => 0
  | pvar _ => 1
  | padd p q => Nat.max (pdeg p) (pdeg q)
  | pmul p q => pdeg p + pdeg q
  | ppow p d => pdeg p * d
  end.

(** ** Degrees

    A polynomial of degree [0] is a constant, and one of degree at most
    [1] in one variable is bounded by a linear function of it. *)

Lemma peval_deg0 p ss ss' : pdeg p = 0 -> peval p ss = peval p ss'.
Proof.
  induction p as [k|i|p IHp q IHq|p IHp q IHq|p IHp d]; cbn; intro H.
  - reflexivity.
  - discriminate H.
  - rewrite IHp, IHq; [reflexivity | ..]; lia.
  - rewrite IHp, IHq; [reflexivity | ..]; lia.
  - destruct d as [|d]; [reflexivity|]. rewrite IHp; [reflexivity|]. nia.
Qed.

Lemma peval_deg1 p : pdeg p <= 1 -> exists k, forall x, peval p [x] <= k * (1 + x).
Proof.
  induction p as [k|i|p IHp q IHq|p IHp q IHq|p IHp d]; cbn; intro H.
  - exists k. intro x. nia.
  - exists 1. intro x. destruct i as [|[|i]]; cbn; lia.
  - destruct IHp as [a Ha]; [lia|]. destruct IHq as [b Hb]; [lia|].
    exists (a + b). intro x. specialize (Ha x). specialize (Hb x). nia.
  - assert (pdeg p = 0 \/ pdeg q = 0) as [Hp|Hq] by lia.
    + destruct IHq as [b Hb]; [lia|]. exists (peval p [0] * b). intro x.
      rewrite (peval_deg0 p [x] [0] Hp). rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono_l, Hb.
    + destruct IHp as [a Ha]; [lia|]. exists (a * peval q [0]). intro x.
      rewrite (peval_deg0 q [x] [0] Hq). specialize (Ha x). nia.
  - destruct d as [|[|d]].
    + exists 1. intro x. cbn. lia.
    + destruct IHp as [a Ha]; [lia|]. exists a. intro x. rewrite Nat.pow_1_r. apply Ha.
    + assert (Hp : pdeg p = 0) by nia.
      exists (peval p [0] ^ S (S d)). intro x. rewrite (peval_deg0 p [x] [0] Hp). nia.
Qed.

(** ** Sums of variables

    [psum_from i n]: the sum of the [n] variables from [i]. *)
Fixpoint psum_from (i n : nat) : poly :=
  match n with 0 => pconst 0 | S n => padd (pvar i) (psum_from (S i) n) end.

Lemma nth_skipn_hd i ss : nth i ss 0 = hd 0 (skipn i ss).
Proof. revert ss; induction i; intros [|x ss]; cbn; auto. Qed.

Lemma skipn_S_tl {A} i (ss : list A) : skipn (S i) ss = tl (skipn i ss).
Proof. revert ss; induction i as [|i IH]; intros [|x ss]; [reflexivity.. | exact (IH ss)]. Qed.

Lemma peval_psum_from i n ss : peval (psum_from i n) ss = list_sum (firstn n (skipn i ss)).
Proof.
  revert i; induction n as [|n IH]; intro i; cbn [psum_from peval]; [reflexivity|].
  rewrite IH, nth_skipn_hd, skipn_S_tl. destruct (skipn i ss) as [|y t]; cbn; [now rewrite firstn_nil | reflexivity].
Qed.
