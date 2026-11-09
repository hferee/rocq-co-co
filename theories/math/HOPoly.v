(** * Higher-order polynomials

    The higher-order polynomials are the closed simply typed λ-terms over
    the numerals, addition and multiplication. They denote functionals over
    the natural numbers. At type [N ⇒ .. ⇒ N],
    they contain the usual polynomials ; at type 2,
    the second-order polynomials of Kapron and Cook ([SOPoly]). They are
    monotone, in the sense of Bezem's strong majorization
    ([hpoly_monotone]). At type [N ⇒ N] they are bounded by polynomials
    ([hpoly_growth]), and at type [(N ⇒ N) ⇒ N ⇒ N] they are exactly the
    second-order polynomials ([SOPoly]). They bound the basic feasible
    functionals ([BFF], [BFFFeasibility]).

    References: 
    B. M. Kapron, S. A. Cook. A new characterization of type-2 feasibility.
    SIAM Journal on Computing 25(1):117-132, 1996.

    M. Bezem. Strongly majorizable functionals of finite type: a model for
    bar recursion containing discontinuous functionals. *)

From Complexity Require Export Lambda.
From Complexity Require Import Poly.
From Stdlib Require Import Arith Lia List Program.Basics.
Import ListNotations.

(** ** Higher-order polynomials *)

Inductive hpc : ty -> Type :=
| hnum (n : nat) : hpc tN
| hadd : hpc (tN ⇒ tN ⇒ tN)
| hmul : hpc (tN ⇒ tN ⇒ tN).

Abbreviation M := (sem nat).

#[global] Instance hp_interp : Interp hpc nat :=
  fun σ c => match c in hpc σ return M σ with hnum n => n | hadd => Nat.add | hmul => Nat.mul end.

#[global] Instance hp_num : PNum hpc nat := fun V n => PCst (hnum n).
Notation "x + y" := (PApp (PApp (PCst hadd) x) y) (in custom lam at level 50, left associativity).
Notation "x * y" := (PApp (PApp (PCst hmul) x) y) (in custom lam at level 40, left associativity).

Definition hpoly (σ : ty) : Type := term hpc [] σ.

(** For example, [λ f x, f (f x + 1)]. *)
Example hp_example : hpoly ((tN ⇒ tN) ⇒ tN ⇒ tN) := db <{ λ f x, f (f x + 1) }>.

Example hp_example_eval : ⟦hp_example⟧ = fun f x => f (f x + 1).
Proof. reflexivity. Qed.

Ltac simpl_hp := simpl_interp hp_interp.

(** ** Strong majorization

    [mle σ x y]: [y] majorizes [x], pointwise and hereditarily, on
    arguments related in the same way. A functional is monotone when it
    majorizes itself. *)
Fixpoint mle (σ : ty) : M σ -> M σ -> Prop :=
  match σ with
  | tN => le
  | σ ⇒ τ => fun f g => forall x y, mle σ x y -> mle τ (f x) (g y)
  end.

Definition monotone (σ : ty) (x : M σ) : Prop := mle σ x x.

Lemma mle_cst σ (c : hpc σ) : monotone σ (cinterp σ c).
Proof. destruct c; cbn; [lia | intros ? ? ? ? ? ?; lia | intros ? ? ? ? ? ?; nia]. Qed.

Lemma mle_interp Γ σ (p : term hpc Γ σ) e e' :
  rel_env mle Γ e e' -> mle σ (interp p e) (interp p e').
Proof. apply rel_interp; [intros ? ? ? ? H; exact H | intros ? ? ? ? ? ? H; apply H | apply mle_cst]. Qed.

(** Higher-order polynomials are monotone (Bezem). *)
Theorem hpoly_monotone σ (p : hpoly σ) : monotone σ ⟦p⟧.
Proof. apply mle_interp. exact I. Qed.

Lemma mle_wk Γ σ (p : hpoly σ) (e : envT nat Γ) : mle σ ⟦p⟧ (interp (wk p) e).
Proof. apply rel_wk; [intros ? ? ? ? H; exact H | intros ? ? ? ? ? ? H; apply H | apply mle_cst]. Qed.

(** ** Constructions

    The constant [0] at any type, the value at [0]s, and the addition of a
    number at every argument, as functionals and as terms (in any
    context). *)
Fixpoint botM (σ : ty) : M σ := match σ with tN => 0 | σ ⇒ τ => fun _ => botM τ end.

Fixpoint baseM (σ : ty) : M σ -> nat :=
  match σ with tN => fun n => n | σ ⇒ τ => fun f => baseM τ (f (botM σ)) end.

Lemma mle_bot σ : monotone σ (botM σ).
Proof. induction σ as [|σ _ τ IH]; cbn; [lia | intros; apply IH]. Qed.

Lemma baseM_mono σ x y : mle σ x y -> baseM σ x <= baseM σ y.
Proof.
  revert x y; induction σ as [|σ _ τ IH]; intros x y H; [exact H|].
  apply IH, H, mle_bot.
Qed.

Fixpoint bot_t (σ : ty) {Γ} : term hpc Γ σ :=
  match σ with tN => tcst (hnum 0) | σ ⇒ τ => tlam (bot_t τ) end.

Fixpoint base_t (σ : ty) {Γ} : term hpc Γ (σ ⇒ tN) :=
  match σ with
  | tN => tlam (tvar vz)
  | σ ⇒ τ => tlam (tapp (base_t τ) (tapp (tvar vz) (bot_t σ)))
  end.

Fixpoint plus_t (σ : ty) {Γ} : term hpc Γ (tN ⇒ σ ⇒ σ) :=
  match σ with
  | tN => tcst hadd
  | σ ⇒ τ =>
      tlam (tlam (tlam (tapp (tapp (plus_t τ) (tvar (vs (vs vz)))) (tapp (tvar (vs vz)) (tvar vz)))))
  end.

Lemma interp_plus_tN Γ (e : envT nat Γ) k m : interp (plus_t tN) e k m = k + m.
Proof. reflexivity. Qed.

Lemma interp_plus_arr σ τ Γ (e : envT nat Γ) k m a :
  interp (plus_t (σ ⇒ τ)) e k m a =
  interp (plus_t τ (Γ := σ :: (σ ⇒ τ) :: tN :: Γ)) (ECons (ECons (ECons e k) m) a) k (m a).
Proof. reflexivity. Qed.

Lemma mle_bot_t σ Γ Γ' (e : envT nat Γ) (e' : envT nat Γ') :
  mle σ (interp (bot_t σ) e) (interp (bot_t σ) e').
Proof. revert Γ Γ' e e'; induction σ as [|σ _ τ IH]; intros; [apply le_n | intros ? ? _; apply IH]. Qed.

Lemma mle_bot_t_botM σ Γ (e : envT nat Γ) :
  mle σ (interp (bot_t σ) e) (botM σ) /\ mle σ (botM σ) (interp (bot_t σ) e).
Proof.
  revert Γ e; induction σ as [|σ _ τ IH]; intros Γ e; [split; apply le_n|].
  split; intros ? ? _; apply IH.
Qed.

Lemma base_t_baseM σ Γ (e : envT nat Γ) m : monotone σ m -> interp (base_t σ) e m = baseM σ m.
Proof.
  revert Γ e m; induction σ as [|σ _ τ IH]; intros Γ e m Hm; [reflexivity|].
  set (e' := ECons e m : envT nat ((σ ⇒ τ) :: Γ)). set (b := interp (bot_t σ) e').
  change (interp (base_t τ) e' (m b) = baseM τ (m (botM σ))).
  destruct (mle_bot_t_botM σ _ e') as [H1 H2].
  rewrite IH by exact (Hm _ _ (mle_bot_t σ _ _ _ _)).
  apply Nat.le_antisymm; apply baseM_mono, Hm; assumption.
Qed.

Lemma baseM_plus_t σ Γ (e : envT nat Γ) k m :
  baseM σ (interp (plus_t σ) e k m) = k + baseM σ m.
Proof. revert Γ e m; induction σ as [|σ _ τ IH]; intros Γ e m; [reflexivity | apply IH]. Qed.

(** ** Usual polynomials

    The type [N ⇒ .. ⇒ N] of the functions of [n] numbers, the application
    of such a function to a list, and the translation of a polynomial in
    [n] variables ([Poly]) into a term. *)
Fixpoint nary (n : nat) : ty := match n with 0 => tN | S n => tN ⇒ nary n end.

Fixpoint applyN (n : nat) : M (nary n) -> list nat -> nat :=
  match n with
  | 0 => fun f _ => f
  | S n => fun f ss => applyN n (f (hd 0 ss)) (tl ss)
  end.

Fixpoint constN_t (n : nat) {Γ} : term hpc Γ (tN ⇒ nary n) :=
  match n with 0 => tlam (tvar vz) | S n => tlam (tlam (tapp (constN_t n) (tvar (vs vz)))) end.

Fixpoint projN_t (n i : nat) {Γ} : term hpc Γ (nary n) :=
  match n, i with
  | 0, _ => tcst (hnum 0)
  | S n, 0 => constN_t n
  | S n, S i => tlam (projN_t n i)
  end.

(** The pointwise extension of [c] to [nary n]. *)
Fixpoint liftN_t (c : hpc (tN ⇒ tN ⇒ tN)) (n : nat) {Γ} : term hpc Γ (nary n ⇒ nary n ⇒ nary n) :=
  match n with
  | 0 => tcst c
  | S n =>
      tlam (tlam (tlam (tapp (tapp (liftN_t c n) (tapp (tvar (vs (vs vz))) (tvar vz)))
                             (tapp (tvar (vs vz)) (tvar vz)))))
  end.

Fixpoint powN_t (n d : nat) {Γ} (p : term hpc Γ (nary n)) : term hpc Γ (nary n) :=
  match d with
  | 0 => tapp (constN_t n) (tcst (hnum 1))
  | S d => tapp (tapp (liftN_t hmul n) p) (powN_t n d p)
  end.

Fixpoint ptrans (n : nat) (p : poly) {Γ} : term hpc Γ (nary n) :=
  match p with
  | pconst k => tapp (constN_t n) (tcst (hnum k))
  | pvar i => projN_t n i
  | padd p q => tapp (tapp (liftN_t hadd n) (ptrans n p)) (ptrans n q)
  | pmul p q => tapp (tapp (liftN_t hmul n) (ptrans n p)) (ptrans n q)
  | ppow p d => powN_t n d (ptrans n p)
  end.

Lemma applyN_constN n Γ (e : envT nat Γ) k ss : applyN n (interp (constN_t n) e k) ss = k.
Proof. revert Γ e ss; induction n; intros; [reflexivity | apply IHn]. Qed.

Lemma applyN_projN n i Γ (e : envT nat Γ) ss :
  length ss = n -> applyN n (interp (projN_t n i) e) ss = nth i ss 0.
Proof.
  revert i Γ e ss; induction n as [|n IH]; intros i Γ e ss Hl.
  - destruct ss; [destruct i; reflexivity | discriminate].
  - destruct ss as [|s ss]; [discriminate|]. destruct i; cbn.
    + apply applyN_constN.
    + apply IH. cbn in Hl. lia.
Qed.

Lemma applyN_liftN c n Γ (e : envT nat Γ) f g ss :
  applyN n (interp (liftN_t c n) e f g) ss = cinterp _ c (applyN n f ss) (applyN n g ss).
Proof. revert Γ e f g ss; induction n; intros; [reflexivity | apply IHn]. Qed.

(** Every polynomial in [n] variables is (the uncurried form of) a
    higher-order polynomial of type [N ⇒ .. ⇒ N]. *)
Theorem poly_hpoly n p ss : length ss = n -> applyN n ⟦ptrans n p⟧ ss = peval p ss.
Proof.
  intro Hl. unfold eval. generalize (tt : envT nat []). generalize (@nil ty) as Γ. intros Γ e.
  induction p as [k|i|p IHp q IHq|p IHp q IHq|p IHp d]; cbn [ptrans peval].
  - apply applyN_constN.
  - apply applyN_projN, Hl.
  - exact (eq_trans (applyN_liftN hadd n _ e _ _ ss) (f_equal2 Nat.add IHp IHq)).
  - exact (eq_trans (applyN_liftN hmul n _ e _ _ ss) (f_equal2 Nat.mul IHp IHq)).
  - induction d as [|d IHd]; cbn [powN_t Nat.pow].
    + apply applyN_constN.
    + exact (eq_trans (applyN_liftN hmul n _ e _ _ ss) (f_equal2 Nat.mul IHp IHd)).
Qed.

(** ** Growth

    A higher-order polynomial of type [N ⇒ N] is bounded by a polynomial
    ([hpoly_growth]). The proof is by a logical relation on the families of
    functionals indexed by a number [n] ([pgrowth]): at [N], the families
    bounded by a polynomial in [n]; at [σ ⇒ τ], the families that map those
    of [σ] to those of [τ]. *)
Fixpoint pgrowth (σ : ty) : (nat -> M σ) -> Prop :=
  match σ return (nat -> M σ) -> Prop with
  | tN => fun G => exists c d, forall n, G n <= c * (n + 1) ^ d
  | σ ⇒ τ => fun G => forall H, pgrowth σ H -> pgrowth τ (fun n => G n (H n))
  end.

Fixpoint pgrowth_env (Γ : list ty) : (nat -> envT nat Γ) -> Prop :=
  match Γ with
  | [] => fun _ => True
  | σ :: Γ => fun E => pgrowth_env Γ (fun n => etl (E n)) /\ pgrowth σ (fun n => ehd (E n))
  end.

Lemma pgrowth_cst σ (c : hpc σ) : pgrowth σ (fun _ => cinterp σ c).
Proof.
  destruct c as [k| |].
  - exists k, 0. intro n. cbn. lia.
  - intros G1 (c1 & d1 & H1) G2 (c2 & d2 & H2). exists (c1 + c2), (d1 + d2). intro n.
    specialize (H1 n). specialize (H2 n).
    assert ((n + 1) ^ d1 <= (n + 1) ^ (d1 + d2)) by (apply Nat.pow_le_mono_r; lia).
    assert ((n + 1) ^ d2 <= (n + 1) ^ (d1 + d2)) by (apply Nat.pow_le_mono_r; lia).
    cbn. nia.
  - intros G1 (c1 & d1 & H1) G2 (c2 & d2 & H2). exists (c1 * c2), (d1 + d2). intro n.
    specialize (H1 n). specialize (H2 n). rewrite Nat.pow_add_r. cbn. nia.
Qed.

Lemma pgrowth_interp Γ σ (p : term hpc Γ σ) E :
  pgrowth_env Γ E -> pgrowth σ (fun n => interp p (E n)).
Proof.
  revert E. induction p as [Γ σ x|Γ σ c|Γ σ τ p IH|Γ σ τ p IHp q IHq]; intros E HE.
  - induction x as [Γ σ|Γ σ τ x IHx]; [apply HE | exact (IHx _ (proj1 HE))].
  - apply pgrowth_cst.
  - intros H HH. exact (IH (fun n => ECons (E n) (H n)) (conj HE HH)).
  - exact (IHp E HE _ (IHq E HE)).
Qed.

Theorem hpoly_growth (p : hpoly (tN ⇒ tN)) : exists c d, forall n, ⟦p⟧ n <= c * (n + 1) ^ d.
Proof.
  apply (pgrowth_interp [] _ p (fun _ => tt) I (fun n => n)).
  exists 1, 1. intro n. rewrite Nat.pow_1_r. lia.
Qed.

(** [2 ^ n] is not bounded by a polynomial. *)
Lemma sq_le_pow2 k : 4 <= k -> k * k <= 2 ^ k.
Proof.
  induction k as [|k IH]; intro Hk; [lia|].
  destruct (Nat.eq_dec k 3) as [->|Hk3]; [cbn; lia|].
  specialize (IH ltac:(lia)). rewrite Nat.pow_succ_r'. nia.
Qed.

Lemma lin_lt_pow2 a b : exists k, a * k + b < 2 ^ k.
Proof.
  exists (2 * (a + b) + 4). pose proof (sq_le_pow2 (2 * (a + b) + 4) ltac:(lia)).
  set (k := 2 * (a + b) + 4) in *. set (P := 2 ^ k) in *. nia.
Qed.

Theorem pow2_not_poly (p : hpoly (tN ⇒ tN)) : ~ (forall n, 2 ^ n <= ⟦p⟧ n). 
Proof. 
  destruct (hpoly_growth p) as (c & d & Hgrowth).
  intro Hf. assert(forall n, 2 ^ n <= c * (n + 1) ^ d).
  { intro n. now transitivity (⟦p⟧ n). }
  destruct (lin_lt_pow2 d (c + 1)) as [j Hj].
  assert (Hj1 : 1 <= 2 ^ j) by (apply Nat.pow_le_mono_r with (a := 2) (b := 0); lia).
  specialize (H (2 ^ j - 1)). replace (2 ^ j - 1 + 1) with (2 ^ j) in H by lia.
  rewrite <- Nat.pow_mul_r in H.
  pose proof (Nat.pow_gt_lin_r 2 c ltac:(lia)).
  assert (2 ^ (2 ^ j - 1) <= 2 ^ (c + j * d)) by (rewrite Nat.pow_add_r; nia).
  apply Nat.pow_le_mono_r_iff in H1; lia.
Qed.
