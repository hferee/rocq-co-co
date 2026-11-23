(** * Lower bounds on the functions on numbers

    Two axioms with negative content on the functions from [nat] to [nat],
    what follows from them, and their proofs in L. *)

From Complexity Require Export TimeCostModel Poly.
From Stdlib Require Import List Lia.
Import ListNotations.
Unset Implicit Arguments.

(** ** The axioms

    The axioms of the time cost model are upper bounds: they all conclude
    a [ComplexityBound], and [has_complexity := fun _ _ => True] satisfies
    them. A lower bound needs an axiom that says what a bound implies.

    [succ_not_free]: whatever its bound, an application of [S] costs at
    least [1], on every argument. *)

Module Type SuccAxiom (Import CM : CostModel) (Import ND : NatData CM).
  Parameter succ_not_free : forall c : ℂI nat unit -> ℂO unit,
    ComplexityBound S c -> forall cn, 1 <= cost (c cn).
End SuccAxiom.

(** [nat_growth]: the size of the output exceeds the size of the input by
    at most [a * (1 + cost)], for a constant [a] of the function (it cannot
    be the same for all the functions, [L_no_uniform_growth]). *)
Module Type NatGrowthAxiom (Import CM : CostModel) (Import ND : NatData CM).
  Parameter nat_growth : forall (f : nat -> nat) (c : ℂI nat unit -> ℂO unit),
    ComplexityBound f c ->
    exists a, forall cn, size (f (val cn)) <= size (val cn) + a * (1 + cost (c cn)).
End NatGrowthAxiom.

Module Type NatLowerTimeCostModel := ParamTimeCostModel <+ SuccAxiom <+ NatGrowthAxiom.

(** ** Consequences *)

Module NatLowerBounds (Import M : NatLowerTimeCostModel).

  (** *** The successor *)

  Lemma c_S_pos : 1 <= c_S.
  Proof. exact (succ_not_free _ S_complexity (0 ⋊ tt)). Qed.

  (** A function [f] that is [S] once applied to [v]: whatever its bound
      [cf], the application of [f v] costs at least [1], on every argument.
      The application of a function to a value with a bound is the only
      rule of the model that adds no cost ([apply_complexity]): the others
      add costs of their own, so that this lower bound does not reach
      [fun n => S (S n)], nor grow with the arguments. *)
  Lemma applied_succ_not_free {A CA} `{Repr A CA} (f : A -> nat -> nat)
    (cf : ℂI A CA -> ℂO (ℂI nat unit -> ℂO unit)) (v : A) (cv : CA) :
    f v = S -> ComplexityBound v cv -> ComplexityBound f cf ->
    forall cn, 1 <= cost (res (cf (v ⋊ cv)) cn).
  Proof.
    intros Hv Hcv Hf. apply succ_not_free. rewrite <- Hv. exact (apply_complexity cf Hcv Hf).
  Qed.

  (** Adding [1] costs at least [1], whatever the bound of [Nat.add]:
      [Nat.add 1] is [S] (by conversion). *)
  Lemma add_one_not_free (c : ℂI nat unit -> ℂO (ℂI nat unit -> ℂO unit)) :
    ComplexityBound Nat.add c -> forall cm, 1 <= cost (res (c (1 ⋊ tt)) cm).
  Proof. intro Hc. exact (applied_succ_not_free Nat.add c 1 tt eq_refl (nat_complexity 1) Hc). Qed.

  (** At higher order: [Nat.iter 1 S] is [S], whatever the bound of
      [Nat.iter] and the bound of [S] given to it. *)
  Lemma iter_one_not_free
    (c : ℂI nat unit -> ℂO (ℂI (nat -> nat) (ℂI nat unit -> ℂO unit) -> ℂO (ℂI nat unit -> ℂO unit)))
    (cs : ℂI nat unit -> ℂO unit) :
    ComplexityBound (fun n => @Nat.iter n nat) c -> ComplexityBound S cs ->
    forall cn, 1 <= cost (res (res (c (1 ⋊ tt)) (S ⋊ cs)) cn).
  Proof.
    intros Hc Hs.
    exact (applied_succ_not_free (@Nat.iter 1 nat) _ S cs eq_refl Hs
             (apply_complexity c (nat_complexity 1) Hc)).
  Qed.

  (** *** The sizes of the outputs *)

  Lemma size_nat n : size n = S n.
  Proof. induction n as [|n IH]; [exact size_O | rewrite size_S, IH; reflexivity]. Qed.

  (** The cost is not at least the size of the output: the identity has
      the constant bound [c_Ic] ([id_complexity]). *)
  Lemma not_output_size :
    ~ (forall (f : nat -> nat) (c : ℂI nat unit -> ℂO unit),
         ComplexityBound f c -> forall cn, size (f (val cn)) <= cost (c cn)).
  Proof.
    intro H. specialize (H (fun x => x) _ (@id_complexity nat unit _) (c_Ic ⋊ tt)).
    cbn in H. rewrite size_nat in H. lia.
  Qed.

  (** The cost is at least the difference between the output and the
      input, up to the constant of the function. For the functions of one
      argument only: a partial application ([Nat.add n]) has its own
      constant, which may grow with [n]. *)
  Lemma nat_growth_diff (f : nat -> nat) (c : ℂI nat unit -> ℂO unit) :
    ComplexityBound f c -> exists a, forall cn, f (val cn) - val cn <= a * (1 + cost (c cn)).
  Proof.
    intro Hf. destruct (nat_growth f c Hf) as [a Ha]. exists a. intro cn.
    specialize (Ha cn). rewrite !size_nat in Ha. lia.
  Qed.

  (** *** No constant bound for doubling, no linear bound for squaring

      In the sizes of the arguments ([ConstantBound], [LinearBound]): the
      bound in the sizes is a polynomial [p] of the size of [n] ([Poly]). *)

  Lemma double_not_constant : ~ ConstantBound (fun n : nat => n + n).
  Proof.
    intros [p [Hd (c & Hb & Hs)]]. destruct (nat_growth_diff _ _ Hb) as [a Ha].
    set (k := peval p [0]). set (n := S (a * (1 + k))).
    specialize (Ha (n ⋊ tt)). destruct (Hs (n ⋊ tt)) as [Hc _]. cbn in Ha, Hc.
    rewrite (peval_deg0 p _ [0] Hd) in Hc. fold k in Hc.
    assert (a * (1 + cost (c (n ⋊ tt))) <= a * (1 + k)) by (apply Nat.mul_le_mono_l; lia).
    unfold n in *. lia.
  Qed.

  Lemma square_not_linear : ~ LinearBound (fun n : nat => n * n).
  Proof.
    intros [p [Hd (c & Hb & Hs)]]. destruct (nat_growth_diff _ _ Hb) as [a Ha].
    destruct (peval_deg1 p Hd) as [k Hk].
    set (n := a * k + a * (1 + 2 * k) + 2).
    specialize (Ha (n ⋊ tt)). destruct (Hs (n ⋊ tt)) as [Hc _]. cbn in Ha, Hc. rewrite size_nat in Hc.
    assert (a * (1 + cost (c (n ⋊ tt))) <= a * (1 + peval p [S n])) by (apply Nat.mul_le_mono_l; lia).
    specialize (Hk (S n)).
    assert (a * (1 + peval p [S n]) <= a * (1 + k * (1 + S n))) by (apply Nat.mul_le_mono_l; lia).
    assert (n * n = n * (a * k) + n * (a * (1 + 2 * k)) + 2 * n) by (unfold n; ring).
    assert (a * (1 + k * (1 + S n)) = a + 2 * (a * k) + n * (a * k)) by ring.
    assert (a * (1 + 2 * k) <= n * (a * (1 + 2 * k))) by (apply Nat.le_mul_l; unfold n; lia).
    lia.
  Qed.
End NatLowerBounds.

(** ** In L

    The axioms hold in L, whose costs bound the β-steps up to the factor
    [K] ([LInstance]). *)

From Complexity Require Import LInstance LDepth.
From Undecidability.L Require Import Util.L_facts.
Unset Implicit Arguments.

(** *** [succ_not_free]

    A realiser [s] of [S] with a complexity of cost [0] on [n] would take
    [0] steps on the encoding of [n]: [app s (nat_enc' n)] would be the
    encoding of [S n], an abstraction. *)
Lemma L_succ_not_free : forall c : ℂI nat unit -> ℂO unit,
  L.ComplexityBound S c -> forall cn, 1 <= cost (c cn).
Proof.
  intros c [(c0 & Hbo & s & Hs)] cn.
  destruct (Hbo cn Logic.I) as [Hle _].
  enough (1 <= cost (c0 cn)) by lia.
  destruct (cost (c0 cn)) eqn:E; [exfalso | lia].
  assert (E' : cost (c0 (val cn ⋊ pot cn)) = 0) by exact E.
  destruct (Hs 0) as [_ H].
  destruct (H 0 (val cn) (pot cn) (nat_enc' (val cn)) (le_n 0) eq_refl ltac:(rewrite E'; lia))
    as (n & v & Hv & Hn & Hr).
  rewrite E' in Hn. assert (n = 0) by (unfold K in Hn; lia). subst n.
  cbn in Hv, Hr. subst. discriminate.
Qed.

(** *** [nat_growth]

    From the depths of the terms ([LDepth]). *)

(** The output of a realiser [s] of [f] on [n] is at depth at most the
    depth of [app s (nat_enc' n)] plus [D] per step, with [D] the larger
    of [vdepth s] and [2]: the constant of [f] is [1 + tdepth s + D * K]
    ([K] is the factor between the costs and the steps). *)
Lemma L_nat_growth (f : nat -> nat) (c : ℂI nat unit -> ℂO unit) :
  L.ComplexityBound f c ->
  exists a, forall cn, Bounds.size (f (val cn)) <= Bounds.size (val cn) + a * (1 + cost (c cn)).
Proof.
  intros [(c0 & Hbo & s & Hs)].
  set (D := Nat.max (vdepth s) 2).
  exists (1 + tdepth s + D * LInstance.K). intro cn.
  destruct (Hbo cn Logic.I) as [Hle _].
  set (C := cost (c0 cn)) in *.
  assert (E : cost (c0 (val cn ⋊ pot cn)) = C) by reflexivity.
  destruct (Hs C) as [Hp H].
  destruct (H C (val cn) (pot cn) (nat_enc' (val cn)) (le_n C) eq_refl ltac:(rewrite E; lia))
    as (N & v & Hv & HN & Hr).
  rewrite E in HN. cbn -[Nat.max] in Hr. subst v.
  apply pow_evalc in Hv; [| apply (proj2 (nat_enc_proc _))].
  destruct (evalc_depth D N _ _ Hv) as (Hd & _).
  { apply closed_app_intro; [exact (proj1 Hp) | exact (proj1 (nat_enc_proc _))]. }
  { cbn -[Nat.max]. pose proof (vdepth_enc (val cn)). unfold D. lia. }
  cbn -[Nat.max] in Hd. rewrite !tdepth_enc in Hd.
  change (S (f (val cn)) <= S (val cn) + (1 + tdepth s + D * LInstance.K) * (1 + cost (c cn))).
  assert (D * N <= D * LInstance.K * cost (c cn)).
  { rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. unfold LInstance.K in *. lia. }
  assert (D * LInstance.K * cost (c cn) <= (1 + tdepth s + D * LInstance.K) * cost (c cn)) by (apply Nat.mul_le_mono_r; lia).
  nia.
Qed.

Module LNatLower <: NatLowerTimeCostModel.
  Include L.
  Definition succ_not_free := L_succ_not_free.
  Definition nat_growth := L_nat_growth.
End LNatLower.

(** *** No factor for all the functions

    [fun n => k + n] costs [1], for every [k]: its realiser puts [k]
    layers of the encoding above its argument ([addk]), in one step. *)

Fixpoint addk (k i : nat) : term :=
  match k with
  | 0 => var i
  | S k => lam (lam (app (var 0) (addk k (S (S i)))))
  end.

Lemma subst_addk k i n : subst (addk k i) i (nat_enc' n) = nat_enc' (k + n).
Proof.
  revert i. induction k as [|k IH]; intro i; cbn.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma bound_addk k i : bound (S i) (addk k i).
Proof.
  revert i. induction k as [|k IH]; intro i; cbn.
  - constructor. lia.
  - apply dcllam, dcllam, dclApp; [apply dclvar; lia | apply IH].
Qed.

Lemma evalc_enc n : evalc 0 (nat_enc' n) (nat_enc' n).
Proof. destruct n; apply evalc_lam. Qed.

Lemma L_add_cheap k : L.ComplexityBound (fun n => k + n) (fun _ => 1 >|).
Proof.
  apply L.has_complexity_bound. exists (lam (addk k 0)). intro b.
  apply arr_lam.
  - split; [apply closed_dcl; constructor; apply bound_addk | apply lambda_lam].
  - intros j a c1 sa Hj Ha Hc. cbn in Ha. subst sa.
    exists 1, (nat_enc' (k + a)). split; [| split; [Llia | reflexivity]].
    apply evalc_sound. change 1 with (S (0 + 0 + 0)).
    eapply evalc_app; [apply evalc_lam | apply evalc_enc |].
    rewrite subst_addk. apply evalc_enc.
Qed.

(** For each [a], a function that exceeds the bound of [nat_growth] with
    the constant [a]: [fun n => 2 * a + n], at the cost [1]. *)
Example add_const_family (a : nat) :
  exists (f : nat -> nat) (c : ℂI nat unit -> ℂO unit), L.ComplexityBound f c /\
    forall cn, Bounds.size (f (val cn)) >= Bounds.size (val cn) + a * (1 + cost (c cn)).
Proof.
  exists (fun n => 2 * a + n), (fun _ => 1 >|). split; [exact (L_add_cheap (2 * a)) |].
  intro cn. change (S (2 * a + val cn) >= S (val cn) + a * (1 + 1)). lia.
Qed.

(** Hence no constant serves for all the functions. *)
Lemma L_no_uniform_growth :
  ~ exists a, forall (f : nat -> nat) (c : ℂI nat unit -> ℂO unit), L.ComplexityBound f c ->
      forall cn, Bounds.size (f (val cn)) <= Bounds.size (val cn) + a * (1 + cost (c cn)).
Proof.
  intros [a H]. destruct (add_const_family (S a)) as (f & c & Hf & Hge).
  specialize (H f c Hf (0 ⋊ tt)). specialize (Hge (0 ⋊ tt)). nia.
Qed.
