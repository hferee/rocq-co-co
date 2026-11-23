(** * Depths of the terms of L

    The depths of the terms of L along an evaluation, for the lower bounds
    in L ([NatLowerBound], [ListLowerBound]), where the depth of the
    encoding of an output bounds its size.

    A β-step [app (lam u) v ≻ subst u 0 v] puts [v] at the occurrences of
    the variable of [lam u]: the depth of the term grows by at most the
    depth of these occurrences in [u] ([depth_subst]). These depths do
    not grow during an evaluation ([vdepth_subst]): the values substituted
    are closed, so that the variables of a body stay where they are. The
    depth of a term thus grows by at most a constant [D] at each step
    ([evalc_depth]), and the encoding of a number has a depth of [3] per
    unit. *)

From Complexity Require Import LInstance.
From Undecidability.L Require Import Util.L_facts.
From Stdlib Require Import Arith Lia.
Unset Implicit Arguments.

Fixpoint tdepth (t : term) : nat :=
  match t with
  | var _ => 1
  | app s u => S (Nat.max (tdepth s) (tdepth u))
  | lam s => S (tdepth s)
  end.

(** [vd t k]: [1] plus the depth of the deepest occurrence of the variable
    [k] in [t] ([0] if there is none). *)
Definition up (m : nat) : nat := match m with 0 => 0 | S _ => S m end.

Fixpoint vd (t : term) (k : nat) : nat :=
  match t with
  | var n => if Nat.eqb n k then 1 else 0
  | app s u => up (Nat.max (vd s k) (vd u k))
  | lam s => up (vd s (S k))
  end.

(** [vdepth t]: the largest [vd] of the variable of a [lam] in [t]. *)
Fixpoint vdepth (t : term) : nat :=
  match t with
  | var _ => 0
  | app s u => Nat.max (vdepth s) (vdepth u)
  | lam s => Nat.max (vd s 0) (vdepth s)
  end.

Lemma up_mono m m' : m <= m' -> up m <= up m'.
Proof. destruct m, m'; cbn -[Nat.max]; lia. Qed.

Lemma vd_subst_none t k v : vd t k = 0 -> subst t k v = t.
Proof.
  revert k. induction t as [n|s IHs u IHu|s IHs]; intros k H; cbn -[Nat.max] in *.
  - destruct (Nat.eqb n k); [discriminate | reflexivity].
  - destruct (Nat.max (vd s k) (vd u k)) eqn:E; [|discriminate].
    rewrite IHs, IHu; [reflexivity | lia | lia].
  - destruct (vd s (S k)) eqn:E; [|discriminate]. rewrite IHs; [reflexivity | exact E].
Qed.

Lemma depth_subst t k v : tdepth (subst t k v) <= Nat.max (tdepth t) (vd t k + tdepth v).
Proof.
  revert k. induction t as [n|s IHs u IHu|s IHs]; intro k; cbn -[Nat.max].
  - destruct (Nat.eqb n k); cbn -[Nat.max]; lia.
  - destruct (Nat.max (vd s k) (vd u k)) eqn:E.
    + rewrite !vd_subst_none by lia. cbn -[Nat.max]. lia.
    + cbn -[Nat.max]. specialize (IHs k). specialize (IHu k). lia.
  - destruct (vd s (S k)) eqn:E.
    + rewrite vd_subst_none by exact E. cbn -[Nat.max]. lia.
    + cbn -[Nat.max]. specialize (IHs (S k)). lia.
Qed.

Lemma vd_bound k t : bound k t -> forall j, k <= j -> vd t j = 0.
Proof.
  induction 1 as [k n Hn|k s u _ IHs _ IHu|k s _ IHs]; intros j Hj; cbn -[Nat.max].
  - destruct (Nat.eqb_spec n j); [lia | reflexivity].
  - rewrite IHs, IHu by exact Hj. reflexivity.
  - rewrite IHs by lia. reflexivity.
Qed.

Lemma vd_closed v j : closed v -> vd v j = 0.
Proof. intro H. apply closed_dcl in H. exact (vd_bound 0 v H j (Nat.le_0_l j)). Qed.

Lemma vd_subst_other t k v j : closed v -> j <> k -> vd (subst t k v) j <= vd t j.
Proof.
  intro Hv. revert k j. induction t as [n|s IHs u IHu|s IHs]; intros k j Hjk; cbn -[Nat.max].
  - destruct (Nat.eqb n k); [rewrite vd_closed by exact Hv; lia | reflexivity].
  - apply up_mono. specialize (IHs k j Hjk). specialize (IHu k j Hjk). lia.
  - apply up_mono. apply IHs. lia.
Qed.

Lemma vdepth_subst t k v : closed v -> vdepth (subst t k v) <= Nat.max (vdepth t) (vdepth v).
Proof.
  intro Hv. revert k. induction t as [n|s IHs u IHu|s IHs]; intro k; cbn -[Nat.max].
  - destruct (Nat.eqb n k); cbn -[Nat.max]; lia.
  - specialize (IHs k). specialize (IHu k). lia.
  - pose proof (vd_subst_other s (S k) v 0 Hv ltac:(lia)). specialize (IHs (S k)). lia.
Qed.

Lemma closed_app_intro s t : closed s -> closed t -> closed (app s t).
Proof. rewrite !closed_dcl. intros Hs Ht. now constructor. Qed.

(** Each β-step of an evaluation adds at most [D] to the depth, if the
    variables of the bodies are at depth at most [D]. *)
Lemma evalc_depth D n s w : evalc n s w -> closed s -> vdepth s <= D ->
  tdepth w <= tdepth s + D * n /\ vdepth w <= D /\ closed w.
Proof.
  induction 1 as [u|s t u v w i j k Hs IHs Ht IHt Hw IHw]; intros Hc HD.
  - split; [lia | split; assumption].
  - apply closed_app in Hc as [Hcs Hct]. cbn -[Nat.max] in HD.
    destruct (IHs Hcs ltac:(lia)) as (Ds & Vs & Cs).
    destruct (IHt Hct ltac:(lia)) as (Dt & Vt & Ct).
    assert (Cw : closed (subst u 0 v)).
    { apply closed_dcl. apply closed_dcl in Cs, Ct. inv Cs. now apply closed_subst. }
    pose proof (vdepth_subst u 0 v Ct). cbn -[Nat.max] in Vs.
    destruct (IHw Cw ltac:(lia)) as (Dw & Vw & Cw').
    pose proof (depth_subst u 0 v). cbn -[Nat.max] in Ds.
    split; [| split; assumption]. cbn -[Nat.max].
    replace (D * S (i + j + k)) with (D + D * i + D * j + D * k) by ring. lia.
Qed.

Lemma tdepth_enc n : tdepth (nat_enc' n) = 3 * n + 3.
Proof. induction n as [|n IH]; cbn -[Nat.max] in *; [reflexivity | rewrite IH; lia]. Qed.

Lemma vd_enc n j : vd (nat_enc' n) j = 0.
Proof. exact (vd_closed _ j (proj1 (nat_enc_proc n))). Qed.

Lemma vdepth_enc n : vdepth (nat_enc' n) <= 2.
Proof.
  induction n as [|n IH]; [cbn -[Nat.max]; lia|].
  cbn [nat_enc' vdepth vd Nat.eqb]. rewrite !vd_enc, ?Nat.max_0_r, ?Nat.max_0_l. cbn [up]. lia.
Qed.
