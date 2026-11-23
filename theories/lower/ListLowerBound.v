(** * A linear lower bound for sorting, from the growth of lists

    An axiom on the growth of the lists of numbers, as [nat_growth] for
    the numbers ([NatLowerBound]), its proof in L, and the lower bound that
    it gives for sorting. *)

From Complexity Require Export TimeCostModel Poly.
From Stdlib Require Import List Permutation Sorted Lia.
Import ListNotations.
Unset Implicit Arguments.

(** ** The axiom

    The output of a function is a suffix of its input and at most
    [a * (1 + cost)] other elements, for a constant [a] of the function:
    each unit of cost builds a bounded number of cells, and the others come
    from the input. It is stated on [list nat]: in L, the encodings of
    values of different types coincide ([0] and [[]]), so that a function
    on lists of lists could return an element of its input as a list, at a
    constant cost.

    An axiom that a [cons] costs at least [1], as [succ_not_free] for [S],
    would not suffice: the rules that compose functions add costs of their
    own, so that it would not reach the other functions.

    It holds at the well-formed inputs ([wf]): a bound may say anything at the others, which the realisers of
    the function are never applied to. *)

Module Type ListGrowthAxiom (Import CM : CostModel) (Import ND : NatData CM) (Import LD : ListData CM).
  Parameter list_growth :
    forall (f : list nat -> list nat) (c : ℂI (list nat) (list unit) -> ℂO (list unit)),
    ComplexityBound f c ->
    exists a, forall cl, wf (val cl) (pot cl) -> exists p q s,
      f (val cl) = p ++ s /\ val cl = q ++ s /\ length p <= a * (1 + cost (c cl)).
End ListGrowthAxiom.

Module Type ListLowerTimeCostModel := ParamTimeCostModel <+ ListGrowthAxiom.

(** ** Sorting

    The best that such an axiom gives is linear: the output of a sort is
    no longer than its input. The lower bound [log2 (n!)] counts
    comparisons, which the sizes do not see ([SortingLowerBound],
    [SortingDialogue]). *)

(** [dec n = [n; ...; 1]]. *)
Fixpoint dec (n : nat) : list nat := match n with 0 => [] | S m => S m :: dec m end.

Lemma length_dec n : length (dec n) = n.
Proof. induction n as [|n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Two consecutive elements of [dec n] decrease. *)
Lemma dec_adjacent n q x y s : dec n = q ++ x :: y :: s -> y < x.
Proof.
  revert q. induction n as [|m IH]; intros q H; cbn in H.
  - destruct q; discriminate.
  - destruct q as [|z q]; cbn in H; injection H as Hx Hy.
    + subst x. destruct m as [|m]; cbn in Hy; [discriminate | injection Hy as Hy _]; lia.
    + exact (IH q Hy).
Qed.

(** Two consecutive elements of a sorted list increase. *)
Lemma sorted_adjacent (p : list nat) x y s : Sorted le (p ++ x :: y :: s) -> x <= y.
Proof.
  induction p as [|z p IH]; cbn; intro H.
  - apply Sorted_inv in H as [_ H]. apply HdRel_inv in H. exact H.
  - apply Sorted_inv in H as [H _]. exact (IH H).
Qed.

(** A suffix of a sorted list and of [dec n] has at most one element. *)
Lemma common_suffix_short n out p q s :
  Sorted le out -> out = p ++ s -> dec n = q ++ s -> length s <= 1.
Proof.
  intros Hs Hout Hdec. destruct s as [|x [|y s]]; cbn; [lia | lia | exfalso].
  subst out. pose proof (sorted_adjacent p x y s Hs). pose proof (dec_adjacent n q x y s Hdec). lia.
Qed.

Module SortingLinearLowerBound (Import M : ListLowerTimeCostModel).

  (** A sorting function returns a sorted permutation of its input. *)
  Definition Sorting (sort : list nat -> list nat) : Prop :=
    forall l, Permutation (sort l) l /\ Sorted le (sort l).

  (** On [dec n], a sort builds at least [n - 1] elements: its output has
      [n], of which at most one is a suffix of the input
      ([common_suffix_short]). *)
  Theorem sort_linear_lower (sort : list nat -> list nat) (c : ℂI (list nat) (list unit) -> ℂO (list unit)) :
    Sorting sort -> ComplexityBound sort c ->
    exists a, forall n pl, wf (dec n) pl -> n - 1 <= a * (1 + cost (c (dec n ⋊ pl))).
  Proof.
    intros Hs Hc. destruct (list_growth sort c Hc) as [a Ha]. exists a. intros n pl Hw.
    destruct (Ha (dec n ⋊ pl) Hw) as (p & q & s & Hout & Hin & Hp). cbn in Hout, Hin.
    destruct (Hs (dec n)) as [Hperm Hsorted].
    pose proof (Permutation_length Hperm) as Hlen. rewrite length_dec in Hlen.
    pose proof (common_suffix_short n (sort (dec n)) p q s Hsorted Hout Hin) as Hsuf.
    rewrite Hout, length_app in Hlen. lia.
  Qed.

  (** In the sizes of the arguments: no constant bound. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Corollary sort_not_constant (sort : list nat -> list nat) : Sorting sort -> ~ ConstantBound sort.
  Proof.
    intros Hs [p [Hd Hb]]. destruct (sort_linear_lower sort _ Hs Hb) as [a Ha].
    set (k := peval p [0]).
    specialize (Ha (2 + a * (1 + k)) []). cbn in Ha.
    rewrite (peval_deg0 p _ [0] Hd) in Ha. fold k in Ha. lia.
  Qed.
  *)
End SortingLinearLowerBound.

(** ** In L

    The proof extends the one of [nat_growth] ([NatLowerBound]): the depth
    of a term, not counting its old subterms ([nd]), the encodings of the
    suffixes of the input and of the numbers. A β-step adds to it at most
    the depth of the occurrences of the variable of its body, and the
    bodies of the old abstractions have depth at most [4]: each step adds
    at most a constant ([evalc_nd]). An output list has [3] units of this
    depth per cell above its first old suffix ([nd_lenc_split]). *)

From Complexity Require Import LInstance NatLowerBound.
From Undecidability.L Require Import Util.L_facts.
Unset Implicit Arguments.

(** *** Encodings *)

(** The realiser of a list of numbers. *)
Fixpoint lenc (l : list nat) : term :=
  match l with
  | [] => lam (lam (var 1))
  | x :: l => lam (lam (app (app (var 0) (nat_enc' x)) (lenc l)))
  end.

(** [lenc l] realises [l] at its well-formed complexities. *)
Lemma rl_lenc j (l : list nat) (c : list unit) :
  @L.wf _ _ (L.Repr_list L.Repr_nat) l c -> rl (L.Repr_list L.Repr_nat) j l c (lenc l).
Proof.
  intro Hw. induction Hw as [| x a l c _ _ IH]; cbn; [reflexivity|].
  exists (nat_enc' x), (lenc l). split; [reflexivity | split; [reflexivity | exact IH]].
Qed.

Lemma wf_units (l : list nat) : @L.wf _ _ (L.Repr_list L.Repr_nat) l (map (fun _ => tt) l).
Proof. induction l; constructor; [exact Logic.I | assumption]. Qed.

Lemma rl_lenc_inv j l c s : rl (L.Repr_list L.Repr_nat) j l c s -> s = lenc l.
Proof.
  revert c s. induction l as [|x l IH]; intros [|a c] s H; cbn in H |- *; try (exact H || contradiction).
  destruct H as (r & t & -> & -> & Ht). rewrite (IH _ _ Ht). reflexivity.
Qed.

Lemma lenc_closed l : closed (lenc l).
Proof. exact (proj1 (rl_proc (rl_lenc 0 l _ (wf_units l)))). Qed.

Lemma nat_enc_inj m m' : nat_enc' m = nat_enc' m' -> m = m'.
Proof.
  revert m'. induction m as [|m IH]; intros [|m'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H. rewrite (IH m' H). reflexivity.
Qed.

Lemma lenc_inj l l' : lenc l = lenc l' -> l = l'.
Proof.
  revert l'. induction l as [|x l IH]; intros [|x' l'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. rewrite (nat_enc_inj _ _ Hx), (IH _ Hl). reflexivity.
Qed.

(** *** The old subterms *)

Fixpoint teqb (s t : term) : bool :=
  match s, t with
  | var n, var m => Nat.eqb n m
  | app s1 s2, app t1 t2 => teqb s1 t1 && teqb s2 t2
  | lam s, lam t => teqb s t
  | _, _ => false
  end.

Lemma teqb_eq s t : teqb s t = true -> s = t.
Proof.
  revert t. induction s as [n|s1 IH1 s2 IH2|s IH]; intros [m|t1 t2|t] H; cbn in H; try discriminate.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
  - rewrite (IH _ H). reflexivity.
Qed.

(** The encodings of the numbers. *)
Fixpoint is_nenc (t : term) : bool :=
  match t with
  | lam (lam (var 1)) => true
  | lam (lam (app (var 0) m)) => is_nenc m
  | _ => false
  end.

Lemma is_nenc_sound : forall t, is_nenc t = true -> exists m, t = nat_enc' m.
Proof.
  fix IH 1. intros t H.
  destruct t as [n|a b|t]; try discriminate.
  destruct t as [n|a b|t]; try discriminate.
  destruct t as [[|[|n]]|a b|t]; try discriminate.
  - exists 0. reflexivity.
  - destruct a as [[|n]|a1 a2|a]; try discriminate.
    destruct (IH b H) as [m ->]. exists (S m). reflexivity.
Qed.

Lemma is_nenc_complete m : is_nenc (nat_enc' m) = true.
Proof. induction m as [|m IH]; [reflexivity | exact IH]. Qed.

(** The suffixes of a list. *)
Fixpoint suffixes (l : list nat) : list (list nat) :=
  match l with [] => [[]] | x :: t => (x :: t) :: suffixes t end.

Lemma suffixes_sound l s : In s (suffixes l) -> exists q, l = q ++ s.
Proof.
  induction l as [|x t IH]; cbn; intros [H|H].
  - subst. exists []. reflexivity.
  - destruct H.
  - subst. exists []. reflexivity.
  - destruct (IH H) as [q ->]. exists (x :: q). reflexivity.
Qed.

Lemma suffixes_complete l q s : l = q ++ s -> In s (suffixes l).
Proof.
  revert l. induction q as [|y q IH]; intros l ->; cbn.
  - destruct s; left; reflexivity.
  - right. apply IH. reflexivity.
Qed.

Section Old.
  Variable l : list nat.

  (** The old subterms: the encodings of the numbers, and of the suffixes
      of [l]. *)
  Definition old (t : term) : bool := is_nenc t || existsb (teqb t) (map lenc (suffixes l)).

  Lemma old_cases t : old t = true -> (exists m, t = nat_enc' m) \/ (exists s, In s (suffixes l) /\ t = lenc s).
  Proof.
    unfold old. intro H. apply orb_prop in H as [H|H]; [left; exact (is_nenc_sound t H) | right].
    apply existsb_exists in H as (u & Hu & He). apply in_map_iff in Hu as (s & <- & Hs).
    exists s. split; [exact Hs | exact (teqb_eq _ _ He)].
  Qed.

  Lemma old_closed t : old t = true -> closed t.
  Proof.
    intro H. destruct (old_cases t H) as [(m & ->)|(s & _ & ->)];
      [exact (proj1 (nat_enc_proc m)) | apply lenc_closed].
  Qed.

  Lemma old_nenc m : old (nat_enc' m) = true.
  Proof. unfold old. rewrite is_nenc_complete. reflexivity. Qed.

  Lemma old_lenc s : In s (suffixes l) -> old (lenc s) = true.
  Proof.
    intro Hs. unfold old. apply orb_true_intro. right. apply existsb_exists.
    exists (lenc s). split; [apply in_map, Hs|].
    clear. induction (lenc s) as [n|a IHa b IHb|a IH]; cbn;
      [apply Nat.eqb_refl | rewrite IHa, IHb; reflexivity | exact IH].
  Qed.

  Lemma old_not_lam_shape t : (forall s, teqb t (lenc s) = false) -> is_nenc t = false -> old t = false.
  Proof.
    intros H1 H2. unfold old. rewrite H2. cbn.
    apply not_true_is_false. intro H. apply existsb_exists in H as (u & Hu & He).
    apply in_map_iff in Hu as (s & <- & _). rewrite H1 in He. discriminate.
  Qed.

  Lemma old_app s u : old (app s u) = false.
  Proof. apply old_not_lam_shape; [intros [|]; reflexivity | reflexivity]. Qed.

  Lemma old_var n : old (var n) = false.
  Proof. apply old_not_lam_shape; [intros [|]; reflexivity | reflexivity]. Qed.

  (** The depth, without the old subterms. *)
  Fixpoint nd (t : term) : nat :=
    if old t then 0 else
    match t with
    | var _ => 1
    | app s u => S (Nat.max (nd s) (nd u))
    | lam s => S (nd s)
    end.

  Lemma nd_var n : nd (var n) = 1.
  Proof. cbn [nd]. rewrite old_var. reflexivity. Qed.

  Lemma nd_app s u : nd (app s u) = S (Nat.max (nd s) (nd u)).
  Proof. cbn [nd]. rewrite old_app. reflexivity. Qed.

  Lemma nd_lam_le s : nd (lam s) <= S (nd s).
  Proof. cbn [nd]. destruct (old (lam s)); lia. Qed.

  Lemma nd_old t : old t = true -> nd t = 0.
  Proof. intro H. destruct t; cbn [nd]; rewrite H; reflexivity. Qed.

  Lemma nd_le_tdepth t : nd t <= tdepth t.
  Proof.
    induction t as [n|s IHs u IHu|s IHs].
    - rewrite nd_var. reflexivity.
    - rewrite nd_app. cbn -[Nat.max]. lia.
    - pose proof (nd_lam_le s). cbn -[Nat.max nd]. lia.
  Qed.

  (** The bodies of the old abstractions are shallow. *)
  Lemma nd_body u : nd u <= nd (lam u) + 4.
  Proof.
    destruct (old (lam u)) eqn:Ho; [| cbn [nd]; rewrite Ho; lia].
    destruct (old_cases _ Ho) as [([|m] & H)|([|x s] & Hs & H)]; cbn in H; injection H as ->.
    - pose proof (nd_lam_le (var 1)). rewrite nd_var in *. lia.
    - pose proof (nd_lam_le (app (var 0) (nat_enc' m))).
      rewrite nd_app, nd_var, (nd_old _ (old_nenc m)) in *. lia.
    - pose proof (nd_lam_le (var 1)). rewrite nd_var in *. lia.
    - assert (Ht : In s (suffixes l)).
      { destruct (suffixes_sound _ _ Hs) as [q Hq]. apply (suffixes_complete l (q ++ [x])).
        rewrite <- app_assoc. exact Hq. }
      pose proof (nd_lam_le (app (app (var 0) (nat_enc' x)) (lenc s))).
      rewrite !nd_app, nd_var, (nd_old _ (old_nenc x)), (nd_old _ (old_lenc s Ht)) in *. lia.
  Qed.

  Lemma nd_subst t k v : closed v -> nd (subst t k v) <= Nat.max (nd t) (vd t k + nd v).
  Proof.
    intro Hv. revert k. induction t as [n|s IHs u IHu|s IHs]; intro k.
    - cbn [subst vd]. rewrite nd_var. destruct (Nat.eqb n k); [lia | rewrite nd_var; lia].
    - cbn [subst vd]. rewrite !nd_app. destruct (Nat.max (vd s k) (vd u k)) eqn:E.
      + rewrite !vd_subst_none by lia. lia.
      + cbn [up]. specialize (IHs k). specialize (IHu k). lia.
    - destruct (old (lam s)) eqn:Ho.
      + rewrite (old_closed _ Ho). lia.
      + assert (Hl : nd (lam s) = S (nd s)) by (cbn [nd]; rewrite Ho; reflexivity).
        cbn [subst vd]. rewrite Hl. pose proof (nd_lam_le (subst s (S k) v)).
        destruct (vd s (S k)) eqn:E.
        * rewrite vd_subst_none in * by exact E. lia.
        * cbn [up]. specialize (IHs (S k)). lia.
  Qed.

  (** Each step adds at most [D + 4], if the variables of the bodies are at
      depth at most [D]. *)
  Lemma evalc_nd D N s w : evalc N s w -> closed s -> vdepth s <= D ->
    nd w <= nd s + (D + 4) * N /\ vdepth w <= D /\ closed w.
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
      pose proof (nd_subst u 0 v Ct). pose proof (nd_body u).
      split; [| split; assumption]. rewrite nd_app.
      replace ((D + 4) * S (i + j + k)) with ((D + 4) + (D + 4) * i + (D + 4) * j + (D + 4) * k) by ring.
      lia.
  Qed.

  (** An output list: [3] per cell above its first old suffix. *)
  Lemma nd_lenc_split L : exists p s, L = p ++ s /\ In s (suffixes l) /\ 3 * length p <= nd (lenc L).
  Proof.
    induction L as [|x L IH].
    - exists [], []. split; [reflexivity | split; [apply (suffixes_complete l l []); rewrite app_nil_r; reflexivity | cbn; lia]].
    - destruct (old (lenc (x :: L))) eqn:Ho.
      + destruct (old_cases _ Ho) as [([|m] & H)|(s & Hs & H)]; cbn in H; try discriminate.
        exists [], s. rewrite (lenc_inj (x :: L) s H). split; [reflexivity | split; [exact Hs | cbn; lia]].
      + destruct IH as (p & s & -> & Hs & Hp). exists (x :: p), s.
        split; [reflexivity | split; [exact Hs|]].
        assert (Hb : old (lam (app (app (var 0) (nat_enc' x)) (lenc (p ++ s)))) = false)
          by (apply old_not_lam_shape; [intros [|]; reflexivity | reflexivity]).
        change (lenc (x :: p ++ s)) with (lam (lam (app (app (var 0) (nat_enc' x)) (lenc (p ++ s))))) in Ho |- *.
        cbn [nd]. rewrite Ho, Hb, !old_app, old_var. cbn [length]. lia.
  Qed.
End Old.

Lemma vd_lenc l j : vd (lenc l) j = 0.
Proof. exact (vd_closed _ j (lenc_closed l)). Qed.

Lemma vdepth_lenc l : vdepth (lenc l) <= 3.
Proof.
  induction l as [|x l IH]; [cbn; lia|].
  cbn [lenc vdepth vd Nat.eqb]. rewrite !vd_enc, !vd_lenc, ?Nat.max_0_r, ?Nat.max_0_l. cbn [up].
  pose proof (vdepth_enc x). lia.
Qed.

(** *** [list_growth] *)

Lemma L_list_growth (f : list nat -> list nat) (c : ℂI (list nat) (list unit) -> ℂO (list unit)) :
  L.ComplexityBound f c ->
  exists a, forall cl, L.wf (val cl) (pot cl) -> exists p q s,
    f (val cl) = p ++ s /\ val cl = q ++ s /\ length p <= a * (1 + cost (c cl)).
Proof.
  intros [(c0 & Hbo & s0 & Hs)].
  set (D := Nat.max (vdepth s0) 3).
  exists (1 + tdepth s0 + (D + 4) * LInstance.K). intros cl Hw.
  destruct (Hbo cl Hw) as [Hle _].
  set (C := cost (c0 cl)) in *.
  assert (E : cost (c0 (val cl ⋊ pot cl)) = C) by reflexivity.
  destruct (Hs C) as [Hp H].
  destruct (H C (val cl) (pot cl) (lenc (val cl)) (le_n C) (rl_lenc C (val cl) (pot cl) Hw)
              ltac:(rewrite E; lia)) as (N & v & Hv & HN & Hr).
  rewrite E in HN. apply rl_lenc_inv in Hr. subst v.
  apply pow_evalc in Hv; [| apply (proj2 (rl_proc (rl_lenc 0 (f (val cl)) _ (wf_units _))))].
  destruct (evalc_nd (val cl) D N _ _ Hv) as (Hd & _).
  { apply closed_app_intro; [exact (proj1 Hp) | apply lenc_closed]. }
  { cbn -[Nat.max]. pose proof (vdepth_lenc (val cl)). unfold D. lia. }
  destruct (nd_lenc_split (val cl) (f (val cl))) as (p & s & Hsplit & Hin & Hlen).
  destruct (suffixes_sound _ _ Hin) as [q Hq].
  exists p, q, s. split; [exact Hsplit | split; [exact Hq |]].
  rewrite nd_app, (nd_old (val cl) (lenc (val cl))) in Hd
    by (apply old_lenc, (suffixes_complete _ []); reflexivity).
  pose proof (nd_le_tdepth (val cl) s0).
  assert ((D + 4) * N <= (D + 4) * LInstance.K * cost (c cl)).
  { rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. unfold LInstance.K in *. lia. }
  assert ((D + 4) * LInstance.K * cost (c cl) <= (1 + tdepth s0 + (D + 4) * LInstance.K) * cost (c cl))
    by (apply Nat.mul_le_mono_r; lia).
  nia.
Qed.

Module LListLower <: ListLowerTimeCostModel.
  Include L.
  Definition list_growth := L_list_growth.
End LListLower.
