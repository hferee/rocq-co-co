(** * The basic feasible functionals have higher-order polynomial bounds

    The denotation of every term of PV^ω ([BFF]) has a complexity bound
    which is majorized by a higher-order polynomial ([HOPoly]): its costs
    and the lengths of its values are bounded by a λ-term over [+] and [×]
    applied to bounds on its arguments ([BFF_hpoly_bound]).

    The majorization ([maj]) and the higher-order polynomial bounds
    ([HPolyBound]) are those of the cost model ([HOBounds]), at the types
    [bits σ]: the ground type is [N], whose size is the length of its
    binary representation ([N.size_nat]). At [N], a bound [m] majorizes a
    number of length at most [m].

    The denotation of a term is its closure conversion ([Lambda]), whose
    complexity follows from the axioms of the combinators. The proof is by
    induction on the terms, in an environment of majorized values
    ([interp_hpoly]): the majorant of a term is the term itself, with each
    constant replaced by its majorant ([BFFComplexity]; for the recursion
    `R`, the bound of [R_cost_bound] in the majorants of `F` and `h`), and
    the costs of the combinators added ([plus_t]).

    The theorem is about terms, not functionals: a complexity is that of a
    program. A functional equal to a BFF ([is_BFF]) may be computed by
    other, slower programs. Every BFF also has a bound on
    sized arguments ([BFF_hpolyS]). *)

From Complexity Require Export BFFComplexity SOPoly.
From Stdlib Require Import NArith.
From Stdlib Require List.
Import List.ListNotations.
Open Scope list_scope.

(** ** Complexities *)

(** The type of the complexities of the functionals of type [σ], and of the
    environments of [Γ]. *)
Fixpoint cty (σ : ty) : Type :=
  match σ with tN => unit | σ ⇒ τ => ℂI (den σ) (cty σ) -> ℂO (cty τ) end.

Fixpoint cenv (Γ : list ty) : Type :=
  match Γ with [] => unit | σ :: Γ => cenv Γ * cty σ end.

(** [norm_types] unfolds the types of the functionals ([den], [cty]) at
    known types. The same term can be elaborated with [den (tN ⇒ tN)] or
    [N -> N], with [cty σ] folded or not; [lia] compares terms
    syntactically, so it needs them normalized. *)
Ltac norm_types := cbn [sem cty] in *.

Module BFFFeasibility (Import M : TimeCostModel).

  Module BC := BFFComplexity M.
  Import BC.

  (** The types of PV^ω as higher-order types ([HOBounds]): the ground type
      is [N], whose size is the length [N.size_nat]. *)
  Fixpoint bits (σ : ty) : HigherOrder σ (den σ) (cty σ) :=
    match σ return HigherOrder σ (den σ) (cty σ) with
    | tN => ho_ground Repr_N N.size_nat
    | σ ⇒ τ => ho_arr (bits σ) (bits τ)
    end.

  Definition repr (σ : ty) : Repr (den σ) (cty σ) := ho_repr (bits σ).

  Fixpoint renv (Γ : list ty) : Repr (envT N Γ) (cenv Γ) :=
    match Γ return Repr (envT N Γ) (cenv Γ) with
    | [] => Repr_unit
    | σ :: Γ => Repr_env (renv Γ) (repr σ)
    end.

  (** [f] has the complexity [c], at type [σ]; [f], a function of the
      environments of [Γ], has the complexity [c]. *)
  Definition CBound (σ : ty) (f : den σ) (c : cty σ) : Prop :=
    @ComplexityBound (den σ) (@repr_ctype _ _ (repr σ)) (repr σ) f c.

  Definition CBoundE Γ σ (f : envT N Γ -> den σ) (c : ℂI (envT N Γ) (cenv Γ) -> ℂO (cty σ)) :=
    @ComplexityBound _ (@repr_ctype _ _ (Repr_arr (renv Γ) (repr σ))) (Repr_arr (renv Γ) (repr σ)) f c.

  Ltac simpl_c := cbv [app cost_add fmap ret_I ret cost res val pot] in *; autounfold with costs in *.

  Global Instance zero_hpoly : HPolyBound (bits tN) 0%N.
  Proof. refine (hpoly_intro _ _ (db <{ 0 }>) _ (N_complexity 0) _). cbn. lia. Qed.

  Global Instance s0_hpoly : HPolyBound (bits (tN ⇒ tN)) s0.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a, a + 7 }>) _ s0_complexity _). simpl_hp.
    intros x cx a _ Hx. cbn in *. pose proof (size_s0 x). lia.
  Qed.

  Global Instance s1_hpoly : HPolyBound (bits (tN ⇒ tN)) s1.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a, a + 7 }>) _ s1_complexity _). simpl_hp.
    intros x cx a _ Hx. cbn in *. pose proof (size_s1 x). lia.
  Qed.

  Global Instance tr_hpoly : HPolyBound (bits (tN ⇒ tN)) tr.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a, a + 3 }>) _ tr_complexity _). simpl_hp.
    intros x cx a _ Hx. cbn in *. pose proof (size_tr x). lia.
  Qed.

  Global Instance par_hpoly : HPolyBound (bits (tN ⇒ tN)) par.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a, a + 3 }>) _ par_complexity _). simpl_hp.
    intros x cx a _ Hx. cbn in *. pose proof (size_par x). lia.
  Qed.

  Global Instance pad_hpoly : HPolyBound (bits (tN ⇒ tN ⇒ tN)) pad.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a b, a + 43 * b + 13 }>) _ pad_complexity _). simpl_hp.
    intros x cx a _ Hx. split; [cbn; lia|].
    intros y cy b _ Hy. cbn in *. pose proof (size_pad x y). lia.
  Qed.

  Global Instance chop_hpoly : HPolyBound (bits (tN ⇒ tN ⇒ tN)) chop.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a b, a + 39 * b + 13 }>) _ chop_complexity _). simpl_hp.
    intros x cx a _ Hx. split; [cbn; lia|].
    intros y cy b _ Hy. cbn in *. pose proof (size_chop x y). lia.
  Qed.

  Global Instance smash_hpoly : HPolyBound (bits (tN ⇒ tN ⇒ tN)) smash.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a b, b * (44 * a + 62) + 14 }>) _ smash_complexity _).
    simpl_hp. intros x cx a _ Hx. split; [cbn; lia|].
    intros y cy b _ Hy. cbn in *. pose proof (size_smash x y). nia.
  Qed.

  Global Instance cond_hpoly : HPolyBound (bits (tN ⇒ tN ⇒ tN ⇒ tN)) cond.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ a b c, b + c + 21 }>) _ cond_complexity _). simpl_hp.
    intros x cx a _ Hx. split; [cbn; lia|].
    intros y cy b _ Hy. split; [cbn; lia|].
    intros z cz c _ Hz. cbn in *. pose proof (size_cond x y z). lia.
  Qed.

  Global Instance R_hpoly : HPolyBound (bits (tN ⇒ (tN ⇒ tN ⇒ tN) ⇒ (tN ⇒ tN) ⇒ tN ⇒ tN)) R.
  Proof.
    refine (hpoly_intro _ _ (db <{ λ am mF mh wm,
      wm * (mF wm 0 + mF wm (am + mh wm) + mh wm + 53 * mh wm + 195) + 31 + (am + mh wm) }>)
      _ R_complexity _).
    simpl_hp.
    intros a ca am _ Ha. split; [cbn; lia|].
    intros F cF mF HmF HF. split; [cbn; lia|].
    intros h ch mh Hmh Hh. split; [cbn; lia|].
    intros w cw wm _ Hw. cbn [maj bits baseM] in *. simpl_c.
    assert (HF' : forall w r, cost (cF (w ⋊ tt)) + cost (res (cF (w ⋊ tt)) (r ⋊ tt))
                              <= mF (N.size_nat w) 0 + mF (N.size_nat w) (N.size_nat r)).
    { intros w' r. destruct (HF w' tt (N.size_nat w') (le_n _) (le_n _)) as [H1 H2].
      destruct (H2 r tt (N.size_nat r) (le_n _) (le_n _)) as [H3 _]. cbn in *. simpl_c. lia. }
    assert (Hh' : forall w, cost (ch (w ⋊ tt)) <= mh (N.size_nat w)).
    { intro w'. destruct (Hh w' tt (N.size_nat w') (le_n _) (le_n _)) as [H1 _]. exact H1. }
    assert (Hl' : forall w, N.size_nat (h w) <= mh (N.size_nat w)).
    { intro w'. destruct (Hh w' tt (N.size_nat w') (le_n _) (le_n _)) as [_ H2]. exact H2. }
    assert (MF : forall n n' m m', n <= n' -> m <= m' -> mF n 0 + mF n m <= mF n' 0 + mF n' m').
    { intros n n' m m' Hn Hm. pose proof (HmF _ _ Hn 0 0 (le_n 0)). pose proof (HmF _ _ Hn _ _ Hm).
      cbn in *. lia. }
    pose proof (R_cost_bound a F h cF ch (fun n m => mF n 0 + mF n m) mh mh
                  HF' Hh' Hl' MF Hmh Hmh w) as HR.
    unfold step_bound in HR.
    pose proof (Hmh _ _ Hw). pose proof (HmF _ _ Hw 0 0 (le_n 0)).
    cbn in *.
    assert (mF (N.size_nat w) (Nat.max (N.size_nat a) (mh (N.size_nat w))) <=
            mF wm (am + mh wm)) by (apply HmF; lia).
    assert (mF (N.size_nat w) 0 + mF (N.size_nat w) (Nat.max (N.size_nat a) (mh (N.size_nat w)))
            + mh (N.size_nat w) + 53 * mh (N.size_nat w) + 195 <=
            mF wm 0 + mF wm (am + mh wm) + mh wm + 53 * mh wm + 195) by lia.
    pose proof (Nat.mul_le_mono _ _ _ _ Hw H2). pose proof (size_R a F h w).
    pose proof (Hl' w). cbn in *. simpl_c. split; lia.
  Qed.

  Lemma pv_hpoly σ (c : pv σ) : HPolyBound (bits σ) (cinterp σ c).
  Proof. destruct c; exact _. Qed.

  (** ** Open terms

      The denotation of a term [t] in the context [Γ] is a function of the
      environments of [Γ] ([interp]). Its majorant is a higher-order
      polynomial [p] in the same context, which majorizes it in every
      environment of values majorized by monotone functionals
      ([maj_open]). *)
  Fixpoint maj_env (Γ : list ty) : envT N Γ -> cenv Γ -> envT nat Γ -> Prop :=
    match Γ with
    | [] => fun _ _ _ => True
    | σ :: Γ => fun e ce me =>
        maj_env Γ (etl e) (fst ce) (etl me) /\ monotone σ (ehd me) /\ maj (bits σ) (ehd e) (snd ce) (ehd me)
    end.

  Lemma maj_env_mono Γ e ce me : maj_env Γ e ce me -> rel_env mle Γ me me.
  Proof.
    revert e ce me; induction Γ as [|σ Γ IH]; intros e ce me He; [exact I|].
    destruct He as (He & Hm & _). exact (conj (IH _ _ _ He) Hm).
  Qed.

  Definition maj_open Γ σ (f : envT N Γ -> den σ) (c : ℂI (envT N Γ) (cenv Γ) -> ℂO (cty σ))
    (p : term hpc Γ σ) : Prop :=
    forall e ce me, maj_env Γ e ce me ->
      cost (c (e ⋊ ce)) <= baseM σ (interp p me) /\ maj (bits σ) (f e) (res (c (e ⋊ ce))) (interp p me).

  (** Variables: [lookup x] costs at most [k], and gives the complexity of
      the variable in the environment. *)
  Fixpoint clookup {Γ σ} (x : var Γ σ) : cenv Γ -> cty σ :=
    match x in var Γ σ return cenv Γ -> cty σ with
    | vz => snd
    | vs x => fun ce => clookup x (fst ce)
    end.

  Lemma lookup_complexity Γ σ (x : var Γ σ) :
    exists c k, CBoundE Γ σ (lookup x) c /\
      forall e ce, cost (c (e ⋊ ce)) <= k /\ res (c (e ⋊ ce)) = clookup x ce.
  Proof.
    induction x as [Γ σ|Γ σ τ x IH].
    - eexists. exists 1. split; [exact (@ehd_complexity _ _ _ _ (renv Γ) (repr σ))|].
      intros e ce. split; reflexivity.
    - destruct IH as (c & k & C & Hc). eexists. exists (2 + k). split.
      + exact (@compose_complexity _ _ _ _ _ _ (renv (τ :: Γ)) (renv Γ) (repr σ) (lookup x) c etl _
                 C (@etl_complexity _ _ _ _ (renv Γ) (repr τ))).
      + intros e ce. destruct (Hc (@etl (envT N Γ) (den τ) e) (@fst (cenv Γ) (cty τ) ce)) as [Hk Hr].
        simpl_c. split; [cbn [Nat.add]; apply le_n_S, le_n_S, Hk | exact Hr].
  Qed.

  Lemma maj_lookup Γ σ (x : var Γ σ) e ce me : maj_env Γ e ce me ->
    monotone σ (lookup x me) /\ maj (bits σ) (lookup x e) (clookup x ce) (lookup x me).
  Proof.
    revert e ce me. induction x as [Γ σ|Γ σ τ x IH]; intros e ce me He;
      [exact (proj2 He) | exact (IH _ _ _ (proj1 He))].
  Qed.

  Lemma interp_hpoly Γ σ (t : term pv Γ σ) :
    exists c p, CBoundE Γ σ (interp t) c /\ maj_open Γ σ (interp t) c p.
  Proof.
    induction t as [Γ σ x|Γ σ c|Γ σ τ t IH|Γ σ τ t IHt u IHu].
    - (* variable *)
      destruct (lookup_complexity Γ σ x) as (c & k & C & Hc).
      exists c, (tapp (tapp (plus_t σ) (tcst (hnum k))) (tvar x)). split; [exact C|].
      intros e ce me He. destruct (Hc e ce) as [Hk ->]. destruct (maj_lookup Γ σ x e ce me He).
      change (interp (tapp (tapp (plus_t σ) (tcst (hnum k))) (tvar x)) me)
        with (interp (plus_t σ) me k (lookup x me)).
      rewrite baseM_plus_t. split; [lia | apply maj_plus; assumption].
    - (* constant *)
      destruct (pv_hpoly σ c) as (cc & p & C & J).
      exists (fun _ => 1 ⋉ cc), (tapp (tapp (plus_t σ) (tcst (hnum 1))) (wk p)). split.
      + exact (@apply_complexity _ _ _ _ (repr σ) (Repr_arr (renv Γ) (repr σ)) (cinterp σ c) Kc cc _
                 C (@Kc_complexity _ _ _ _ (repr σ) (renv Γ))).
      + intros e ce me He.
        change (interp (tapp (tapp (plus_t σ) (tcst (hnum 1))) (wk p)) me)
          with (interp (plus_t σ) me 1 (interp (wk p) me)).
        rewrite baseM_plus_t. split; [cbn; lia|].
        apply maj_plus, (maj_mle _ _ _ _ _ J), mle_wk.
    - (* λ-abstraction *)
      destruct IH as (c & p & C & J).
      eexists. exists (tlam (tapp (tapp (plus_t τ) (tcst (hnum 1))) p)). split.
      + exact (@apply_complexity _ _ _ _ (Repr_arr (renv (σ :: Γ)) (repr τ))
                 (Repr_arr (renv Γ) (Repr_arr (repr σ) (repr τ))) (interp t) Lam c _
                 C (@Lam_complexity _ _ _ _ _ _ (renv Γ) (repr σ) (repr τ))).
      + intros e ce me He. simpl_c. split.
        * cbn [baseM]. change (interp (tlam _) me (botM σ)) with
            (interp (plus_t τ (Γ := σ :: Γ)) (ECons me (botM σ)) 1 (interp p (ECons me (botM σ)))).
          rewrite baseM_plus_t. lia.
        * intros x cx a Ha Hx. destruct (J (ECons e x) (ce, cx) (ECons me a) (conj He (conj Ha Hx)))
            as [Jc Jm].
          change (interp (tlam _) me a) with
            (interp (plus_t τ (Γ := σ :: Γ)) (ECons me a) 1 (interp p (ECons me a))).
          rewrite baseM_plus_t. simpl_c. split; [cbn [Nat.add]; apply le_n_S, Jc | apply maj_plus, Jm].
    - (* application *)
      destruct IHt as (ct & pt & Ct & Jt). destruct IHu as (cu & pu & Cu & Ju).
      (* the costs of [t], of [u] and of the application *)
      set (k := tapp (tapp (tcst hadd) (tapp (tapp (tcst hadd) (tcst (hnum 1)))
                                             (tapp (base_t (σ ⇒ τ)) pt)))
                     (tapp (base_t σ) pu)).
      eexists. exists (tapp (tapp (plus_t τ) k) (tapp pt pu)). split.
      + exact (@apply_complexity _ _ _ _ (Repr_arr (renv Γ) (repr σ)) (Repr_arr (renv Γ) (repr τ))
                 (interp u) (Sc (interp t)) cu _ Cu
                 (@apply_complexity _ _ _ _ (Repr_arr (renv Γ) (repr (σ ⇒ τ)))
                    (Repr_arr (Repr_arr (renv Γ) (repr σ)) (Repr_arr (renv Γ) (repr τ)))
                    (interp t) Sc ct _ Ct
                    (@Sc_complexity _ _ _ _ _ _ (renv Γ) (repr σ) (repr τ)))).
      + intros e ce me He. pose proof (maj_env_mono _ _ _ _ He) as Hme.
        pose proof (mle_interp _ _ pt _ _ Hme) as Mt. pose proof (mle_interp _ _ pu _ _ Hme) as Mu.
        destruct (Jt e ce me He) as [Jtc Jtm]. destruct (Ju e ce me He) as [Juc Jum].
        destruct (Jtm _ _ _ Mu Jum) as [Jac Jam].
        change (interp (tapp (tapp (plus_t τ) k) (tapp pt pu)) me) with
          (interp (plus_t τ) me (interp k me) (interp pt me (interp pu me))).
        change (interp k me) with
          (1 + interp (base_t (σ ⇒ τ)) me (interp pt me) + interp (base_t σ) me (interp pu me)).
        rewrite baseM_plus_t, !base_t_baseM by assumption. simpl_c. split; [lia | apply maj_plus, Jam].
  Qed.

  (** ** The theorem *)

  Theorem BFF_hpoly_bound σ (t : term pv [] σ) : HPolyBound (bits σ) ⟦t⟧.
  Proof.
    destruct (interp_hpoly [] σ t) as (c & p & C & J).
    exists (res (c (tt ⋊ tt))), p. split.
    - exact (@apply_complexity _ _ _ _ Repr_unit (repr σ) tt (interp t) tt c tt_complexity C).
    - exact (proj2 (J tt tt tt I)).
  Qed.

  (** Every basic feasible functional has a bound on sized arguments. *)
  Corollary BFF_hpolyS σ (t : term pv [] σ) : HPolyBoundS (bits σ) ⟦t⟧.
  Proof. exact (hpoly_hpolyS _ _ (BFF_hpoly_bound _ t)). Qed.

  (** At type [N ⇒ N]: the cost of [⟦t⟧ x] and the length of its value are
      bounded by a higher-order polynomial of type [N ⇒ N] in the length of
      [x]. *)
  Corollary BFF1_hpoly_bound (t : term pv [] (tN ⇒ tN)) :
    exists c (p : hpoly (tN ⇒ tN)), CBound (tN ⇒ tN) ⟦t⟧ c /\
      forall x, cost (c (x ⋊ tt)) <= ⟦p⟧ (N.size_nat x) /\ N.size_nat (⟦t⟧ x) <= ⟦p⟧ (N.size_nat x).
  Proof.
    destruct (BFF_hpoly_bound _ t) as (c & p & C & J).
    exists c, p. split; [exact C|].
    intro x. exact (J x tt (N.size_nat x) (le_n _) (le_n _)).
  Qed.

  (** At type [(N ⇒ N) ⇒ N ⇒ N]: let `a` be a monotone bound on the costs
      of the argument [f] (with complexity [cf]) and on the lengths of its
      values, in the length of their arguments. The cost of [⟦t⟧ f x] (the
      application to [f], then to [x]) and the length of its value are
      bounded by a higher-order polynomial of type 2 in `a` and the length
      of [x].

      The higher-order polynomial is bounded by a second-order polynomial
      ([BFF2_sopoly_bound]). *)
  Corollary BFF2_hpoly_bound (t : term pv [] ((tN ⇒ tN) ⇒ tN ⇒ tN)) :
    exists c (p : hpoly ((tN ⇒ tN) ⇒ tN ⇒ tN)), CBound _ ⟦t⟧ c /\
      forall (f : N -> N) (cf : ℂI N unit -> ℂO unit) (a : nat -> nat),
      (forall n n', n <= n' -> a n <= a n') ->
      (forall x, cost (cf (x ⋊ tt)) <= a (N.size_nat x) /\ N.size_nat (f x) <= a (N.size_nat x)) ->
      forall x,
        cost (c (f ⋊ cf)) + cost (res (c (f ⋊ cf)) (x ⋊ tt)) <= 2 * ⟦p⟧ a (N.size_nat x) /\
        N.size_nat (⟦t⟧ f x) <= ⟦p⟧ a (N.size_nat x).
  Proof.
    destruct (BFF_hpoly_bound _ t) as (c & p & C & J).
    exists c, p. split; [exact C|].
    intros f cf a Ha Hf x.
    assert (Hmaj : maj (bits (tN ⇒ tN)) f cf a).
    { intros y [] m _ Hy. destruct (Hf y) as [H1 H2]. pose proof (Ha _ _ Hy). cbn. lia. }
    destruct (J f cf a Ha Hmaj) as [Hc Hm].
    destruct (Hm x tt (N.size_nat x) (le_n _) (le_n _)) as [Hx Hl].
    (* the cost of the application to [f] is the value at [0] *)
    assert (Hp : ⟦p⟧ a 0 <= ⟦p⟧ a (N.size_nat x))
      by exact (hpoly_monotone _ p a a Ha 0 (N.size_nat x) (Nat.le_0_l _)).
    change (baseM (tN ⇒ tN) (⟦p⟧ a)) with (⟦p⟧ a 0) in Hc.
    change (baseM tN (⟦p⟧ a (N.size_nat x))) with (⟦p⟧ a (N.size_nat x)) in Hx.
    split; [| exact Hl].
    eapply Nat.le_trans; [exact (Nat.add_le_mono _ _ _ _ Hc Hx) | lia].
  Qed.

  (** The same bound with a second-order polynomial in `a` and the length
      of [x], as Kapron and Cook's: [p] is a second-order polynomial
      ([hpoly_sopoly]). Their bound is in the
      length function of [f] only, with oracle calls cheap, whereas `a`
      also bounds the cost of [f]. *)
  Corollary BFF2_sopoly_bound (t : term pv [] ((tN ⇒ tN) ⇒ tN ⇒ tN)) :
    exists c (q : sopoly), CBound _ ⟦t⟧ c /\
      forall (f : N -> N) (cf : ℂI N unit -> ℂO unit) (a : nat -> nat),
      (forall n n', n <= n' -> a n <= a n') ->
      (forall x, cost (cf (x ⋊ tt)) <= a (N.size_nat x) /\ N.size_nat (f x) <= a (N.size_nat x)) ->
      forall x,
        cost (c (f ⋊ cf)) + cost (res (c (f ⋊ cf)) (x ⋊ tt)) <= 2 * soeval q a (N.size_nat x) /\
        N.size_nat (⟦t⟧ f x) <= soeval q a (N.size_nat x).
  Proof.
    destruct (BFF2_hpoly_bound t) as (c & p & C & J).
    destruct (hpoly_sopoly p) as [q Hq].
    exists c, q. split; [exact C|].
    intros f cf a Ha Hf x. destruct (J f cf a Ha Hf x) as [H1 H2].
    rewrite Hq in H1, H2. split; [exact H1 | exact H2].
  Qed.
End BFFFeasibility.
