(** * Higher-order polynomial bounds

    [Bounds] bounds first-order functions by polynomials in the sizes of
    their arguments. At higher types, the arguments are themselves
    functions: they are measured by majorants, functionals over the sizes,
    and the bounds are higher-order polynomials ([HOPoly]). *)

From Complexity Require Import CostModelCore Bounds Poly HOPoly.
From Stdlib Require Import List Lia.
Import ListNotations.

Module HOBounds (Import CM : BoundsCore).
  (** ** Higher-order types

      [HigherOrder σ A CA]: [A] is a type of functionals of shape [σ],
      built from base types with a representation and a size ([Size]), and
      [CA] the type of their complexities. A value of a base type is
      measured by its size: the bounds hold for all its complexities. *)

  Inductive HigherOrder : ty -> Type -> Type -> Type :=
  | ho_ground {A CA} (RA : Repr A CA) : Size A -> HigherOrder tN A CA
  | ho_arr {σ τ A CA B CB} : HigherOrder σ A CA -> HigherOrder τ B CB ->
      HigherOrder (σ ⇒ τ) (A -> B) (ℂI A CA -> ℂO CB).

  Fixpoint ho_repr {σ A CA} (h : HigherOrder σ A CA) : Repr A CA :=
    match h in HigherOrder σ A CA return Repr A CA with
    | ho_ground RA _ => RA
    | ho_arr h1 h2 => Repr_arr (ho_repr h1) (ho_repr h2)
    end.

  (** [f] has the complexity [c]. *)
  Definition HOBound {σ A CA} (h : HigherOrder σ A CA) (f : A) (c : CA) : Prop :=
    @ComplexityBound A (@repr_ctype _ _ (ho_repr h)) f c.

  (** ** Majorization

      A logical relation over the types: at a ground type, a bound [m]
      majorizes a value of size at most [m]; at [σ ⇒ τ], [m] majorizes a
      function [f] of complexity [c] when, for every argument [x] majorized
      by a monotone [a], the cost of [f x] is at most the value of [m a] at
      [0]s ([baseM]), and [m a] majorizes [f x]. *)

  Fixpoint maj {σ A CA} (h : HigherOrder σ A CA) : A -> CA -> M σ -> Prop :=
    match h in HigherOrder σ A CA return A -> CA -> M σ -> Prop with
    | ho_ground _ s => fun x _ m => s x <= m
    | @ho_arr σ τ _ _ _ _ h1 h2 => fun f c m => forall x cx a, monotone σ a -> maj h1 x cx a ->
        cnat (cost (c (x ⋊ cx))) <= baseM τ (m a) /\ maj h2 (f x) (res (c (x ⋊ cx))) (m a)
    end.

  Lemma maj_mle {σ A CA} (h : HigherOrder σ A CA) f c m m' :
    maj h f c m -> mle σ m m' -> maj h f c m'.
  Proof.
    induction h as [A CA0 RA s|σ τ A CA B CB h1 _ h2 IH]; intros Hf Hm; cbn in *; [lia|].
    intros x cx a Ha Hx. destruct (Hf x cx a Ha Hx) as [Hc Hv].
    pose proof (Hm a a Ha). split; [pose proof (baseM_mono τ _ _ H); lia | exact (IH _ _ _ _ Hv H)].
  Qed.

  Lemma maj_plus {σ A CA} (h : HigherOrder σ A CA) Γ (e : envT nat Γ) y cy k m :
    maj h y cy m -> maj h y cy (interp (plus_t σ) e k m).
  Proof.
    revert Γ e y cy m; induction h as [A CA0 RA s|σ τ A CA B CB h1 _ h2 IH]; intros Γ e y cy m H.
    - rewrite interp_plus_tN. cbn in *. lia.
    - intros x cx a Ha Hx. destruct (H x cx a Ha Hx) as [Hc Hm]. rewrite interp_plus_arr.
      split; [rewrite baseM_plus_t; lia | apply IH, Hm].
  Qed.

  (** ** Higher-order polynomial bounds *)

  Class HPolyBound {σ A CA} (h : HigherOrder σ A CA) (f : A) : Prop :=
    hpoly_bound : exists (c : CA) (p : hpoly σ), HOBound h f c /\ maj h f c ⟦p⟧.

  (** The bound [p] comes before the proof obligations, so that it is
      elaborated with its type ([db]). *)
  Lemma hpoly_intro {σ A CA} (h : HigherOrder σ A CA) f (p : hpoly σ) c :
    HOBound h f c -> maj h f c ⟦p⟧ -> HPolyBound h f.
  Proof. intros C J. exists c, p. split; assumption. Qed.
  Arguments hpoly_intro & {σ A CA} h f p c _ _.

  (** ** Sizes

      The majorization quantifies over all the potentials of the
      arguments, even those that are not complexities of them; the sizes
      restrict them. Following Férée (Game semantics approach to
      higher-order complexity, JCSS 87:1-15, 2017), the size of a function
      bounds its dialogue with its arguments, the questions it asks and its
      answer, with the type of the complexities. Only what the function
      creates is charged: the values it receives are free, as in the cost
      model.

      [CSized h f s], with [s] of the type of a complexity of [f]: for all
      the arguments [xs] of [f], each sized by the complexity given with
      it, there is a finite certificate of questions to the arguments such
      that
      - the size of the answer [f xs], plus the weights of the questions,
        is at most the total cost of [s] on [xs] ([dcost]), plus the
        largest answer received ([recv]): the answer may copy it;
      - every list of arguments [xs'] of the same sizes that gives the
        same answers to these questions gives the same answer [f xs'].

      The weight of a question [zs] to an argument [x] of size [sx] is [1]
      plus the cost of [sx] on [zs]: the sub-dialogue that [f] triggers,
      in which [x] reads [zs]. Its answer is received, so it is free. A
      ground value is asked with no argument, for the weight [1]. So the
      size counts the number of questions, and their sizes through the
      sizes of the arguments (Férée, definition 13). Ground data carry no
      size bound (their complexities carry no information): a ground value
      is its own size. *)

  (** *** Dialogues *)

  (** The ground type of the answers, and its size. *)
  Fixpoint gty {σ A CA} (h : HigherOrder σ A CA) : Type :=
    match h with @ho_ground A _ _ _ => A | ho_arr _ h2 => gty h2 end.

  Fixpoint gsize {σ A CA} (h : HigherOrder σ A CA) : gty h -> nat :=
    match h as h0 return gty h0 -> nat with ho_ground _ s => s | ho_arr _ h2 => gsize h2 end.

  (** The arguments of a functional, each with its size. *)
  Fixpoint spine {σ A CA} (h : HigherOrder σ A CA) : Type :=
    match h with ho_ground _ _ => unit | @ho_arr _ _ A CA _ _ _ h2 => ℂI A CA * spine h2 end.

  (** The answer of [f] to the arguments [xs]. *)
  Fixpoint answer {σ A CA} (h : HigherOrder σ A CA) : A -> spine h -> gty h :=
    match h as h0 in HigherOrder σ A CA return A -> spine h0 -> gty h0 with
    | ho_ground _ _ => fun y _ => y
    | ho_arr _ h2 => fun f xs => answer h2 (f (val (fst xs))) (snd xs)
    end.

  (** The total cost of the complexity [s] on the arguments [xs]. *)
  Fixpoint dcost {σ A CA} (h : HigherOrder σ A CA) : CA -> spine h -> nat :=
    match h as h0 in HigherOrder σ A CA return CA -> spine h0 -> nat with
    | ho_ground _ _ => fun _ _ => 0
    | ho_arr _ h2 => fun s xs => cnat (cost (s (fst xs))) + dcost h2 (res (s (fst xs))) (snd xs)
    end.

  (** A certificate: questions to each argument, each question being the
      arguments of the argument asked. *)
  Fixpoint cert {σ A CA} (h : HigherOrder σ A CA) : Type :=
    match h with ho_ground _ _ => unit | ho_arr h1 h2 => list (spine h1) * cert h2 end.

  (** The weight of the question [zs] to the argument [x]: the
      sub-dialogue it triggers. *)
  Definition qweight {σ A CA} (h : HigherOrder σ A CA) (x : ℂI A CA) (zs : spine h) : nat :=
    S (dcost h (pot x) zs).

  Fixpoint cweight {σ A CA} (h : HigherOrder σ A CA) : spine h -> cert h -> nat :=
    match h as h0 return spine h0 -> cert h0 -> nat with
    | ho_ground _ _ => fun _ _ => 0
    | ho_arr h1 h2 => fun xs q =>
        list_sum (map (qweight h1 (fst xs)) (fst q)) + cweight h2 (snd xs) (snd q)
    end.

  (** The largest answer received, to the questions of [q]. *)
  Fixpoint recv {σ A CA} (h : HigherOrder σ A CA) : spine h -> cert h -> nat :=
    match h as h0 return spine h0 -> cert h0 -> nat with
    | ho_ground _ _ => fun _ _ => 0
    | ho_arr h1 h2 => fun xs q =>
        Nat.max (list_max (map (fun zs => gsize h1 (answer h1 (val (fst xs)) zs)) (fst q)))
          (recv h2 (snd xs) (snd q))
    end.

  (** [xs'] has the sizes of [xs], and the same answers to the questions of
      [q]. *)
  Fixpoint agree_on {σ A CA} (h : HigherOrder σ A CA) : cert h -> spine h -> spine h -> Prop :=
    match h as h0 return cert h0 -> spine h0 -> spine h0 -> Prop with
    | ho_ground _ _ => fun _ _ _ => True
    | ho_arr h1 h2 => fun q xs xs' =>
        pot (fst xs') = pot (fst xs) /\
        Forall (fun zs => answer h1 (val (fst xs')) zs = answer h1 (val (fst xs)) zs) (fst q) /\
        agree_on h2 (snd q) (snd xs) (snd xs')
    end.

  (** *** Size

      At each type, three predicates, defined together by recursion on the
      type: [lsized] is the size ([CSized]); [lspine] holds of the
      arguments sized by their potentials; [lcert] of the certificates
      whose questions are sized. *)
  Record level {σ A CA} (h : HigherOrder σ A CA) : Type := {
    lsized : A -> CA -> Prop;
    lspine : spine h -> Prop;
    lcert : cert h -> Prop }.
  Arguments lsized {σ A CA h}. Arguments lspine {σ A CA h}. Arguments lcert {σ A CA h}.

  Fixpoint lev {σ A CA} (h : HigherOrder σ A CA) : level h :=
    match h as h0 return level h0 with
    | ho_ground _ _ =>
        {| lsized := fun _ _ => True; lspine := fun _ => True; lcert := fun _ => True |}
    | ho_arr h1 h2 =>
        let sp xs := lsized (lev h1) (val (fst xs)) (pot (fst xs)) /\ lspine (lev h2) (snd xs) in
        let cq q := Forall (lspine (lev h1)) (fst q) /\ lcert (lev h2) (snd q) in
        @Build_level _ _ _ (ho_arr h1 h2)
          (fun f s => forall xs, sp xs -> exists q, cq q /\
             gsize (ho_arr h1 h2) (answer (ho_arr h1 h2) f xs) + cweight (ho_arr h1 h2) xs q
               <= dcost (ho_arr h1 h2) s xs + recv (ho_arr h1 h2) xs q /\
             forall xs', sp xs' -> agree_on (ho_arr h1 h2) q xs xs' ->
               answer (ho_arr h1 h2) f xs' = answer (ho_arr h1 h2) f xs)
          sp cq
    end.

  (** [s] is a size bound of [f]: same type as a complexity of [f]. *)
  Definition CSized {σ A CA} (h : HigherOrder σ A CA) : A -> CA -> Prop := lsized (lev h).

  (** ** Sized arguments

      [HPolyBoundS] is [HPolyBound] on the arguments with a size bound, in
      their complexities and their sizes, kept apart; every [HPolyBound] is
      one ([hpoly_hpolyS]).

      [smaj h f c m]: [f] of complexity [c] is majorized by [m] on the
      arguments with a size bound. Each argument [x] comes with its
      complexity [cx], majorized by [a] as in [maj], and with a size bound
      [sx] ([CSized]), majorized by [b]: the two are kept apart, and [m]
      takes both. The majorants of [smaj] have the shape [dbl σ], where
      each argument type is doubled. *)
  Fixpoint dbl (σ : ty) : ty := match σ with tN => tN | σ ⇒ τ => σ ⇒ σ ⇒ dbl τ end.

  Fixpoint smaj {σ A CA} (h : HigherOrder σ A CA) : A -> CA -> M (dbl σ) -> Prop :=
    match h in HigherOrder σ A CA return A -> CA -> M (dbl σ) -> Prop with
    | ho_ground _ s => fun x _ m => s x <= m
    | @ho_arr σ τ _ _ _ _ h1 h2 => fun f c m =>
        forall x cx a sx b, monotone σ a -> monotone σ b ->
        maj h1 x cx a -> CSized h1 x sx -> maj h1 x sx b ->
        cnat (cost (c (x ⋊ cx))) <= baseM (dbl τ) (m a b) /\ smaj h2 (f x) (res (c (x ⋊ cx))) (m a b)
    end.

  Lemma smaj_mle {σ A CA} (h : HigherOrder σ A CA) f c m m' :
    smaj h f c m -> mle (dbl σ) m m' -> smaj h f c m'.
  Proof.
    revert f c m m'; induction h as [A CA0 RA s|σ τ A CA B CB h1 _ h2 IH]; intros f c m m' Hf Hm;
      cbn in *; [lia|].
    intros x cx a sx b Ha Hb Hx Hs Hsb. destruct (Hf x cx a sx b Ha Hb Hx Hs Hsb) as [Hc Hv].
    pose proof (Hm a a Ha b b Hb) as H. split; [pose proof (baseM_mono _ _ _ H); lia | exact (IH _ _ _ _ Hv H)].
  Qed.

  (** [f] has a higher-order polynomial bound on the arguments with a size
      bound: in their complexities and in their sizes. *)
  Definition HPolyBoundS {σ A CA} (h : HigherOrder σ A CA) (f : A) : Prop :=
    exists (c : CA) (p : hpoly (dbl σ)), HOBound h f c /\ smaj h f c ⟦p⟧.

  (** As [hpoly_intro], the bound [p] first. *)
  Lemma hpoly_introS {σ A CA} (h : HigherOrder σ A CA) f (p : hpoly (dbl σ)) c :
    HOBound h f c -> smaj h f c ⟦p⟧ -> HPolyBoundS h f.
  Proof. intros C J. exists c, p. split; assumption. Qed.
  Arguments hpoly_introS & {σ A CA} h f p c _ _.

  (** *** From [maj] to [smaj]

      A majorant that ignores the sizes ([dropM]): every majorization is
      one ([maj_smaj]), and so is every higher-order polynomial bound
      ([hpoly_hpolyS]), through the term [drop_t]. *)
  Fixpoint dropM (σ : ty) : M σ -> M (dbl σ) :=
    match σ return M σ -> M (dbl σ) with
    | tN => fun m => m
    | σ ⇒ τ => fun m a _ => dropM τ (m a)
    end.

  Fixpoint drop_t (σ : ty) {Γ} : term hpc Γ (σ ⇒ dbl σ) :=
    match σ with
    | tN => tlam (tvar vz)
    | σ ⇒ τ => tlam (tlam (tlam (tapp (drop_t τ) (tapp (tvar (vs (vs vz))) (tvar (vs vz))))))
    end.

  Lemma mle_drop σ Γ (e : envT nat Γ) m m' :
    mle σ m m' -> mle (dbl σ) (dropM σ m) (interp (drop_t σ) e m').
  Proof.
    revert Γ e m m'; induction σ as [|σ _ τ IH]; intros Γ e m m' Hm; [exact Hm|].
    intros a a' Ha b b' _. cbn. apply IH, Hm, Ha.
  Qed.

  Lemma baseM_drop σ m : baseM (dbl σ) (dropM σ m) = baseM σ m.
  Proof. revert m; induction σ as [|σ _ τ IH]; intros m; [reflexivity | apply IH]. Qed.

  Lemma maj_smaj {σ A CA} (h : HigherOrder σ A CA) f c m : maj h f c m -> smaj h f c (dropM σ m).
  Proof.
    revert f c m; induction h as [A CA0 RA s|σ τ A CA B CB h1 _ h2 IH]; intros f c m H; [exact H|].
    intros x cx a sx b Ha _ Hx _ _. destruct (H x cx a Ha Hx) as [H1 H2]. cbn [dropM].
    split; [rewrite baseM_drop; exact H1 | exact (IH _ _ _ H2)].
  Qed.

  Lemma hpoly_hpolyS {σ A CA} (h : HigherOrder σ A CA) f : HPolyBound h f -> HPolyBoundS h f.
  Proof.
    intros (c & p & Hc & Hm). exists c, (tapp (drop_t σ) p). split; [exact Hc|].
    apply (smaj_mle _ _ _ _ _ (maj_smaj _ _ _ _ Hm)). exact (mle_drop σ [] tt _ _ (hpoly_monotone σ p)).
  Qed.

  (** ** First-order functions

      A first-order type ([FirstOrder]) is a higher-order type of order 1
      ([fo_ho]), and its higher-order polynomial bounds give polynomial
      bounds ([hpoly_polynomial]), also with smaller sizes ([fo_below]): a
      higher-order polynomial of order 1 is at most [k * (1 + s) ^ d] in the
      sum [s] of its arguments ([pgrowth]), and so are the costs that it
      majorizes. *)
  Fixpoint fo_ty {A CA} (fo : FirstOrder A CA) : ty :=
    match fo with fo_res _ _ => tN | fo_arg _ _ fo => tN ⇒ fo_ty fo end.

  Fixpoint fo_ho {A CA} (fo : FirstOrder A CA) : HigherOrder (fo_ty fo) A CA :=
    match fo as fo0 in FirstOrder A CA return HigherOrder (fo_ty fo0) A CA with
    | fo_res RB SB => ho_ground RB SB
    | fo_arg RA SA fo => ho_arr (ho_ground RA SA) (fo_ho fo)
    end.

  Fixpoint fo_arity {A CA} (fo : FirstOrder A CA) : nat :=
    match fo with fo_res _ _ => 0 | fo_arg _ _ fo => S (fo_arity fo) end.

  (** [fo_below fo h]: [h] is [fo] at order 1, with sizes at most those of
      [fo] ([fo_ho fo] for instance). *)
  Fixpoint fo_below {A CA} (fo : FirstOrder A CA) : HigherOrder (fo_ty fo) A CA -> Prop :=
    match fo as fo0 in FirstOrder A CA return HigherOrder (fo_ty fo0) A CA -> Prop with
    | @fo_res B CB RB SB => fun h => exists sB : Size B, h = ho_ground RB sB /\ forall x, sB x <= SB x
    | @fo_arg A CA B CB RA SA fo => fun h =>
        exists (sA : Size A) (h' : HigherOrder (fo_ty fo) B CB),
          h = ho_arr (ho_ground RA sA) h' /\ (forall x, sA x <= SA x) /\ fo_below fo h'
    end.

  Lemma fo_below_ho {A CA} (fo : FirstOrder A CA) : fo_below fo (fo_ho fo).
  Proof.
    induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; cbn.
    - exists SB. split; [reflexivity | intro; apply le_n].
    - exists SA, (fo_ho fo). split; [reflexivity | split; [intro; apply le_n | exact IH]].
  Qed.

  Lemma fo_below_repr {A CA} (fo : FirstOrder A CA) h : fo_below fo h -> ho_repr h = fo_repr fo.
  Proof.
    revert h. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros h Hh; cbn in Hh.
    - destruct Hh as (sB & -> & _). reflexivity.
    - destruct Hh as (sA & h' & -> & _ & Hh'). cbn. now rewrite (IH h' Hh').
  Qed.

  (** [diag fo m N]: [m] applied to [N] for every argument. *)
  Fixpoint diag {A CA} (fo : FirstOrder A CA) : M (fo_ty fo) -> nat -> nat :=
    match fo as fo0 in FirstOrder A CA return M (fo_ty fo0) -> nat -> nat with
    | fo_res _ _ => fun m _ => m
    | fo_arg _ _ fo => fun m N => diag fo (m N) N
    end.

  Lemma diag_mle {A CA} (fo : FirstOrder A CA) x y N : mle (fo_ty fo) x y -> diag fo x N <= diag fo y N.
  Proof.
    revert x y. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros x y H; cbn; [exact H|].
    apply IH, H, le_n.
  Qed.

  Lemma diag_mono {A CA} (fo : FirstOrder A CA) x N N' :
    monotone (fo_ty fo) x -> N <= N' -> diag fo x N <= diag fo x N'.
  Proof.
    revert x. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros x Hx HN; cbn; [apply le_n|].
    transitivity (diag fo (x N') N).
    - apply diag_mle, Hx, HN.
    - apply IH; [apply Hx, le_n | exact HN].
  Qed.

  Lemma baseM_diag {A CA} (fo : FirstOrder A CA) x N :
    monotone (fo_ty fo) x -> baseM (fo_ty fo) x <= diag fo x N.
  Proof.
    revert x. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros x Hx; cbn; [apply le_n|].
    transitivity (diag fo (x 0) N).
    - apply IH, Hx, le_n.
    - apply diag_mle, Hx. lia.
  Qed.

  Lemma diag_growth {A CA} (fo : FirstOrder A CA) (G : nat -> M (fo_ty fo)) :
    pgrowth (fo_ty fo) G -> exists k d, forall N, diag fo (G N) N <= k * (N + 1) ^ d.
  Proof.
    revert G. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros G HG; cbn.
    - exact HG.
    - apply (IH (fun n => G n n)), HG. exists 1, 1. intro n. rewrite Nat.pow_1_r. lia.
  Qed.

  (** The costs majorized by [m] are bounded by its diagonal. *)
  Lemma maj_size_costs {A CA} (fo : FirstOrder A CA) (h : HigherOrder (fo_ty fo) A CA) (f : A) (c : CA)
      (m : M (fo_ty fo)) k d ss :
    fo_below fo h -> monotone (fo_ty fo) m ->
    (forall N, diag fo m N <= k * (list_sum ss + N + 1) ^ d) ->
    maj h f c m ->
    size_costs fo (fun ss => k * (1 + list_sum ss) ^ d) ss c.
  Proof.
    revert h f c m ss. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros h f c m ss Hh Hm Hd Hf;
      cbn; [exact I|].
    destruct Hh as (sA & h' & -> & Hs & Hh').
    intro ca. set (s := size (Size := SA) (val ca)).
    destruct (Hf (val ca) (pot ca) s (le_n s) (Hs (val ca))) as [Hc Hr].
    change (val ca ⋊ pot ca) with ca in Hc, Hr.
    rewrite list_sum_app. cbn [list_sum fold_right]. split.
    - pose proof (baseM_diag fo (m s) s (Hm s s (le_n s))). specialize (Hd s). cbn in Hd.
      replace (S (list_sum ss + (s + 0))) with (list_sum ss + s + 1) by lia. lia.
    - apply (IH h' (f (val ca)) _ (m s)); [exact Hh' | apply Hm, le_n | | exact Hr].
      intro N. specialize (Hd (s + N)). cbn in Hd.
      transitivity (diag fo (m (s + N)) N); [apply diag_mle, Hm; lia|].
      transitivity (diag fo (m (s + N)) (s + N)); [apply diag_mono; [apply Hm, le_n | lia]|].
      rewrite list_sum_app. cbn [list_sum fold_right].
      replace (list_sum ss + (s + 0) + N + 1) with (list_sum ss + (s + N) + 1) by lia. exact Hd.
  Qed.

  (** Only the sizes of the arguments of [fo], at most [fo_arity fo], matter. *)
  Lemma size_costs_mono_len {A CA} (fo : FirstOrder A CA) (g g' : list nat -> nat) ss c :
    (forall ss', length ss' <= length ss + fo_arity fo -> g ss' <= g' ss') ->
    size_costs fo g ss c -> size_costs fo g' ss c.
  Proof.
    revert ss c. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros ss c Hg H; cbn in *; [exact I|].
    intro ca. destruct (H ca) as [H1 H2]. split.
    - eapply Nat.le_trans; [exact H1 | apply Hg; rewrite length_app; cbn; lia].
    - apply (IH (ss ++ [size (Size := SA) (val ca)]) (res (c ca))); [| exact H2].
      intros ss' Hl. apply Hg. rewrite length_app in Hl. cbn in Hl. lia.
  Qed.

  Theorem hpoly_polynomial {A CA} `{fo : FirstOrder A CA} (h : HigherOrder (fo_ty fo) A CA) (f : A) :
    fo_below fo h -> HPolyBound h f -> PolynomialBound f.
  Proof.
    intros Hh (c & p & Hc & Hm).
    destruct (diag_growth fo (fun _ => ⟦p⟧) (pgrowth_interp [] _ p (fun _ => tt) I)) as (k & d & Hg).
    exists (pmul (pconst k) (ppow (padd (pconst 1) (psum_from 0 (fo_arity fo))) d)), c. split.
    - unfold HOBound in Hc. rewrite (fo_below_repr fo h Hh) in Hc. exact Hc.
    - apply (size_costs_mono_len fo (fun ss => k * (1 + list_sum ss) ^ d)).
      + intros ss Hl. cbn [peval]. rewrite peval_psum_from. cbn [skipn].
        rewrite (firstn_all2 ss) by (cbn in Hl; lia). apply le_n.
      + apply (maj_size_costs fo h f c ⟦p⟧ k d []); [exact Hh | apply hpoly_monotone | | exact Hm].
        intro N. exact (Hg N).
  Qed.

  Corollary hpoly_polynomial_fo {A CA} `{fo : FirstOrder A CA} (f : A) :
    HPolyBound (fo_ho fo) f -> PolynomialBound f.
  Proof. apply hpoly_polynomial, fo_below_ho. Qed.
End HOBounds.
