(** * Higher-order polynomial bounds

    [Bounds] bounds first-order functions by polynomials in the sizes of
    their arguments. At higher types, the arguments are themselves
    functions: they are measured by majorants, functionals over the sizes,
    and the bounds are higher-order polynomials ([HOPoly]).

    [HigherOrder σ A CA]: [A] is a type of functionals of shape [σ], built
    from ground types with a representation ([Ground]) and a size ([Size]),
    and [CA] is the type of their complexities. Everything below is defined
    over such a description, whatever the ground types and their sizes.

    The majorization is a logical relation over the types ([maj]):
    - at a ground type, a bound [m] majorizes a value of size at most [m];
    - at [σ ⇒ τ], [m] majorizes a function [f] of complexity [c] when, for
      every argument [x] majorized by a monotone `a`, the cost of [f x] is
      at most the value of `m a` at [0]s ([baseM]), and `m a` majorizes
      [f x].
    [HPolyBound h f]: [f] has a complexity majorized by a higher-order
    polynomial.

    The majorization quantifies over all the potentials of the arguments,
    even those that are not complexities of them. The sizes ([CSized])
    restrict them. Following Férée, the size of a function bounds its
    dialogue with its arguments, the questions it asks them and its answer,
    and it has the type of the complexities. Only what the function creates
    is charged: the values it receives (the answers of its arguments) are
    free, as in the cost model, where moving a value costs nothing.
    [HPolyBoundS] is [HPolyBound] on the arguments with a size bound
    ([smaj]): in their complexities and their sizes, kept apart. Every
    [HPolyBound] is one ([hpoly_hpolyS]).

    H. Férée. Game semantics approach to higher-order complexity. JCSS
    87:1-15, 2017. *)

From Complexity Require Import CostModelCore HOPoly.
From Stdlib Require Import List Lia.
Import ListNotations.

Module HOBounds (Import CM : CostModelCore).

  (** ** Higher-order types *)

  Inductive HigherOrder : ty -> Type -> Type -> Type :=
  | ho_ground {A} : Ground A -> Size A -> HigherOrder tN A unit
  | ho_arr {σ τ A CA B CB} : HigherOrder σ A CA -> HigherOrder τ B CB ->
      HigherOrder (σ ⇒ τ) (A -> B) (ℂI A CA -> ℂO CB).

  Fixpoint ho_repr {σ A CA} (h : HigherOrder σ A CA) : Repr A CA :=
    match h in HigherOrder σ A CA return Repr A CA with
    | ho_ground RA _ => RA
    | ho_arr h1 h2 => Repr_arr (ho_repr h1) (ho_repr h2)
    end.

  (** [f] has the complexity [c]. *)
  Definition HOBound {σ A CA} (h : HigherOrder σ A CA) (f : A) (c : CA) : Prop :=
    @ComplexityBound A (@repr_ctype _ _ (ho_repr h)) (ho_repr h) f c.

  (** ** Majorization *)

  Fixpoint maj {σ A CA} (h : HigherOrder σ A CA) : A -> CA -> M σ -> Prop :=
    match h in HigherOrder σ A CA return A -> CA -> M σ -> Prop with
    | ho_ground _ s => fun x _ m => s x <= m
    | @ho_arr σ τ _ _ _ _ h1 h2 => fun f c m => forall x cx a, monotone σ a -> maj h1 x cx a ->
        cost (c (x ⋊ cx)) <= baseM τ (m a) /\ maj h2 (f x) (res (c (x ⋊ cx))) (m a)
    end.

  Lemma maj_mle {σ A CA} (h : HigherOrder σ A CA) f c m m' :
    maj h f c m -> mle σ m m' -> maj h f c m'.
  Proof.
    induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros Hf Hm; cbn in *; [lia|].
    intros x cx a Ha Hx. destruct (Hf x cx a Ha Hx) as [Hc Hv].
    pose proof (Hm a a Ha). split; [pose proof (baseM_mono τ _ _ H); lia | exact (IH _ _ _ _ Hv H)].
  Qed.

  Lemma maj_plus {σ A CA} (h : HigherOrder σ A CA) Γ (e : envT nat Γ) y cy k m :
    maj h y cy m -> maj h y cy (interp (plus_t σ) e k m).
  Proof.
    revert Γ e y cy m; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros Γ e y cy m H.
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
      size bound (their complexity is [unit]): a ground value is its own
      size. *)

  (** *** Dialogues *)

  (** The ground type of the answers, and its size. *)
  Fixpoint gty {σ A CA} (h : HigherOrder σ A CA) : Type :=
    match h with @ho_ground A _ _ => A | ho_arr _ h2 => gty h2 end.

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
    | ho_arr _ h2 => fun s xs => cost (s (fst xs)) + dcost h2 (res (s (fst xs))) (snd xs)
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

  (** The arguments [xs] are sized by their potentials. *)
  Definition Sized_args {σ A CA} (h : HigherOrder σ A CA) : spine h -> Prop := lspine (lev h).

  Lemma CSized_ground {A} (RA : Ground A) (sA : Size A) x c : CSized (ho_ground RA sA) x c.
  Proof. exact I. Qed.

  (** *** Monotonicity

      [cle h c c']: the costs of [c'] are at least those of [c], at every
      application, hereditarily. The sizes are closed upwards ([CSized_mono]).
      ([bound_order] is abstract, and only [bound_order_arr] relates it to
      the costs, in one direction: [cle] is the pointwise order.) *)
  Fixpoint cle {σ A CA} (h : HigherOrder σ A CA) : CA -> CA -> Prop :=
    match h in HigherOrder σ A CA return CA -> CA -> Prop with
    | ho_ground _ _ => fun _ _ => True
    | ho_arr _ h2 => fun c c' => forall x, cost (c x) <= cost (c' x) /\ cle h2 (res (c x)) (res (c' x))
    end.

  Lemma dcost_mono {σ A CA} (h : HigherOrder σ A CA) c c' xs : cle h c c' -> dcost h c xs <= dcost h c' xs.
  Proof.
    revert c c' xs; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros c c' xs H; [apply le_n|].
    destruct (H (fst xs)) as [H1 H2]. cbn. pose proof (IH _ _ (snd xs) H2). lia.
  Qed.

  Lemma CSized_mono {σ A CA} (h : HigherOrder σ A CA) f c c' : cle h c c' -> CSized h f c -> CSized h f c'.
  Proof.
    destruct h as [A RA s|σ τ A CA B CB h1 h2]; intros Hc Hf; [exact I|].
    intros xs Hxs. destruct (Hf xs Hxs) as (q & Hq & Hw & Hm). exists q. split; [exact Hq|].
    split; [pose proof (dcost_mono (ho_arr h1 h2) c c' xs Hc); lia | exact Hm].
  Qed.

  (** [cplus h k c]: [c] with [k] added to the cost of every application. *)
  Fixpoint cplus {σ A CA} (h : HigherOrder σ A CA) (k : nat) : CA -> CA :=
    match h in HigherOrder σ A CA return CA -> CA with
    | ho_ground _ _ => fun c => c
    | ho_arr _ h2 => fun c x => (k + cost (c x)) +> cplus h2 k (res (c x))
    end.

  Lemma cle_refl {σ A CA} (h : HigherOrder σ A CA) c : cle h c c.
  Proof.
    revert c; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros c; [exact I|].
    intros x. split; [apply le_n | apply IH].
  Qed.

  Lemma cle_cplus {σ A CA} (h : HigherOrder σ A CA) k c : cle h c (cplus h k c).
  Proof.
    revert c; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros c; [exact I|].
    intros x. cbn. split; [lia | apply IH].
  Qed.

  (** *** Complexities and sizes

      Férée's sizes are bounded by the complexities (proposition 6): a
      machine pays for its dialogue. [SizedComplexities] states it, up to a
      constant for the literals of the program. It is not a theorem of the
      cost model, whose complexities are upper bounds: it is a principle to
      check in its instances. It is meant for allocation, not for time: in
      the allocation cost model, it is an axiom ([sized_allocations], for
      the ground types measured by their footprint). Since received values
      are free, a function that moves them, as the identity, is sized at a
      constant cost ([id_sized]). *)
  Definition SizedComplexities : Prop :=
    forall σ A CA (h : HigherOrder σ A CA) f c, HOBound h f c -> exists k, CSized h f (cplus h k c).

  (** *** Low types *)

  Section LowTypes.
    Context {A B D : Type} (RA : Ground A) (sA : Size A) (RB : Ground B) (sB : Size B)
      (RD : Ground D) (sD : Size D).

    (** A first-order function [f] of size [s]: on each argument [y], the
        size of [f y] plus the question [1] (if [f] reads [y]) is at most
        the cost plus the size of [y], which [f] receives. *)
    Lemma CSized_1 (f : A -> B) (s : ℂI A unit -> ℂO unit) :
      (forall y : ℂI A unit, 1 + sB (f (val y)) <= cost (s y) + sA (val y)) ->
      CSized (ho_arr (ho_ground RA sA) (ho_ground RB sB)) f s.
    Proof.
      intros H [y []] _. exists ([tt], tt). split; [split; [constructor; [exact I | constructor] | exact I]|].
      cbn. split; [specialize (H y); lia|].
      intros [y' []] _ (_ & Hq & _). inversion_clear Hq as [|? ? Hy _]. cbn in *. now rewrite Hy.
    Qed.

    (** A constant function needs no question. *)
    Lemma CSized_const (n : B) (s : ℂI A unit -> ℂO unit) :
      (forall y : ℂI A unit, sB n <= cost (s y)) ->
      CSized (ho_arr (ho_ground RA sA) (ho_ground RB sB)) (fun _ => n) s.
    Proof.
      intros H [y []] _. exists ([], tt). split; [split; [constructor | exact I]|].
      cbn. split; [specialize (H y); lia | reflexivity].
    Qed.

    (** At type [(A → B) → D]: a functional [F] of size [cF] answers on a
        function [f] of size [cf] after finitely many questions [ys] to
        [f]. Each costs [1] plus the cost of [cf] on [y], the answers
        [f y] are free, and the questions determine [F f] among the
        functions of size [cf]. *)
    Lemma CSized_2 (F : (A -> B) -> D) cF (f : A -> B) cf :
      CSized (ho_arr (ho_arr (ho_ground RA sA) (ho_ground RB sB)) (ho_ground RD sD)) F cF ->
      CSized (ho_arr (ho_ground RA sA) (ho_ground RB sB)) f cf ->
      exists ys : list A,
        sD (F f) + list_sum (map (fun y => S (cost (cf (y ⋊ tt)))) ys)
          <= cost (cF (f ⋊ cf)) + list_max (map (fun y => sB (f y)) ys) /\
        forall g, CSized (ho_arr (ho_ground RA sA) (ho_ground RB sB)) g cf ->
          (forall y, In y ys -> g y = f y) -> F g = F f.
    Proof.
      intros HF Hf.
      destruct (HF (f ⋊ cf, tt) (conj Hf I)) as ([qs []] & _ & Hw & Hm).
      exists (map (fun zs => val (fst zs)) qs). split.
      - cbn [answer gsize cweight recv dcost fst snd val pot] in Hw. rewrite !map_map.
        match goal with |- context [list_sum (map ?w qs)] =>
          replace (map w qs) with (map (qweight (ho_arr (ho_ground RA sA) (ho_ground RB sB)) (f ⋊ cf)) qs)
        end.
        + match type of Hw with context [list_max ?l] =>
          match goal with |- context [list_max ?l'] => change l' with l end end.
          lia.
        + apply map_ext. intros [[y []] []]. unfold qweight. cbn. lia.
      - intros g Hg Hgf. apply (Hm (g ⋊ cf, tt) (conj Hg I)).
        split; [reflexivity|]. split; [|exact I].
        apply Forall_forall. intros zs Hin. cbn [answer val fst].
        apply Hgf, (in_map (fun zs : ℂI A unit * unit => val (fst zs))), Hin.
    Qed.

    (** The restriction to sized arguments is not vacuous: evaluation at a
        point [a0] is a sized functional of type [(A → B) → B], with the
        cost of its question. *)
    Definition eval_at (a0 : A) (f : A -> B) : B := f a0.

    Definition eval_at_size (a0 : A) (cf : ℂI (A -> B) (ℂI A unit -> ℂO unit)) : ℂO unit :=
      (1 + cost (pot cf (a0 ⋊ tt))) >|.

    Lemma eval_at_sized a0 :
      CSized (ho_arr (ho_arr (ho_ground RA sA) (ho_ground RB sB)) (ho_ground RB sB))
        (eval_at a0) (eval_at_size a0).
    Proof.
      intros [f []] [Hf _]. exists ([(a0 ⋊ tt, tt)], tt).
      split; [split; [constructor; [split; exact I | constructor] | exact I]|].
      unfold eval_at. cbn. split; [lia|].
      intros [f' []] _ (_ & Hq & _). inversion_clear Hq as [|? ? H _]. exact H.
    Qed.
  End LowTypes.

  (** The identity reads its argument, and answers it: at a constant cost. *)
  Lemma id_sized {A} (RA : Ground A) (sA : Size A) (s : ℂI A unit -> ℂO unit) :
    (forall y, 1 <= cost (s y)) -> CSized (ho_arr (ho_ground RA sA) (ho_ground RA sA)) (fun x => x) s.
  Proof. intros H. apply (CSized_1 RA sA RA sA). intros y. specialize (H y). lia. Qed.

  (** ** Sized arguments

      [smaj h f c m]: [f] of complexity [c] is majorized by [m] on the
      arguments with a size bound. Each argument [x] comes with its
      complexity [cx], majorized by `a` as in [maj], and with a size bound
      [sx] ([CSized]), majorized by `b`: the two are kept apart, and [m]
      takes both. The majorants of [smaj] have the shape [dbl σ], where
      each argument type is doubled. *)
  Fixpoint dbl (σ : ty) : ty := match σ with tN => tN | σ ⇒ τ => σ ⇒ σ ⇒ dbl τ end.

  Fixpoint smaj {σ A CA} (h : HigherOrder σ A CA) : A -> CA -> M (dbl σ) -> Prop :=
    match h in HigherOrder σ A CA return A -> CA -> M (dbl σ) -> Prop with
    | ho_ground _ s => fun x _ m => s x <= m
    | @ho_arr σ τ _ _ _ _ h1 h2 => fun f c m =>
        forall x cx a sx b, monotone σ a -> monotone σ b ->
        maj h1 x cx a -> CSized h1 x sx -> maj h1 x sx b ->
        cost (c (x ⋊ cx)) <= baseM (dbl τ) (m a b) /\ smaj h2 (f x) (res (c (x ⋊ cx))) (m a b)
    end.

  Lemma smaj_mle {σ A CA} (h : HigherOrder σ A CA) f c m m' :
    smaj h f c m -> mle (dbl σ) m m' -> smaj h f c m'.
  Proof.
    revert f c m m'; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros f c m m' Hf Hm;
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
    revert f c m; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros f c m H; [exact H|].
    intros x cx a sx b Ha _ Hx _ _. destruct (H x cx a Ha Hx) as [H1 H2]. cbn [dropM].
    split; [rewrite baseM_drop; exact H1 | exact (IH _ _ _ H2)].
  Qed.

  Lemma hpoly_hpolyS {σ A CA} (h : HigherOrder σ A CA) f : HPolyBound h f -> HPolyBoundS h f.
  Proof.
    intros (c & p & Hc & Hm). exists c, (tapp (drop_t σ) p). split; [exact Hc|].
    apply (smaj_mle _ _ _ _ _ (maj_smaj _ _ _ _ Hm)). exact (mle_drop σ [] tt _ _ (hpoly_monotone σ p)).
  Qed.

  (** ** Raising complexities and majorants *)

  (** [plusM k m]: the majorant [m] with [k] added at every application. *)
  Definition plusM (σ : ty) (k : nat) (m : M σ) : M σ := interp (plus_t σ (Γ := [])) tt k m.

  Lemma plusM_mono σ k m : monotone σ m -> monotone σ (plusM σ k m).
  Proof. intros Hm. exact (mle_interp [] _ (plus_t σ) tt tt I k k (le_n k) m m Hm). Qed.

  Lemma maj_cplus_env {σ A CA} (h : HigherOrder σ A CA) Γ (e : envT nat Γ) k y cy m :
    maj h y cy m -> maj h y (cplus h k cy) (interp (plus_t σ) e k m).
  Proof.
    revert Γ e y cy m; induction h as [A RA s|σ τ A CA B CB h1 _ h2 IH]; intros Γ e y cy m H.
    - rewrite interp_plus_tN. cbn in *. lia.
    - intros x cx a Ha Hx. destruct (H x cx a Ha Hx) as [Hc Hm]. rewrite interp_plus_arr.
      cbn [cplus cost res]. split; [rewrite baseM_plus_t; lia | apply IH, Hm].
  Qed.

  Lemma maj_cplus {σ A CA} (h : HigherOrder σ A CA) k y cy m :
    maj h y cy m -> maj h y (cplus h k cy) (plusM σ k m).
  Proof. exact (maj_cplus_env h [] tt k y cy m). Qed.
End HOBounds.
