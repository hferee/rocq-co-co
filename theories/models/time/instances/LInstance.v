(** * L is an instance of the cost model

    The parts of the time cost model implemented with the call-by-value
    λ-calculus L of the Rocq Library of Undecidability Proofs (terms
    [term], weak call-by-value reduction [step]), gathered in [L]; Rocq
    checks that they provide every axiom ([<:]), with no axiom used. The
    analyses, functors over the cost model, then bound L running times, up
    to the factor [K]: L is a reasonable machine model (Forster, Kunze &
    Roth, POPL 2020). *)

From Stdlib Require Import List ZArith QArith.
From Complexity Require Export TimeCostModel.
From Undecidability.L Require Import Util.L_facts.
Import HOAS_Notations.
(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Local Open Scope nat_scope.
Unset Implicit Arguments.

(** ** Evaluation with a count of beta-steps

    [evalc], a big-step evaluation that counts β-steps, is sound and
    complete for [pow step] ([evalc_sound], [pow_evalc]): the proofs build
    reductions with it. *)

Inductive evalc : nat -> term -> term -> Prop :=
| evalc_lam s : evalc 0 (lam s) (lam s)
| evalc_app s t u v w i j k :
    evalc i s (lam u) -> evalc j t v -> evalc k (subst u 0 v) w ->
    evalc (S (i + j + k)) (app s t) w.

Lemma evalc_lambda n s v : evalc n s v -> lambda v.
Proof. induction 1; eauto using lambda_lam. Qed.

Lemma evalc_sound n s v : evalc n s v -> pow step n s v.
Proof.
  induction 1 as [s | s t u v w i j k Hs IHs Ht IHt Hu IHu].
  - reflexivity.
  - destruct (evalc_lambda _ _ _ Ht) as [v' ->].
    replace (S (i + j + k)) with (i + (j + (1 + k))) by lia.
    eapply pow_trans. { exact (pow_step_congL IHs (eq_refl t)). }
    eapply pow_trans. { exact (pow_step_congR (eq_refl (lam u)) IHt). }
    eapply pow_trans; [| exact IHu]. exists (subst u 0 (lam v')). split; [constructor | reflexivity].
Qed.

(** Conversely, every reduction of L to a value is an evaluation. *)
Lemma step_evalc s t n v : s ≻ t -> evalc n t v -> evalc (S n) s v.
Proof.
  intros H; revert n v; induction H as [s t | s t t' H IH | s s' t H IH]; intros n v Hv.
  - exact (evalc_app _ _ _ _ _ 0 0 n (evalc_lam s) (evalc_lam t) Hv).
  - inversion Hv as [| ? ? u v' w i j k Hs Ht Hu]; subst.
    replace (S (S (i + j + k))) with (S (i + S j + k)) by lia.
    eapply evalc_app; [exact Hs | apply IH, Ht | exact Hu].
  - inversion Hv as [| ? ? u v' w i j k Hs Ht Hu]; subst.
    replace (S (S (i + j + k))) with (S (S i + j + k)) by lia.
    eapply evalc_app; [apply IH, Hs | exact Ht | exact Hu].
Qed.

Lemma pow_evalc n : forall s v, pow step n s v -> lambda v -> evalc n s v.
Proof.
  induction n as [| n IH]; intros s v H Hv.
  - unfold pow in H; cbn in H. subst. destruct Hv as [u ->]. constructor.
  - destruct H as [t [Hst Ht]]. eapply step_evalc; [exact Hst | apply IH; assumption].
Qed.

Lemma evalc_val v : proc v -> evalc 0 v v.
Proof. intros [_ [s ->]]. constructor. Qed.

Lemma evalc_app_val s t w n :
  evalc n (app s t) w -> lambda s -> lambda t ->
  exists u m, s = lam u /\ n = S m /\ evalc m (subst u 0 t) w.
Proof.
  intros H [s' ->] [t' ->]. inversion H as [| ? ? u0 v0 w0 i j k Hs Ht Hu]; subst.
  inversion Hs; subst. inversion Ht; subst. exists u0, k. auto.
Qed.

(** Closed terms are not changed by substitutions. *)
Ltac closed_subst :=
  repeat match goal with
  | H : closed ?x |- context [subst ?x ?n ?u] => rewrite (H n u)
  | H : proc ?x |- context [subst ?x ?n ?u] => rewrite (proj1 H n u)
  end.

Lemma evalc_beta u v w n : evalc 0 v v -> evalc n (subst u 0 v) w ->
  evalc (S n) (app (lam u) v) w.
Proof. intros Hv Hu. exact (evalc_app _ _ _ _ _ 0 0 n (evalc_lam u) Hv Hu). Qed.

(** Evaluating the function and the argument first. *)
Lemma evalc_cong s t s' t' w n1 n2 n3 :
  evalc n1 s s' -> evalc n2 t t' -> evalc n3 (app s' t') w ->
  evalc (n1 + n2 + n3) (app s t) w.
Proof.
  intros Hs Ht H.
  destruct (evalc_lambda _ _ _ Hs) as [u ->]. destruct (evalc_lambda _ _ _ Ht) as [v ->].
  inversion H as [| ? ? u0 v0 w0 i j k Hs' Ht' Hu]; subst.
  inversion Hs'; subst. inversion Ht'; subst.
  replace (n1 + n2 + S (0 + 0 + k)) with (S (n1 + n2 + k)) by lia.
  eapply evalc_app; eassumption.
Qed.

(** [Leval] proves [evalc ?n s ?v] by following the syntax of [s], using
    the evaluations in the context for applications of abstract terms. *)
Ltac Leval :=
  first
    [ eassumption
    | apply evalc_lam
    | apply evalc_val; assumption
    | eapply evalc_beta; [Leval | cbn [subst Nat.eqb]; closed_subst; Leval]
    | lazymatch goal with
      | |- evalc _ (app (app _ _) _) _ => eapply evalc_cong; [Leval | Leval | Leval]
      | |- evalc _ (app _ (app _ _)) _ => eapply evalc_cong; [Leval | Leval | Leval]
      end ].

Lemma proc_closed s : proc s -> closed s.
Proof. now intros []. Qed.

Lemma closed_bound k s : closed s -> bound k s.
Proof. intros H. apply (bound_ge (k := 0)); [now apply closed_dcl | lia]. Qed.

Ltac Lproc :=
  split; [ apply closed_dcl;
           repeat (apply dcllam || apply dclApp || (apply dclvar; lia)
                   || (apply closed_bound; first [assumption | apply proc_closed; assumption]))
         | eexists; reflexivity ].

Lemma evalc_det n n' s v v' : evalc n s v -> evalc n' s v' -> n = n' /\ v = v'.
Proof.
  intros H; revert n' v'; induction H as [s | s t u v w i j k Hs IHs Ht IHt Hu IHu];
    intros n' v' H'.
  - inversion H'; subst; auto.
  - inversion H' as [| ? ? u' v'' w' i' j' k' Hs' Ht' Hu']; subst.
    destruct (IHs _ _ Hs') as [-> E]. inversion E; subst.
    destruct (IHt _ _ Ht') as [-> ->]. destruct (IHu _ _ Hu') as [-> ->]. auto.
Qed.

(** L is deterministic. *)
Lemma pow_det n m s v w : pow step n s v -> pow step m s w -> lambda v -> lambda w -> v = w.
Proof.
  intros Hv Hw Lv Lw.
  exact (proj2 (evalc_det _ _ _ _ _ (pow_evalc _ _ _ Hv Lv) (pow_evalc _ _ _ Hw Lw))).
Qed.

(** ** Encodings of ground data

    The constructor [i] (from [0]) of a type with [k] constructors is
    [λ x_0 .. x_(k-1). x_i a_1 .. a_m], applied to its arguments (Scott
    encodings). *)

Definition unit_enc : term := lam (var 0).

Fixpoint nat_enc' (n : nat) : term :=
  match n with O => lam (lam (var 1)) | S n => lam (lam (app (var 0) (nat_enc' n))) end.

Definition bool_enc (b : bool) : term := if b then lam (lam (var 1)) else lam (lam (var 0)).

Fixpoint pos_enc (p : positive) : term :=
  match p with
  | xI p => lam (lam (lam (app (var 2) (pos_enc p))))
  | xO p => lam (lam (lam (app (var 1) (pos_enc p))))
  | xH => lam (lam (lam (var 0)))
  end.

Definition N_enc (n : N) : term :=
  match n with N0 => lam (lam (var 1)) | Npos p => lam (lam (app (var 0) (pos_enc p))) end.

Definition Z_enc (z : Z) : term :=
  match z with
  | Z0 => lam (lam (lam (var 2)))
  | Zpos p => lam (lam (lam (app (var 1) (pos_enc p))))
  | Zneg p => lam (lam (lam (app (var 0) (pos_enc p))))
  end.

Definition comp_enc (c : comparison) : term :=
  match c with
  | Eq => lam (lam (lam (var 2)))
  | Lt => lam (lam (lam (var 1)))
  | Gt => lam (lam (lam (var 0)))
  end.

Definition Q_enc (q : Q) : term :=
  lam (app (app (var 0) (Z_enc (Qnum q))) (pos_enc (Qden q))).

Lemma unit_enc_proc : proc unit_enc.
Proof. Lproc. Qed.

Lemma nat_enc_proc n : proc (nat_enc' n).
Proof. induction n; cbn; Lproc. Qed.

Lemma bool_enc_proc b : proc (bool_enc b).
Proof. destruct b; cbn; Lproc. Qed.

Lemma pos_enc_proc p : proc (pos_enc p).
Proof. induction p; cbn; Lproc. Qed.

Lemma N_enc_proc n : proc (N_enc n).
Proof. destruct n as [| p]; cbn; [| pose proof (pos_enc_proc p)]; Lproc. Qed.

Lemma Z_enc_proc z : proc (Z_enc z).
Proof. destruct z as [| p | p]; cbn; try pose proof (pos_enc_proc p); Lproc. Qed.

Lemma comp_enc_proc c : proc (comp_enc c).
Proof. destruct c; cbn; Lproc. Qed.

Lemma Q_enc_proc q : proc (Q_enc q).
Proof.
  pose proof (Z_enc_proc (Qnum q)); pose proof (pos_enc_proc (Qden q)); unfold Q_enc; Lproc.
Qed.

(** ** Representations

    A representation of [A] with complexities [CA] is a realisability
    relation [rl k x c s]: the closed L value [s] realises [x] with
    complexity [c], for the applications whose cost is at most [k] (a
    budget of model cost: this step-indexing is what [fix_complexity]
    needs). It comes with the order on complexities, and a default
    complexity ([dflt], for [cdefault]), and the well-formed complexities
    of the values ([rwf], for [wf]), the only ones that realisers have. A
    function with complexity [cf] is realised by an L value whose application to the realiser of an
    argument [a] reduces in at most [K * cost (cf a)] steps to a realiser
    of the result. Lists, options, pairs and sums are realised
    element-wise, by the realisers of their elements with their
    complexities (the default one for the missing ones of options and
    sums; a list needs one for each element). *)

(** The factor between the costs of the model and the steps of L. *)
Definition K := 8.

Record LRepr (A CA : Type) := {
  rl : nat -> A -> CA -> term -> Prop;
  bo : CA -> CA -> Prop;
  dflt : CA;
  rwf : A -> CA -> Prop;
  rl_proc : forall k x c s, rl k x c s -> proc s;
  rl_down : forall k k' x c s, k' <= k -> rl k x c s -> rl k' x c s;
  rl_mono : forall k x c c' s, bo c c' -> rl k x c s -> rl k x c' s;
  bo_refl : forall c, bo c c;
  bo_trans : forall c1 c2 c3, bo c1 c2 -> bo c2 c3 -> bo c1 c3;
  rl_wf : forall k x c s, rl k x c s -> rwf x c }.
Arguments rl {_ _} _ _ _ _ _.
Arguments bo {_ _} _ _ _.
Arguments dflt {_ _} _.
Arguments rwf {_ _} _ _ _.
Arguments rl_wf {_ _ _ _ _ _ _} _.
Arguments rl_proc {_ _ _ _ _ _ _} _.
Arguments rl_down {_ _ _ _ _ _ _ _} _ _.
Arguments rl_mono {_ _ _ _ _ _ _ _} _ _.
Arguments bo_refl {_ _} _ _.
Arguments bo_trans {_ _ _ _ _ _} _ _.

(** Ground data: realised by their encoding, at any budget. *)
Definition ground_repr {A} (e : A -> term) (He : forall x, proc (e x)) : LRepr A unit.
Proof.
  refine {| rl := fun _ x _ s => s = e x; bo := fun _ _ => True; dflt := tt;
            rwf := fun _ _ => True |}.
  - intros k x c s ->. apply He.
  - intros k k' x c s _ H. exact H.
  - intros k x c c' s _ H. exact H.
  - auto.
  - auto.
  - auto.
Defined.

Lemma ground_rl {A} (e : A -> term) He k x : rl (ground_repr e He) k x tt (e x).
Proof. reflexivity. Qed.

(** Functions: applied to a realiser of an argument whose cost fits in the
    budget, a realiser reduces in at most [K] times this cost to a realiser
    of the result, with the remaining budget. *)
Definition arr_rl {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB)
  (k : nat) (f : A -> B) (cf : ℂI A CA -> ℂO CB) (s : term) : Prop :=
  proc s /\ forall j a c1 sa, j <= k -> rl RA j a c1 sa -> cost (cf (a ⋊ c1)) <= j ->
    exists n v, pow step n (app s sa) v /\ n <= K * cost (cf (a ⋊ c1)) /\
      rl RB (j - cost (cf (a ⋊ c1))) (f a) (res (cf (a ⋊ c1))) v.

(** The order: at the well-formed inputs, the only ones the realisers
    are applied to ([rl_wf]). *)
Definition arr_bo {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) (c c' : ℂI A CA -> ℂO CB) : Prop :=
  forall ca, rwf RA (val ca) (pot ca) -> cost (c ca) <= cost (c' ca) /\ bo RB (res (c ca)) (res (c' ca)).

Definition arr_repr {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) :
  LRepr (A -> B) (ℂI A CA -> ℂO CB).
Proof.
  refine {| rl := arr_rl RA RB; bo := arr_bo RA RB;
            dflt := fun _ => 0 +> dflt RB; rwf := fun _ _ => True |}.
  - intros k f c s [H _]. exact H.
  - intros k k' f c s Hk [Hp H]. split; [exact Hp |]. intros j a c1 sa Hj. apply H. lia.
  - intros k f c c' s Hb [Hp H]. split; [exact Hp |].
    intros j a c1 sa Hj Ha Hc. destruct (Hb (a ⋊ c1) (rl_wf Ha)) as [Hcost Hcomp].
    destruct (H j a c1 sa Hj Ha ltac:(lia)) as (n & v & Hv & Hn & Hr).
    exists n, v. split; [exact Hv | split; [unfold K in *; lia |]].
    eapply rl_mono; [exact Hcomp |]. eapply rl_down; [| exact Hr]. lia.
  - intros c ca _. split; [lia | apply bo_refl].
  - intros c1 c2 c3 H12 H23 ca Hw. destruct (H12 ca Hw), (H23 ca Hw).
    split; [lia | eapply bo_trans; eauto].
  - auto.
Defined.

Lemma arr_app {A CA B CB} {RA : LRepr A CA} {RB : LRepr B CB} {k f cf s} (j : nat) {a c1 sa} :
  rl (arr_repr RA RB) k f cf s -> j <= k -> rl RA j a c1 sa -> cost (cf (a ⋊ c1)) <= j ->
  exists n v, pow step n (app s sa) v /\ n <= K * cost (cf (a ⋊ c1)) /\
    rl RB (j - cost (cf (a ⋊ c1))) (f a) (res (cf (a ⋊ c1))) v.
Proof. intros [_ H]. apply H. Qed.

Lemma arr_lam {A CA B CB} {RA : LRepr A CA} {RB : LRepr B CB} {k f cf s} :
  proc s ->
  (forall j a c1 sa, j <= k -> rl RA j a c1 sa -> cost (cf (a ⋊ c1)) <= j ->
    exists n v, pow step n (app s sa) v /\ n <= K * cost (cf (a ⋊ c1)) /\
      rl RB (j - cost (cf (a ⋊ c1))) (f a) (res (cf (a ⋊ c1))) v) ->
  rl (arr_repr RA RB) k f cf s.
Proof. intros Hp H. split; assumption. Qed.

Lemma rl_down_ {A CA} {R : LRepr A CA} {k x c s} (k' : nat) :
  rl R k x c s -> k' <= k -> rl R k' x c s.
Proof. intros H Hk. exact (rl_down Hk H). Qed.

(** Lists ([ListTimeCostModel]): realised by the realisers of their
    elements, with their complexities, one for each element. *)
Fixpoint list_rl {A CA} (P : A -> CA -> term -> Prop) (l : list A) (c : list CA)
  (s : term) : Prop :=
  match l with
  | nil => match c with nil => s = lam (lam (var 1)) | _ :: _ => False end
  | cons x l =>
      match c with
      | nil => False
      | a :: c => exists r t, s = lam (lam (app (app (var 0) r) t)) /\
          P x a r /\ list_rl P l c t
      end
  end.

Lemma list_rl_nil {A CA} {P : A -> CA -> term -> Prop} {c s} :
  list_rl P nil c s -> s = lam (lam (var 1)).
Proof. destruct c; cbn; [exact (fun H => H) | intros []]. Qed.

(** The realisers of a non-empty list, read as the case analysis reads
    them: its head has the head of the complexity, its tail the tail. *)
Lemma list_rl_cons {A CA} {P : A -> CA -> term -> Prop} {x l c s} (d : CA) :
  list_rl P (x :: l) c s ->
  exists r t, s = lam (lam (app (app (var 0) r) t)) /\ P x (hd d c) r /\ list_rl P l (tl c) t.
Proof. destruct c as [| a c]; cbn; [intros [] | exact (fun H => H)]. Qed.

(** The order and the well-formed complexities: [Forall2] ([TimeLists]). *)
Definition list_repr {A CA} (RA : LRepr A CA) : LRepr (list A) (list CA).
Proof.
  refine {| rl := fun k l c s => list_rl (rl RA k) l c s;
            bo := Forall2 (bo RA); dflt := nil; rwf := Forall2 (rwf RA) |}.
  - intros k l; induction l as [| x l IH]; intros [| a c] s; cbn; try tauto.
    + intros ->. Lproc.
    + intros (r & t & -> & Hr & Ht). pose proof (rl_proc Hr). pose proof (IH _ _ Ht). Lproc.
  - intros k k' l c s Hk; revert c s; induction l as [| x l IH]; intros [| a c] s; cbn; try tauto.
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_down Hk Hr) | apply IH, Ht]].
  - intros k l; induction l as [| x l IH]; intros c c' s Hb;
      destruct Hb as [| a a' c c' Ha Hc]; cbn; try tauto.
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_mono Ha Hr) | exact (IH c c' t Hc Ht)]].
  - apply Forall2_refl_. intro c. apply bo_refl.
  - apply Forall2_trans_. intros c1 c2 c3. apply bo_trans.
  - intros k l; induction l as [| x l IH]; intros [| a c] s H; cbn in H; try contradiction.
    + constructor.
    + destruct H as (r & t & -> & Hr & Ht). constructor; [exact (rl_wf Hr) | exact (IH _ _ Ht)].
Defined.

(** Options ([OptionTimeCostModel]): realised by the realiser of their
    element, with its complexity, or the default one. *)
Definition option_rl {A CA} (d : CA) (P : A -> CA -> term -> Prop) (o : option A)
  (c : option CA) (s : term) : Prop :=
  match o with
  | Some x => exists r, s = lam (lam (app (var 1) r)) /\ P x (option_dflt d c) r
  | None => s = lam (lam (var 0))
  end.

Definition option_repr {A CA} (RA : LRepr A CA) : LRepr (option A) (option CA).
Proof.
  refine {| rl := fun k o c s => option_rl (dflt RA) (rl RA k) o c s;
            bo := fun c c' => bo RA (option_dflt (dflt RA) c) (option_dflt (dflt RA) c');
            dflt := None; rwf := fun _ _ => True |}.
  - intros k [x |] c s H; cbn in H.
    + destruct H as (r & -> & Hr). pose proof (rl_proc Hr). Lproc.
    + subst s. Lproc.
  - intros k k' [x |] c s Hk H; cbn in *; [| exact H].
    destruct H as (r & -> & Hr). exists r. split; [reflexivity | exact (rl_down Hk Hr)].
  - intros k [x |] c c' s Hb H; cbn in *; [| exact H].
    destruct H as (r & -> & Hr). exists r. split; [reflexivity | exact (rl_mono Hb Hr)].
  - intros c. apply bo_refl.
  - intros c1 c2 c3 H12 H23. exact (bo_trans H12 H23).
  - auto.
Defined.

(** Sums ([SumTimeCostModel]): realised by the realiser of their element,
    with its complexity, or the default one: [inl x] by [λl. λr. l x],
    [inr y] by [λl. λr. r y]. The default complexity is the one of [inl]. *)
Definition sum_rl {A CA B CB} (dA : CA) (dB : CB) (P : A -> CA -> term -> Prop)
  (Q : B -> CB -> term -> Prop) (x : A + B) (c : CA + CB) (s : term) : Prop :=
  match x with
  | inl a => exists r, s = lam (lam (app (var 1) r)) /\ P a (sum_left dA c) r
  | inr b => exists r, s = lam (lam (app (var 0) r)) /\ Q b (sum_right dB c) r
  end.

Definition sum_repr {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) : LRepr (A + B) (CA + CB).
Proof.
  refine {| rl := fun k x c s => sum_rl (dflt RA) (dflt RB) (rl RA k) (rl RB k) x c s;
            bo := fun c c' => bo RA (sum_left (dflt RA) c) (sum_left (dflt RA) c') /\
                              bo RB (sum_right (dflt RB) c) (sum_right (dflt RB) c');
            dflt := inl (dflt RA); rwf := fun _ _ => True |}.
  - intros k [a | b] c s H; cbn in H; destruct H as (r & -> & Hr); pose proof (rl_proc Hr); Lproc.
  - intros k k' [a | b] c s Hk H; cbn in *; destruct H as (r & -> & Hr); exists r;
      (split; [reflexivity | exact (rl_down Hk Hr)]).
  - intros k [a | b] c c' s [B1 B2] H; cbn in *; destruct H as (r & -> & Hr); exists r;
      split; [reflexivity | exact (rl_mono B1 Hr) | reflexivity | exact (rl_mono B2 Hr)].
  - intros c. split; apply bo_refl.
  - intros c1 c2 c3 [B1 B2] [B3 B4]. split; [exact (bo_trans B1 B3) | exact (bo_trans B2 B4)].
  - auto.
Defined.

(** Environments of closures ([Combinators]): pairs of realisers of any
    representations. *)
Definition env_rl {E CE A CA} (RE : LRepr E CE) (RA : LRepr A CA) (k : nat) (e : env E A)
  (c : CE * CA) (s : term) : Prop :=
  exists r1 r2, s = lam (app (app (var 0) r1) r2) /\
    rl RE k (etl e) (fst c) r1 /\ rl RA k (ehd e) (snd c) r2.

Definition env_repr {E CE A CA} (RE : LRepr E CE) (RA : LRepr A CA) :
  LRepr (env E A) (CE * CA).
Proof.
  refine {| rl := env_rl RE RA;
            bo := fun c c' => bo RE (fst c) (fst c') /\ bo RA (snd c) (snd c');
            dflt := (dflt RE, dflt RA);
            rwf := fun e c => rwf RE (etl e) (fst c) /\ rwf RA (ehd e) (snd c) |}.
  - intros k e c s (r1 & r2 & -> & H1 & H2).
    pose proof (rl_proc H1). pose proof (rl_proc H2). Lproc.
  - intros k k' e c s Hk (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k e c c' s [B1 B2] (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_mono B1 H1) | exact (rl_mono B2 H2)]].
  - intros c. split; apply bo_refl.
  - intros c1 c2 c3 [B1 B2] [B3 B4]. split; [exact (bo_trans B1 B3) | exact (bo_trans B2 B4)].
  - intros k e c s (r1 & r2 & -> & H1 & H2). exact (conj (rl_wf H1) (rl_wf H2)).
Defined.

(** Pairs ([ProdTimeCostModel]): realised by the realisers of their
    elements, with their complexities, as the environments. *)
Definition prod_rl {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) (k : nat) (p : A * B)
  (c : CA * CB) (s : term) : Prop :=
  exists r1 r2, s = lam (app (app (var 0) r1) r2) /\
    rl RA k (fst p) (fst c) r1 /\ rl RB k (snd p) (snd c) r2.

Definition prod_repr {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) :
  LRepr (A * B) (CA * CB).
Proof.
  refine {| rl := prod_rl RA RB;
            bo := fun c c' => bo RA (fst c) (fst c') /\ bo RB (snd c) (snd c');
            dflt := (dflt RA, dflt RB);
            rwf := fun p c => rwf RA (fst p) (fst c) /\ rwf RB (snd p) (snd c) |}.
  - intros k p c s (r1 & r2 & -> & H1 & H2).
    pose proof (rl_proc H1). pose proof (rl_proc H2). Lproc.
  - intros k k' p c s Hk (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k p c c' s [B1 B2] (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_mono B1 H1) | exact (rl_mono B2 H2)]].
  - intros c. split; apply bo_refl.
  - intros c1 c2 c3 [B1 B2] [B3 B4]. split; [exact (bo_trans B1 B3) | exact (bo_trans B2 B4)].
  - intros k p c s (r1 & r2 & -> & H1 & H2). exact (conj (rl_wf H1) (rl_wf H2)).
Defined.

(** ** Tactics *)

Ltac Llia := unfold K in *; cbn [cost res pot val] in *; lia.

(** Introduce an argument of a function being realised. *)
Ltac Lfun :=
  apply arr_lam; [Lproc |
    let j := fresh "j" in let a := fresh "a" in let c := fresh "c" in
    let s := fresh "s" in let Hj := fresh "Hj" in let Ha := fresh "Ha" in
    let Hc := fresh "Hc" in
    intros j a c s Hj Ha Hc; pose proof (rl_proc Ha);
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I] in Hc |- *].

(** Evaluate, check the cost, and leave the realisability of the result. *)
Ltac Lstep := do 2 eexists; split; [apply evalc_sound; Leval | split; [Llia |]].

(** Apply the realiser [Hf] of a function to the realiser [Ha] of an
    argument, with the budget [J]. *)
Ltac Lcall Hf Ha J :=
  let n := fresh "n" in let v := fresh "v" in let E := fresh "E" in
  let N := fresh "N" in let R := fresh "R" in
  edestruct (arr_app J Hf ltac:(Llia) (rl_down_ J Ha ltac:(Llia)) ltac:(Llia))
    as (n & v & E & N & R);
  cbn [cost res pot val] in N, R; pose proof (rl_proc R);
  apply pow_evalc in E; [| apply (rl_proc R)].

Ltac Lend H := eapply rl_down; [| exact H]; Llia.

Ltac Lground := cbn in *; subst; reflexivity.

(** ** Realisers *)

Definition Ic_r := lam (var 0).
Definition Kc_r := lam (lam (var 1)).
Definition compose_r := lam (lam (lam (app (var 2) (app (var 1) (var 0))))).
Definition Cc_r := lam (lam (lam (app (app (var 2) (var 0)) (var 1)))).
Definition Sc_r := lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0))))).
Definition ehd_r := lam (app (var 0) (lam (lam (var 0)))).
Definition etl_r := lam (app (var 0) (lam (lam (var 1)))).
Definition Lam_r := lam (lam (lam (app (var 2) (lam (app (app (var 0) (var 2)) (var 1)))))).

(** The case combinators in environments ([TimeDatatypes]): [caseE] takes
    the code of the branches, the code [x] of the matched value and the
    environment [e], evaluates [x e], and applies the value to one handler
    per constructor, then to [Ic_r]. The handler of a constructor with [m]
    arguments takes them, then a dummy argument, and calls the code of its
    branch on [e] extended with them (the environments are pairs of
    realisers, [env_rl]). [b] is the index of the code of the branch in the
    context [e; x; branches], the last branch first. *)
Definition hE0 (b : nat) := lam (app (var (S b)) (var 1)).
Definition hE1 (b : nat) := lam (lam (app (var (S (S b))) (lam (app (app (var 0) (var 3)) (var 2))))).
Definition hE2 (b : nat) :=
  lam (lam (lam (app (var (S (S (S b))))
    (lam (app (app (var 0) (lam (app (app (var 0) (var 5)) (var 4)))) (var 2)))))).

Definition caseE1 (h1 : term) := lam (lam (lam (app (app (app (var 1) (var 0)) h1) Ic_r))).
Definition caseE2 (h1 h2 : term) :=
  lam (lam (lam (lam (app (app (app (app (var 1) (var 0)) h1) h2) Ic_r)))).
Definition caseE3 (h1 h2 h3 : term) :=
  lam (lam (lam (lam (lam (app (app (app (app (app (var 1) (var 0)) h1) h2) h3) Ic_r))))).

Ltac LunfoldE := cbv [caseE1 caseE2 caseE3 hE0 hE1 hE2 Ic_r unit_enc]; intro k.
Ltac LcaseE1_start := LunfoldE; Lfun; Lstep; Lfun; Lstep; Lfun.
Ltac LcaseE2_start := LunfoldE; Lfun; Lstep; Lfun; Lstep; Lfun; Lstep; Lfun.
Ltac LcaseE3_start := LunfoldE; Lfun; Lstep; Lfun; Lstep; Lfun; Lstep; Lfun; Lstep; Lfun.

(** Unfold the encoding of the matched value in its evaluation. *)
Ltac Lscrut x e := match goal with H : evalc _ (app x e) _ |- _ => cbn in H end.

(** The realisers of a representation [R] do not distinguish the values
    that are pointwise equal at the arity [ar] ([PwExt] of [TimeFix]). *)
Definition pw_ext {B CB} (R : LRepr B CB) (ar : Arity B) : Prop :=
  forall k x y c s, pw_eq ar x y -> rl R k y c s -> rl R k x c s.

Lemma pw_ext_val_ {B CB} (R : LRepr B CB) : pw_ext R (ar_val B).
Proof. intros k x y c s E H. cbn in E. subst. exact H. Qed.

(** A function is only observed through its applications. *)
Lemma pw_ext_fun_ {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) (ar : Arity B) :
  pw_ext RB ar -> pw_ext (arr_repr RA RB) (ar_fun A B ar).
Proof.
  intros HB k f g c s E [Hp H]. split; [exact Hp |].
  intros j a c1 sa Hj Ha Hc. destruct (H j a c1 sa Hj Ha Hc) as (n & v & Hv & Hn & Hr).
  exists n, v. split; [exact Hv | split; [exact Hn | exact (HB _ _ _ _ _ (E a) Hr)]].
Qed.

(** ** L is an instance of the cost model *)

Module LCM <: CostModel.
  Definition Repr := LRepr.
  Existing Class Repr.

  (** The size of a value is its number of constructors, the length of its
      binary encoding ([Size]), not the size of its encoding as an L term. *)

  Global Instance Repr_arr {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) :
    Repr (A -> B) (ℂI A CA -> ℂO CB) := arr_repr RA RB.

  (** [x] has complexity [c]: some L value realises it, at every budget. *)
  Definition has_complexity {A CA} {R : Repr A CA} (x : A) (c : CA) : Prop :=
    exists s, forall k, rl R k x c s.

  Definition bound_order {A CA} {R : Repr A CA} (c c' : CA) : Prop := bo R c c'.
  Definition cdefault {A CA} {R : Repr A CA} : CA := dflt R.
  Definition wf {A CA} {R : Repr A CA} (x : A) (c : CA) : Prop := rwf R x c.

  Global Instance bound_order_po {A CA} {R : Repr A CA} : PreOrder (@bound_order A CA R) :=
    ltac:(split; [intro c; apply bo_refl | intros c1 c2 c3; apply bo_trans]).

  Lemma bound_order_arr {A CA B CB} {RA : Repr A CA} {RB : Repr B CB}
    (c c' : ℂI A CA -> ℂO CB) :
    (forall ca, wf (val ca) (pot ca) ->
       cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.
  Proof. intro H. exact H. Qed.

  (** The complexity bounds ([Complexities]). The bounds of L are its
      complexities: realisability is monotone in the complexity. *)
  Include Complexities.
  Include GroundTypes.

  Lemma complexity_bound_has {A CA} {R : Repr A CA} (f : A) (c : CA) :
    ComplexityBound f c -> has_complexity f c.
  Proof. intros [(c0 & Hc & s & H)]. exists s. intro k. exact (rl_mono Hc (H k)). Qed.

  (** The bounds in the size of the inputs ([Bounds]), their tactics
      ([BoundsTactics]), and the bounds at higher types ([HOBounds]). *)
  Include Bounds.
  Include BoundsTactics.
  Include HOBounds.
End LCM.

(** Higher-order primitives. *)
Module LBT <: BasicTimeCostModel LCM.
  Import LCM.
  (** Every application is a beta-step: each combinator costs [1]. *)
  Definition c_clo := 1.
  Definition c_ehd := 1.
  Definition c_etl := 1.
  Definition c_Lam := 1.
  Definition c_Kc := 1.
  Definition c_Ic := 1.
  Definition c_compose := 1.
  Definition c_Cc := 1.
  Definition c_Sc := 1.
  (** L reduces terms: there is no stack, and no frame to pay. *)
  Definition c_frame := 0.

  Lemma id_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (fun (x : A) => x) (fun ca => (1 +> pot ca) : ℂO CA).
  Proof.
    intros A CA R. apply has_complexity_bound. exists Ic_r. intro k. Lfun. Lstep. Lend Ha.
  Qed.

  Lemma apply_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
      {v : A} {f : A -> B} {cv : CA} (cf : ℂI A CA -> ℂO CB),
      ComplexityBound v cv ->
      ComplexityBound f cf ->
      ComplexityBound (f v: B) (res (cf (v ⋊ cv))).
  Proof.
    intros A B CA CB RA RB v f cv cf [sv Hv]%complexity_bound_has [sf Hf]%complexity_bound_has.
    apply has_complexity_bound.
    set (c := cost (cf (v ⋊ cv))).
    destruct (arr_app c (Hf c) ltac:(lia) (Hv c) ltac:(lia)) as (n0 & v0 & E0 & _ & R0).
    exists v0. intro k.
    destruct (arr_app (k + c) (Hf (k + c)) ltac:(lia) (Hv (k + c)) ltac:(lia))
      as (n1 & v1 & E1 & _ & R1).
    rewrite <- (pow_det _ _ _ _ _ E0 E1 (proj2 (rl_proc R0)) (proj2 (rl_proc R1))) in R1.
    eapply rl_down; [| exact R1]. lia.
  Qed.

  Lemma compose_complexity : forall {A B C CA CB CC}
      `{Repr A CA} `{Repr B CB} `{Repr C CC}
      (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
      ComplexityBound f cf ->
      ComplexityBound g cg ->
      ComplexityBound (compose f g : A -> C)
                      (fun ca => 1 ⊕ pot <$> (f ⋊ cf) · ((g ⋊ cg) · ca)).
  Proof.
    intros A B C CA CB CC RA RB RC f cf g cg [sf Hf]%complexity_bound_has
      [sg Hg]%complexity_bound_has.
    apply has_complexity_bound.
    exists (lam (app sf (app sg (var 0)))). intro k.
    pose proof (rl_proc (Hf 0)). pose proof (rl_proc (Hg 0)).
    Lfun. Lcall (Hg j) Ha (j - 1). Lcall (Hf j) R (j - 1 - cost (cg (a ⋊ c))).
    Lstep. Lend R0.
  Qed.

  Lemma constant_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB} b {cb},
      ComplexityBound (b : B) (cb : CB) ->
      ComplexityBound (fun (_ : A) => b) (fun _ => 1 +> cb).
  Proof.
    intros A B CA CB RA RB b cb [sb Hb]%complexity_bound_has. apply has_complexity_bound.
    exists (lam sb). intro k. pose proof (rl_proc (Hb 0)).
    Lfun. Lstep. apply Hb.
  Qed.

  Global Instance Repr_unit : Repr unit unit :=
    ground_repr (fun _ => unit_enc) (fun _ => unit_enc_proc).

  Lemma tt_complexity : ComplexityBound tt tt.
  Proof.
    apply has_complexity_bound. exists unit_enc. intro k. reflexivity.
  Qed.

End LBT.

(** Combinators. *)
Module LCB <: CombinatorTimeCostModel LCM LBT.
  Import LCM LBT.
  Global Instance Repr_env {E CE A CA} (RE : Repr E CE) (RA : Repr A CA) :
    Repr (env E A) (CE * CA) :=
    env_repr RE RA.

  Lemma wf_env : forall {E CE A CA} `{Repr E CE} `{Repr A CA} (e : env E A) (c : CE * CA),
    wf e c <-> wf (etl e) (fst c) /\ wf (ehd e) (snd c).
  Proof. intros. reflexivity. Qed.

  Lemma ehd_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@ehd E A) (fun ce => 1 +> snd (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists ehd_r. intro k. Lfun.
    destruct Ha as (r1 & r2 & -> & Hr1 & Hr2). pose proof (rl_proc Hr1). pose proof (rl_proc Hr2).
    Lstep. Lend Hr2.
  Qed.

  Lemma etl_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@etl E A) (fun ce => 1 +> fst (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists etl_r. intro k. Lfun.
    destruct Ha as (r1 & r2 & -> & Hr1 & Hr2). pose proof (rl_proc Hr1). pose proof (rl_proc Hr2).
    Lstep. Lend Hr1.
  Qed.

  Lemma Lam_complexity : forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => 1 +>
       fun ce : ℂI E CE => 1 +>
       fun ca : ℂI A CA => 1 ⊕ pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))).
  Proof.
    intros. apply has_complexity_bound. exists Lam_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    assert (He : rl (env_repr _ _) j1 (ECons a0 a1) (c0, c1)
                   (lam (app (app (var 0) s0) s1)))
      by (exists s0, s1; split; [reflexivity | split; [exact (rl_down_ j1 Ha0 ltac:(lia)) | exact Ha1]]).
    Lcall Ha He (j1 - 1). Lstep. Lend R.
  Qed.

  Lemma Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
      ComplexityBound (@Kc A B) (fun ca => 1 +> (fun _ => 1 +> pot ca)).
  Proof.
    intros. apply has_complexity_bound. exists Kc_r. intro k. Lfun. Lstep. Lfun. Lstep. Lend Ha.
  Qed.

  Lemma Ic_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (@Ic A) (fun ca => 1 +> pot ca).
  Proof.
    intros. apply has_complexity_bound. exists Ic_r. intro k. Lfun. Lstep. Lend Ha.
  Qed.

  Lemma compose_hcomplexity : forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 1 +>
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +>
       fun ca : ℂI A CA => 1 ⊕ pot <$> cf · (cg · ca)).
  Proof.
    intros. apply has_complexity_bound. exists compose_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    Lcall Ha0 Ha1 (j1 - 1). Lcall Ha R (j1 - 1 - cost (c0 (a1 ⋊ c1))).
    Lstep. Lend R0.
  Qed.

  Lemma Cc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 +>
       fun ca : ℂI A CA => 1 +>
       fun cx : ℂI X CX => 1 ⊕ pot <$> cf · cx · ca).
  Proof.
    intros. apply has_complexity_bound. exists Cc_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    Lcall Ha Ha1 (j1 - 1). Lcall R Ha0 (j1 - 1 - cost (c (a1 ⋊ c1))).
    Lstep. Lend R0.
  Qed.

  Lemma Sc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 +>
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 1 +>
       fun cx : ℂI X CX => 1 ⊕ pot <$> cf · cx · (cg · cx)).
  Proof.
    intros. apply has_complexity_bound. exists Sc_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    Lcall Ha0 Ha1 (j1 - 1). Lcall Ha Ha1 (j1 - 1 - cost (c0 (a1 ⋊ c1))).
    Lcall R0 R (j1 - 1 - cost (c0 (a1 ⋊ c1)) - cost (c (a1 ⋊ c1))).
    Lstep. Lend R1.
  Qed.

  (** The definitions and tactics of the model ([Found], [cbound], ...). *)
  Include CombinatorTactics LCM LBT.
End LCB.

(** [nat]. *)
Module LNT <: NatTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_S := 1.
  Definition c_case_nat := 1.
  Global Instance Repr_nat : Repr nat unit := ground_repr nat_enc' nat_enc_proc.

  Global Instance Size_nat : Size nat := fun n => S n.
  Lemma size_O : Bounds.size 0 = 1.
  Proof. reflexivity. Qed.
  Lemma size_S : forall n, Bounds.size (S n) = 1 + Bounds.size n.
  Proof. reflexivity. Qed.

  Lemma nat_complexity : forall n : nat, ComplexityBound n tt.
  Proof.
    intro n. apply has_complexity_bound. exists (nat_enc' n). intro k. reflexivity.
  Qed.

  Lemma S_complexity : ComplexityBound S (fun x => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (var 0) (var 2))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma nat_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@nat_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cs : ℂI (env E nat -> A) (ℂI (env E nat) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (E -> nat) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | O => pot cz ce
         | S k => pot cs (ECons (val ce) k ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE2 (hE0 3) (hE1 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). cbn in R. subst v. unfold nat_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [| m]; cbn [cost res pot val] in *; Lscrut s1 s2.
    - Lcall Ha Ha2 b. Lstep. Lend R.
    - pose proof (nat_enc_proc m).
      assert (He : rl (env_repr RE Repr_nat) b (ECons a2 m) (c2, tt)
                     (lam (app (app (var 0) s2) (nat_enc' m)))).
      { exists s2, (nat_enc' m). split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact (ground_rl nat_enc' nat_enc_proc b m)]. }
      Lcall Ha0 He b. Lstep. Lend R.
  Qed.

End LNT.

(** [bool]. *)
Module LBO <: BoolTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_case_bool := 1.
  Global Instance Repr_bool : Repr bool unit := ground_repr bool_enc bool_enc_proc.

  Global Instance Size_bool : Size bool := fun _ => 1.
  Lemma size_bool : forall b : bool, Bounds.size b = 1.
  Proof. reflexivity. Qed.

  Lemma bool_complexity : forall b : bool, ComplexityBound b tt.
  Proof.
    intro b. apply has_complexity_bound. exists (bool_enc b). intro k. reflexivity.
  Qed.

  Lemma bool_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@bool_case E A)
      (fun ct : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cf : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cb : ℂI (E -> bool) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cb ce) ⊕
         if val cb (val ce) then pot ct ce else pot cf ce).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE2 (hE0 3) (hE0 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). cbn in R. subst v. unfold bool_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2); cbn [cost res pot val] in *; Lscrut s1 s2.
    - Lcall Ha Ha2 b. Lstep. Lend R.
    - Lcall Ha0 Ha2 b. Lstep. Lend R.
  Qed.

End LBO.

(** Lists. *)
(** Lists. *)
Module LLM <: ListTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_cons := 1.
  Definition c_case_list := 1.
  Global Instance Repr_list {A CA} (RA : Repr A CA) : Repr (list A) (list CA) := list_repr RA.

  Global Instance Size_list {A} (SA : Size A) : Size (list A) :=
    fix size_list l := match l with nil => 1 | a :: l => 1 + SA a + size_list l end.
  Lemma size_nil : forall {A} `{Size A}, Bounds.size (@nil A) = 1.
  Proof. reflexivity. Qed.
  Lemma size_cons : forall {A} `{Size A} (a : A) l,
    Bounds.size (a :: l) = 1 + Bounds.size a + Bounds.size l.
  Proof. reflexivity. Qed.

  Lemma wf_list : forall {A CA} `{Repr A CA} (l : list A) (c : list CA),
    wf l c <-> Forall2 wf l c.
  Proof. intros. reflexivity. Qed.

  Lemma bound_order_list : forall {A CA} `{Repr A CA} (c c' : list CA),
    Forall2 (@bound_order A CA _) c c' -> bound_order c c'.
  Proof. intros A CA RA c c' H. exact H. Qed.

  Lemma nil_complexity : forall {A CA} `{Repr A CA}, ComplexityBound (@nil A) (@nil CA).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (lam (lam (var 1))). intro k. reflexivity.
  Qed.

  Lemma cons_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@cons A) (fun ch => 1 +> fun ct => 1 +> (pot ch :: pot ct)).
  Proof.
    intros A CA RA. apply has_complexity_bound.
    exists (lam (lam (lam (lam (app (app (var 0) (var 3)) (var 2)))))). intro k.
    Lfun. Lstep. Lfun. Lstep. cbn [rl Repr_list list_repr list_rl hd tl].
    exists s, s0. split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - exact (rl_down_ (j0 - 1) Ha0 ltac:(lia)).
  Qed.

  Lemma list_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * CX) * list CX) -> ℂO CA) => 1 +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO (list CX)) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cl ce) ⊕
         match val cl (val ce) with
         | cons h t =>
             pot cc (ECons (ECons (val ce) h) t
                       ⋊ ((pot ce, hd cdefault (res (pot cl ce))), tl (res (pot cl ce))))
         | nil => pot cz ce
         end).
  Proof.
    intros X CX E CE A CA RX RE RA. apply has_complexity_bound. exists (caseE2 (hE0 3) (hE2 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). unfold list_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    set (cl := res (c1 (a2 ⋊ c2))) in *.
    destruct (a1 a2) as [| x l]; cbn in R; cbn [cost res pot val] in *.
    - apply (list_rl_nil (A := X) (P := fun _ _ _ => True)) in R. subst v. Lscrut s1 s2. Lcall Ha Ha2 b. Lstep. Lend R.
    - apply (list_rl_cons (dflt RX)) in R. destruct R as (r & t & -> & Hr & Ht). pose proof (rl_proc Hr).
      assert (Ht' : rl (Repr_list RX) b l (tl cl) t) by exact Ht. pose proof (rl_proc Ht').
      assert (He : rl (env_repr (env_repr RE RX) (Repr_list RX)) b (ECons (ECons a2 x) l)
                     ((c2, hd cdefault cl), tl cl)
                     (lam (app (app (var 0) (lam (app (app (var 0) s2) r))) t))).
      { exists (lam (app (app (var 0) s2) r)), t. split; [reflexivity|]. split; [| exact Ht'].
        exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha0 He b. Lstep. Lend R.
  Qed.

End LLM.

(** Options. *)
Module LOM <: OptionTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_Some := 1.
  Definition c_case_option := 1.
  Global Instance Repr_option {A CA} (RA : Repr A CA) : Repr (option A) (option CA) :=
    option_repr RA.

  Global Instance Size_option {A} (SA : Size A) : Size (option A) :=
    fun o => match o with None => 1 | Some a => 1 + SA a end.
  Lemma size_None : forall {A} `{Size A}, Bounds.size (@None A) = 1.
  Proof. reflexivity. Qed.
  Lemma size_Some : forall {A} `{Size A} (a : A), Bounds.size (Some a) = 1 + Bounds.size a.
  Proof. reflexivity. Qed.

  Lemma bound_order_option : forall {A CA} `{Repr A CA} (c c' : option CA),
    bound_order (option_dflt cdefault c) (option_dflt cdefault c') -> bound_order c c'.
  Proof. intros A CA RA c c' H. exact H. Qed.

  Lemma None_complexity : forall {A CA} `{Repr A CA}, ComplexityBound (@None A) (@None CA).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (lam (lam (var 0))). intro k. reflexivity.
  Qed.

  Lemma Some_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Some A) (fun ca => 1 +> Some (pot ca)).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (lam (lam (lam (app (var 1) (var 2))))). intro k.
    Lfun. Lstep. cbn [rl Repr_option option_repr option_rl].
    exists s. split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma option_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => 1 +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO (option CX)) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot co ce) ⊕
         match val co (val ce) with
         | Some x => pot cs (ECons (val ce) x ⋊ (pot ce, option_dflt cdefault (res (pot co ce))))
         | None => pot cz ce
         end).
  Proof.
    intros X CX E CE A CA RX RE RA. apply has_complexity_bound. exists (caseE2 (hE1 3) (hE0 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). unfold option_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    set (co := res (c1 (a2 ⋊ c2))) in *.
    destruct (a1 a2) as [x |]; cbn in R; cbn [cost res pot val] in *.
    - destruct R as (r & -> & Hr). pose proof (rl_proc Hr).
      assert (He : rl (env_repr RE RX) b (ECons a2 x) (c2, option_dflt cdefault co)
                     (lam (app (app (var 0) s2) r))).
      { exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha He b. Lstep. Lend R.
    - subst v. Lscrut s1 s2. Lcall Ha0 Ha2 b. Lstep. Lend R.
  Qed.

End LOM.

(** Pairs. *)
Module LPM <: ProdTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_pair := 1.
  Definition c_case_prod := 1.
  Global Instance Repr_prod {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) :
    Repr (A * B) (CA * CB) := prod_repr RA RB.

  Global Instance Size_prod {A B} (SA : Size A) (SB : Size B) : Size (A * B) :=
    fun p => 1 + SA (fst p) + SB (snd p).
  Lemma size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    Bounds.size (a, b) = 1 + Bounds.size a + Bounds.size b.
  Proof. reflexivity. Qed.

  Lemma bound_order_prod : forall {A CA B CB} `{Repr A CA} `{Repr B CB} (c c' : CA * CB),
    bound_order (fst c) (fst c') -> bound_order (snd c) (snd c') -> bound_order c c'.
  Proof. intros A CA B CB RA RB c c' H1 H2. exact (conj H1 H2). Qed.

  Lemma wf_prod : forall {A CA B CB} `{Repr A CA} `{Repr B CB} (p : A * B) (c : CA * CB),
    wf p c <-> wf (fst p) (fst c) /\ wf (snd p) (snd c).
  Proof. intros. reflexivity. Qed.

  Lemma pair_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@pair A B) (fun ca => 1 +> fun cb => 1 +> (pot ca, pot cb)).
  Proof.
    intros A CA B CB RA RB. apply has_complexity_bound.
    exists (lam (lam (lam (app (app (var 0) (var 2)) (var 1))))). intro k.
    Lfun. Lstep. Lfun. Lstep.
    cbn [rl Repr_prod prod_repr prod_rl fst snd]. exists s, s0. split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - eapply rl_down; [| exact Ha0]. lia.
  Qed.

  Lemma prod_case_complexity :
    forall {X CX Y CY E CE A CA} `{Repr X CX} `{Repr Y CY} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@prod_case X Y E A)
      (fun cf : ℂI (env (env E X) Y -> A) (ℂI (env (env E X) Y) ((CE * CX) * CY) -> ℂO CA) =>
         1 +>
       fun cp : ℂI (E -> X * Y) (ℂI E CE -> ℂO (CX * CY)) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cp ce) ⊕
         let (x, y) := val cp (val ce) in
         let (cx, cy) := res (pot cp ce) in
         pot cf (ECons (ECons (val ce) x) y ⋊ ((pot ce, cx), cy))).
  Proof.
    intros X CX Y CY E CE A CA RX RY RE RA. apply has_complexity_bound. exists (caseE1 (hE2 2)).
    LcaseE1_start. Lcall Ha0 Ha1 (j1 - 1). unfold prod_case.
    set (b := j1 - 1 - cost (c0 (a1 ⋊ c1))).
    destruct (a0 a1) as [x y]; destruct (res (c0 (a1 ⋊ c1))) as [cx cy];
      cbn [rl Repr_prod prod_repr prod_rl fst snd] in R; cbn [cost res pot val] in *.
    destruct R as (r1 & r2 & -> & Hr1 & Hr2).
    pose proof (rl_proc Hr1). pose proof (rl_proc Hr2).
    assert (He : rl (env_repr (env_repr RE RX) RY) b (ECons (ECons a1 x) y) ((c1, cx), cy)
                   (lam (app (app (var 0) (lam (app (app (var 0) s1) r1))) r2))).
    { exists (lam (app (app (var 0) s1) r1)), r2. split; [reflexivity|]. split; [| exact Hr2].
      exists s1, r1. split; [reflexivity|].
      split; [exact (rl_down_ b Ha1 ltac:(unfold b; lia)) | exact Hr1]. }
    Lcall Ha He b. Lstep. Lend R.
  Qed.
End LPM.

(** Sums. *)
Module LSM <: SumTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_ctor_sum := 1.
  Definition c_case_sum := 1.
  Global Instance Repr_sum {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) :
    Repr (A + B) (CA + CB) := sum_repr RA RB.

  Global Instance Size_sum {A B} (SA : Size A) (SB : Size B) : Size (A + B) :=
    fun x => match x with inl a => 1 + SA a | inr b => 1 + SB b end.
  Lemma size_inl : forall {A B} `{Size A} `{Size B} (a : A),
    Bounds.size (@inl A B a) = 1 + Bounds.size a.
  Proof. reflexivity. Qed.
  Lemma size_inr : forall {A B} `{Size A} `{Size B} (b : B),
    Bounds.size (@inr A B b) = 1 + Bounds.size b.
  Proof. reflexivity. Qed.

  Lemma bound_order_sum : forall {A CA B CB} `{Repr A CA} `{Repr B CB} (c c' : CA + CB),
    bound_order (sum_left cdefault c) (sum_left cdefault c') ->
    bound_order (sum_right cdefault c) (sum_right cdefault c') -> bound_order c c'.
  Proof. intros A CA B CB RA RB c c' H1 H2. exact (conj H1 H2). Qed.

  Lemma inl_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@inl A B) (fun ca => 1 +> @inl CA CB (pot ca)).
  Proof.
    intros A CA B CB RA RB. apply has_complexity_bound.
    exists (lam (lam (lam (app (var 1) (var 2))))). intro k.
    Lfun. Lstep. cbn [rl Repr_sum sum_repr sum_rl].
    exists s. split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma inr_complexity : forall {A CA B CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@inr A B) (fun cb => 1 +> @inr CA CB (pot cb)).
  Proof.
    intros A CA B CB RA RB. apply has_complexity_bound.
    exists (lam (lam (lam (app (var 0) (var 2))))). intro k.
    Lfun. Lstep. cbn [rl Repr_sum sum_repr sum_rl].
    exists s. split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma sum_case_complexity :
    forall {X CX Y CY E CE A CA} `{Repr X CX} `{Repr Y CY} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@sum_case X Y E A)
      (fun cl : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => 1 +>
       fun cr : ℂI (env E Y -> A) (ℂI (env E Y) (CE * CY) -> ℂO CA) => 1 +>
       fun cs : ℂI (E -> X + Y) (ℂI E CE -> ℂO (CX + CY)) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cs ce) ⊕
         match val cs (val ce), res (pot cs ce) with
         | inl x, inl cx => pot cl (ECons (val ce) x ⋊ (pot ce, cx))
         | inl x, inr _ => pot cl (ECons (val ce) x ⋊ (pot ce, cdefault))
         | inr y, inr cy => pot cr (ECons (val ce) y ⋊ (pot ce, cy))
         | inr y, inl _ => pot cr (ECons (val ce) y ⋊ (pot ce, cdefault))
         end).
  Proof.
    intros X CX Y CY E CE A CA RX RY RE RA. apply has_complexity_bound.
    exists (caseE2 (hE1 3) (hE1 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). unfold sum_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [x | y]; destruct (res (c1 (a2 ⋊ c2))) as [cx | cy];
      cbn in R; cbn [cost res pot val] in *;
      destruct R as (r & -> & Hr); pose proof (rl_proc Hr).
    - assert (He : rl (env_repr RE RX) b (ECons a2 x) (c2, cx) (lam (app (app (var 0) s2) r))).
      { exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha He b. Lstep. Lend R.
    - assert (He : rl (env_repr RE RX) b (ECons a2 x) (c2, cdefault) (lam (app (app (var 0) s2) r))).
      { exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha He b. Lstep. Lend R.
    - assert (He : rl (env_repr RE RY) b (ECons a2 y) (c2, cdefault) (lam (app (app (var 0) s2) r))).
      { exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha0 He b. Lstep. Lend R.
    - assert (He : rl (env_repr RE RY) b (ECons a2 y) (c2, cy) (lam (app (app (var 0) s2) r))).
      { exists s2, r. split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Lcall Ha0 He b. Lstep. Lend R.
  Qed.
End LSM.

(** [positive], [N], [Z], [comparison] and [Q]. *)
Module LZM <: ZTimeCostModel LCM LBT LCB.
  Import LCM LBT LCB.
  Definition c_ctor_Z := 1.
  Definition c_case_Z := 1.
  Global Instance Repr_positive : Repr positive unit := ground_repr pos_enc pos_enc_proc.

  Global Instance Repr_N : Repr N unit := ground_repr N_enc N_enc_proc.

  Global Instance Repr_Z : Repr Z unit := ground_repr Z_enc Z_enc_proc.

  Global Instance Repr_Q : Repr Q unit := ground_repr Q_enc Q_enc_proc.

  Global Instance Repr_comparison : Repr comparison unit := ground_repr comp_enc comp_enc_proc.

  Global Instance Size_positive : Size positive := fun p => Pos.size_nat p.
  Global Instance Size_N : Size N := fun n => match n with N0 => 1 | Npos p => S (Pos.size_nat p) end.
  Global Instance Size_Z : Size Z := fun z => match z with Z0 => 1 | Zpos p | Zneg p => S (Pos.size_nat p) end.
  Global Instance Size_Q : Size Q := fun q => S (Size_Z (Qnum q) + Pos.size_nat (Qden q)).
  Global Instance Size_comparison : Size comparison := fun _ => 1.
  Lemma size_xH : (Bounds.size xH = 1)%nat.
  Proof. reflexivity. Qed.
  Lemma size_xO : (forall p, Bounds.size (xO p) = 1 + Bounds.size p)%nat.
  Proof. reflexivity. Qed.
  Lemma size_xI : (forall p, Bounds.size (xI p) = 1 + Bounds.size p)%nat.
  Proof. reflexivity. Qed.
  Lemma size_N0 : (Bounds.size N0 = 1)%nat.
  Proof. reflexivity. Qed.
  Lemma size_Npos : (forall p, Bounds.size (Npos p) = 1 + Bounds.size p)%nat.
  Proof. reflexivity. Qed.
  Lemma size_Z0 : (Bounds.size Z0 = 1)%nat.
  Proof. reflexivity. Qed.
  Lemma size_Zpos : (forall p, Bounds.size (Zpos p) = 1 + Bounds.size p)%nat.
  Proof. reflexivity. Qed.
  Lemma size_Zneg : (forall p, Bounds.size (Zneg p) = 1 + Bounds.size p)%nat.
  Proof. reflexivity. Qed.
  Lemma size_Qmake :
    (forall n d, Bounds.size (Qmake n d) = 1 + Bounds.size n + Bounds.size d)%nat.
  Proof. reflexivity. Qed.
  Lemma size_comparison : (forall c : comparison, Bounds.size c = 1)%nat.
  Proof. reflexivity. Qed.

  Lemma positive_complexity : forall p : positive, ComplexityBound p tt.
  Proof.
    intro x. apply has_complexity_bound. exists (pos_enc x). intro k. reflexivity.
  Qed.

  Lemma N_complexity : forall n : N, ComplexityBound n tt.
  Proof.
    intro x. apply has_complexity_bound. exists (N_enc x). intro k. reflexivity.
  Qed.

  Lemma Z_complexity : forall z : Z, ComplexityBound z tt.
  Proof.
    intro x. apply has_complexity_bound. exists (Z_enc x). intro k. reflexivity.
  Qed.

  Lemma Q_complexity : forall q : Q, ComplexityBound q tt.
  Proof.
    intro x. apply has_complexity_bound. exists (Q_enc x). intro k. reflexivity.
  Qed.

  Lemma comparison_complexity : forall c : comparison, ComplexityBound c tt.
  Proof.
    intro x. apply has_complexity_bound. exists (comp_enc x). intro k. reflexivity.
  Qed.

  Lemma xI_complexity : ComplexityBound xI (fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 2) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma xO_complexity : ComplexityBound xO (fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 1) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Npos_complexity : ComplexityBound Npos (fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (var 0) (var 2))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Zpos_complexity : ComplexityBound Zpos (fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 1) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Zneg_complexity : ComplexityBound Zneg (fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 0) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Qmake_complexity : ComplexityBound Qmake (fun _ => 1 +> fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (app (var 0) (var 2)) (var 1))))). intro k. Lfun. Lstep. Lfun. Lstep. Lground.
  Qed.

  Lemma positive_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@positive_case E A)
      (fun cI : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cO : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cH : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (E -> positive) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cp ce) ⊕
         match val cp (val ce) with
         | xI q => pot cI (ECons (val ce) q ⋊ (pot ce, tt))
         | xO q => pot cO (ECons (val ce) q ⋊ (pot ce, tt))
         | xH => pot cH ce
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE3 (hE1 4) (hE1 3) (hE0 2)).
    LcaseE3_start. Lcall Ha2 Ha3 (j3 - 1). cbn in R. subst v. unfold positive_case.
    set (b := j3 - 1 - cost (c2 (a3 ⋊ c3))).
    destruct (a2 a3) as [q | q |]; cbn [cost res pot val] in *; Lscrut s2 s3.
    - pose proof (pos_enc_proc q).
      assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt)
                     (lam (app (app (var 0) s3) (pos_enc q)))).
      { exists s3, (pos_enc q). split; [reflexivity|].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | exact (ground_rl pos_enc pos_enc_proc b q)]. }
      Lcall Ha He b. Lstep. Lend R.
    - pose proof (pos_enc_proc q).
      assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt)
                     (lam (app (app (var 0) s3) (pos_enc q)))).
      { exists s3, (pos_enc q). split; [reflexivity|].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | exact (ground_rl pos_enc pos_enc_proc b q)]. }
      Lcall Ha0 He b. Lstep. Lend R.
    - Lcall Ha1 Ha3 b. Lstep. Lend R.
  Qed.

  Lemma N_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@N_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (E -> N) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | N0 => pot cz ce
         | Npos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE2 (hE0 3) (hE1 2)).
    LcaseE2_start. Lcall Ha1 Ha2 (j2 - 1). cbn in R. subst v. unfold N_case.
    set (b := j2 - 1 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [| q]; cbn [cost res pot val] in *; Lscrut s1 s2.
    - Lcall Ha Ha2 b. Lstep. Lend R.
    - pose proof (pos_enc_proc q).
      assert (He : rl (env_repr RE Repr_positive) b (ECons a2 q) (c2, tt)
                     (lam (app (app (var 0) s2) (pos_enc q)))).
      { exists s2, (pos_enc q). split; [reflexivity|].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact (ground_rl pos_enc pos_enc_proc b q)]. }
      Lcall Ha0 He b. Lstep. Lend R.
  Qed.

  Lemma Z_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Z_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cx : ℂI (E -> Z) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cx ce) ⊕
         match val cx (val ce) with
         | Z0 => pot cz ce
         | Zpos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         | Zneg p => pot cn (ECons (val ce) p ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE3 (hE0 4) (hE1 3) (hE1 2)).
    LcaseE3_start. Lcall Ha2 Ha3 (j3 - 1). cbn in R. subst v. unfold Z_case.
    set (b := j3 - 1 - cost (c2 (a3 ⋊ c3))).
    destruct (a2 a3) as [| q | q]; cbn [cost res pot val] in *; Lscrut s2 s3.
    - Lcall Ha Ha3 b. Lstep. Lend R.
    - pose proof (pos_enc_proc q).
      assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt)
                     (lam (app (app (var 0) s3) (pos_enc q)))).
      { exists s3, (pos_enc q). split; [reflexivity|].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | exact (ground_rl pos_enc pos_enc_proc b q)]. }
      Lcall Ha0 He b. Lstep. Lend R.
    - pose proof (pos_enc_proc q).
      assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt)
                     (lam (app (app (var 0) s3) (pos_enc q)))).
      { exists s3, (pos_enc q). split; [reflexivity|].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | exact (ground_rl pos_enc pos_enc_proc b q)]. }
      Lcall Ha1 He b. Lstep. Lend R.
  Qed.

  Lemma comparison_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@comparison_case E A)
      (fun cq : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cl : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cg : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cc : ℂI (E -> comparison) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cc ce) ⊕
         match val cc (val ce) with
         | Eq => pot cq ce
         | Lt => pot cl ce
         | Gt => pot cg ce
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE3 (hE0 4) (hE0 3) (hE0 2)).
    LcaseE3_start. Lcall Ha2 Ha3 (j3 - 1). cbn in R. subst v. unfold comparison_case.
    set (b := j3 - 1 - cost (c2 (a3 ⋊ c3))).
    destruct (a2 a3); cbn [cost res pot val] in *; Lscrut s2 s3.
    - Lcall Ha Ha3 b. Lstep. Lend R.
    - Lcall Ha0 Ha3 b. Lstep. Lend R.
    - Lcall Ha1 Ha3 b. Lstep. Lend R.
  Qed.

  Lemma Q_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Q_case E A)
      (fun cf : ℂI (env (env E Z) positive -> A)
                   (ℂI (env (env E Z) positive) ((CE * unit) * unit) -> ℂO CA) => 1 +>
       fun cq : ℂI (E -> Q) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 1 ⊕ cost (pot cq ce) ⊕
         match val cq (val ce) with
         | Qmake n d => pot cf (ECons (ECons (val ce) n) d ⋊ ((pot ce, tt), tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound. exists (caseE1 (hE2 2)).
    LcaseE1_start. Lcall Ha0 Ha1 (j1 - 1). unfold Q_case.
    set (b := j1 - 1 - cost (c0 (a1 ⋊ c1))).
    destruct (a0 a1) as [zn pd]; cbn [rl Repr_Q ground_repr] in R; unfold Q_enc in R;
      cbn [Qnum Qden] in R; subst v; cbn [cost res pot val] in *.
    pose proof (Z_enc_proc zn). pose proof (pos_enc_proc pd).
    assert (He : rl (env_repr (env_repr RE Repr_Z) Repr_positive) b (ECons (ECons a1 zn) pd) ((c1, tt), tt)
                   (lam (app (app (var 0) (lam (app (app (var 0) s1) (Z_enc zn)))) (pos_enc pd)))).
    { exists (lam (app (app (var 0) s1) (Z_enc zn))), (pos_enc pd). split; [reflexivity|].
      split; [| exact (ground_rl pos_enc pos_enc_proc b pd)].
      exists s1, (Z_enc zn). split; [reflexivity|].
      split; [exact (rl_down_ b Ha1 ltac:(unfold b; lia)) | exact (ground_rl Z_enc Z_enc_proc b zn)]. }
    Lcall Ha He b. Lstep. Lend R.
  Qed.

End LZM.

(** Fixpoints. The unfolding equation is pointwise, and the realisers of
    the result do not distinguish pointwise-equal values ([PwExt]). For a
    realiser [se] of [e], [f e] is realised by L's fixpoint operator [rho]
    applied to [fix_G sF se], which runs the realiser [sF] of [F] in the
    environment of [se] and of the recursive function ([env_rl]): by
    induction on the budget, one unfolding takes 4 beta-steps (3 for [rho],
    1 for the environment) and costs at least one, and the recursive calls
    have a smaller budget. [fix_r sF] realises [f]: applied to [se], it is
    [rho (fix_G sF se)] after one beta-step, the cost of the closure. *)
Definition fix_G (sF se : term) : term := lam (app sF (lam (app (app (var 0) se) (var 1)))).
Definition fix_r (sF : term) : term :=
  lam (lam (app (app (app r r) (lam (app sF (lam (app (app (var 0) (var 3)) (var 1)))))) (var 0))).

Lemma fix_r_subst sF se : closed sF -> closed se ->
  subst (lam (app (app (app r r) (lam (app sF (lam (app (app (var 0) (var 3)) (var 1)))))) (var 0))) 0 se
  = rho (fix_G sF se).
Proof.
  intros HsF Hse. unfold rho, fix_G, r. cbn [subst Nat.eqb]. rewrite (HsF 2 se). reflexivity.
Qed.

Module LFX <: FixTimeCostModel LCM LBT LCB.
  Import LCM LBT.
  Definition c_fix := 1.

  Definition PwExt {B CB} (R : Repr B CB) (ar : Arity B) : Prop := pw_ext R ar.
  Existing Class PwExt.
  Global Instance pw_ext_val {B CB} (R : Repr B CB) : PwExt R (ar_val B) := pw_ext_val_ R.
  Global Instance pw_ext_fun {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) (ar : Arity B) :
    PwExt RB ar -> PwExt (Repr_arr RA RB) (ar_fun A B ar) := pw_ext_fun_ RA RB ar.

  Lemma fix_complexity : forall {E CE A B CA CB} `{Repr E CE} `{Repr A CA} {RB : Repr B CB}
      (ar : Arity B) `{!PwExt RB ar} (f : E -> A -> B)
      (F : env E (A -> B) -> A -> B)
      (cF : ℂI (env E (A -> B)) (CE * (ℂI A CA -> ℂO CB)) -> ℂO (ℂI A CA -> ℂO CB))
      (cf : ℂI E CE -> ℂO (ℂI A CA -> ℂO CB)),
      1 <= c_fix ->
      (forall e, is_fixpoint ar (fun g => F (ECons e g)) (f e)) ->
      ComplexityBound F cF ->
      bound_order
        (fun ce : ℂI E CE => 1 +> fun ca : ℂI A CA =>
           1 ⊕ pot <$> (F ⋊ cF) · (ECons (val ce) (f (val ce)) ⋊ (pot ce, res (cf ce))) · ca)
        cf ->
      ComplexityBound f cf.
  Proof.
    intros E CE A B CA CB RE RA RB ar Hpw f F cF cf _ Hfix [sF HF]%complexity_bound_has Hrec.
    apply has_complexity_bound.
    pose proof (rl_proc (HF 0)) as HpF.
    exists (fix_r sF). intro k. unfold fix_r. Lfun.
    destruct (Hrec (a ⋊ c) (rl_wf Ha)) as [Hcost0 Hcomp0].
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I] in Hcost0, Hcomp0.
    set (cfe := res (cf (a ⋊ c))) in *.
    assert (HpG : proc (rho (fix_G sF s)))
      by (split; [apply rho_cls, proc_closed; unfold fix_G; Lproc | apply rho_lambda]).
    (* the recursive function [f a], at every budget up to [j] *)
    assert (Hrho : forall k', k' <= j -> rl (Repr_arr RA RB) k' (f a) cfe (rho (fix_G sF s))).
    { intro k'. induction k' as [k' IH] using (well_founded_induction lt_wf). intro Hk'.
      apply arr_lam; [exact HpG |]. intros j' x c1 sx Hj' Hx Hc'.
      pose proof (rl_proc Hx).
      destruct (Hcomp0 (x ⋊ c1) (rl_wf Hx)) as [Hcost Hcomp].
      cbn [cost res pot val cost_add CostModelCore.app fmap ret_I] in Hcost, Hcomp.
      assert (IHj : rl (Repr_arr RA RB) (j' - 1) (f a) cfe (rho (fix_G sF s))) by (apply IH; Llia).
      assert (Hpair : rl (env_repr RE (Repr_arr RA RB)) (j' - 1) (ECons a (f a)) (c, cfe)
                        (lam (app (app (var 0) s) (rho (fix_G sF s))))).
      { exists s, (rho (fix_G sF s)). split; [reflexivity |].
        split; [exact (rl_down_ (j' - 1) Ha ltac:(Llia)) | exact IHj]. }
      Lcall (HF j') Hpair (j' - 1).
      Lcall R Hx (j' - 1 - cost (cF (ECons a (f a) ⋊ (c, cfe)))).
      do 2 eexists; split.
      { apply evalc_sound. unfold rho at 1, r, fix_G at 1. Leval. }
      split; [Llia |].
      apply (Hpw _ _ _ _ _ (Hfix a x)). eapply rl_mono; [exact Hcomp |]. Lend R0. }
    do 2 eexists; split.
    { apply evalc_sound. eapply evalc_beta; [apply evalc_val; assumption |].
      rewrite fix_r_subst by (try apply proc_closed; assumption). apply evalc_lam. }
    split; [Llia |].
    apply Hrho. Llia.
  Qed.

  Include FixRules LCM LBT LCB.
End LFX.

(** ** The analyses hold in L

    The analyses are functors over the cost model: they can be applied to
    the L instance. For instance, the bound of [Nat.add] proved in
    [NatComplexity] is an L running time. *)

Module L <: TimeCostModel.
  Include LCM. Include LBT. Include LCB. Include LBO. Include LNT.
  Include LLM. Include ListWf LCM LLM. Include LOM. Include OptionGround LCM LOM.
  Include LPM. Include ProdGround LCM LPM. Include LSM. Include SumGround LCM LSM.
  Include LZM. Include LFX.
End L.


