(** * L is an instance of the cost model

    The modules below implement all the parts of the time cost model
    ([CostModel], [BasicTimeCostModel], [CombinatorTimeCostModel],
    [FixTimeCostModel] and the models of the datatypes) with the
    call-by-value lambda-calculus L, and [L] gathers them ([TimeCostModel]).
    Rocq checks that they provide every axiom ([<:]). The analyses, which
    are functors over the cost model, can then be applied to [L]: their
    bounds are L running times).

    - A representation [Repr A CA] is a realisability relation between the
      values of [A] with complexities [CA] and closed L values. It is
      step-indexed by a budget of model cost, which is what
      [fix_complexity] needs.
    - A function with complexity [cf] is realised by an L value whose
      application to the realiser of an argument `a` reduces in at most
      `K * cost (cf a)` steps to a realiser of the result.
    - Ground data are realised by Scott encodings. Lists, options and pairs
      are realised element-wise, so that they are representable whenever
      their elements are. The environments of closures ([Combinators]) are
      pairs of realisers of any representations.
    - Only [fix_complexity] uses an axiom: functional extensionality, to
      turn its pointwise unfolding equation into an equality.

    L and its reduction are those of the Rocq Library of Undecidability
    Proofs (opam package [coq-library-undecidability]): the terms [term],
    the weak call-by-value reduction [step] and its iterations [pow step n].
    The relation is stated with them, so that the costs of the model are L
    running times, up to the factor [K]. L is a reasonable machine model
    (Forster, Kunze & Roth, POPL 2020). The proofs build reductions with
    [evalc], a big-step evaluation that counts beta-steps, which is sound
    and complete for [pow step] ([evalc_sound], [pow_evalc]). *)

From Stdlib Require Import List ZArith QArith FunctionalExtensionality.
From Complexity Require Export TimeCostModel.
From Undecidability.L Require Import Util.L_facts.
Import HOAS_Notations.
Local Open Scope nat_scope.
Unset Implicit Arguments.

(** ** Evaluation with a count of beta-steps *)

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
    needs). It comes with the order on complexities. *)

(** The factor between the costs of the model and the steps of L. *)
Definition K := 8.

Record LRepr (A CA : Type) := {
  rl : nat -> A -> CA -> term -> Prop;
  bo : CA -> CA -> Prop;
  rl_proc : forall k x c s, rl k x c s -> proc s;
  rl_down : forall k k' x c s, k' <= k -> rl k x c s -> rl k' x c s;
  rl_mono : forall k x c c' s, bo c c' -> rl k x c s -> rl k x c' s;
  bo_refl : forall c, bo c c;
  bo_trans : forall c1 c2 c3, bo c1 c2 -> bo c2 c3 -> bo c1 c3 }.
Arguments rl {_ _} _ _ _ _ _.
Arguments bo {_ _} _ _ _.
Arguments rl_proc {_ _ _ _ _ _ _} _.
Arguments rl_down {_ _ _ _ _ _ _ _} _ _.
Arguments rl_mono {_ _ _ _ _ _ _ _} _ _.
Arguments bo_refl {_ _} _ _.
Arguments bo_trans {_ _ _ _ _ _} _ _.

(** Ground data: realised by their encoding, at any budget. *)
Definition ground_repr {A} (e : A -> term) (He : forall x, proc (e x)) : LRepr A unit.
Proof.
  refine {| rl := fun _ x _ s => s = e x; bo := fun _ _ => True |}.
  - intros k x c s ->. apply He.
  - intros k k' x c s _ H. exact H.
  - intros k x c c' s _ H. exact H.
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

Definition arr_bo {A CA B CB} (RB : LRepr B CB) (c c' : ℂI A CA -> ℂO CB) : Prop :=
  forall ca, cost (c ca) <= cost (c' ca) /\ bo RB (res (c ca)) (res (c' ca)).

Definition arr_repr {A CA B CB} (RA : LRepr A CA) (RB : LRepr B CB) :
  LRepr (A -> B) (ℂI A CA -> ℂO CB).
Proof.
  refine {| rl := arr_rl RA RB; bo := @arr_bo A CA B CB RB |}.
  - intros k f c s [H _]. exact H.
  - intros k k' f c s Hk [Hp H]. split; [exact Hp |]. intros j a c1 sa Hj. apply H. lia.
  - intros k f c c' s Hb [Hp H]. split; [exact Hp |].
    intros j a c1 sa Hj Ha Hc. destruct (Hb (a ⋊ c1)) as [Hcost Hcomp].
    destruct (H j a c1 sa Hj Ha ltac:(lia)) as (n & v & Hv & Hn & Hr).
    exists n, v. split; [exact Hv | split; [unfold K in *; lia |]].
    eapply rl_mono; [exact Hcomp |]. eapply rl_down; [| exact Hr]. lia.
  - intros c ca. split; [lia | apply bo_refl].
  - intros c1 c2 c3 H12 H23 ca. destruct (H12 ca), (H23 ca).
    split; [lia | eapply bo_trans; eauto].
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

(** Lists, options and pairs of ground data: realised element-wise. *)
Fixpoint list_rl {A} (P : A -> term -> Prop) (l : list A) (s : term) : Prop :=
  match l with
  | nil => s = lam (lam (var 1))
  | cons x l => exists r t, s = lam (lam (app (app (var 0) r) t)) /\ P x r /\ list_rl P l t
  end.

Definition list_repr {A} (RA : LRepr A unit) : LRepr (list A) unit.
Proof.
  refine {| rl := fun k l _ s => list_rl (fun x r => rl RA k x tt r) l s;
            bo := fun _ _ => True |}.
  - intros k l c s; revert s; induction l as [| x l IH]; cbn; intros s.
    + intros ->. Lproc.
    + intros (r & t & -> & Hr & Ht). pose proof (rl_proc Hr). pose proof (IH _ Ht). Lproc.
  - intros k k' l c s Hk; revert s; induction l as [| x l IH]; cbn; intros s; [auto |].
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_down Hk Hr) | apply IH, Ht]].
  - intros k l c c' s _ H. exact H.
  - auto.
  - auto.
Defined.

Definition option_rl {A} (P : A -> term -> Prop) (o : option A) (s : term) : Prop :=
  match o with
  | Some x => exists r, s = lam (lam (app (var 1) r)) /\ P x r
  | None => s = lam (lam (var 0))
  end.

Definition option_repr {A} (RA : LRepr A unit) : LRepr (option A) unit.
Proof.
  refine {| rl := fun k o _ s => option_rl (fun x r => rl RA k x tt r) o s;
            bo := fun _ _ => True |}.
  - intros k [x |] c s; cbn.
    + intros (r & -> & Hr). pose proof (rl_proc Hr). Lproc.
    + intros ->. Lproc.
  - intros k k' [x |] c s Hk; cbn; [| auto].
    intros (r & -> & Hr). exists r. split; [reflexivity | exact (rl_down Hk Hr)].
  - intros k o c c' s _ H. exact H.
  - auto.
  - auto.
Defined.

Definition prod_rl {A B} (P1 : A -> term -> Prop) (P2 : B -> term -> Prop) (p : A * B)
  (s : term) : Prop :=
  exists r1 r2, s = lam (app (app (var 0) r1) r2) /\ P1 (fst p) r1 /\ P2 (snd p) r2.

Definition prod_repr {A B} (RA : LRepr A unit) (RB : LRepr B unit) : LRepr (A * B) unit.
Proof.
  refine {| rl := fun k p _ s => prod_rl (fun x r => rl RA k x tt r) (fun y r => rl RB k y tt r) p s;
            bo := fun _ _ => True |}.
  - intros k p c s (r1 & r2 & -> & H1 & H2).
    pose proof (rl_proc H1). pose proof (rl_proc H2). Lproc.
  - intros k k' p c s Hk (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k p c c' s _ H. exact H.
  - auto.
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
            bo := fun c c' => bo RE (fst c) (fst c') /\ bo RA (snd c) (snd c') |}.
  - intros k e c s (r1 & r2 & -> & H1 & H2).
    pose proof (rl_proc H1). pose proof (rl_proc H2). Lproc.
  - intros k k' e c s Hk (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k e c c' s [B1 B2] (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_mono B1 H1) | exact (rl_mono B2 H2)]].
  - intros c. split; apply bo_refl.
  - intros c1 c2 c3 [B1 B2] [B3 B4]. split; [exact (bo_trans B1 B3) | exact (bo_trans B2 B4)].
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
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hc |- *].

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

(** Case analyses apply the encoding of the value to one closure per
    constructor, and the selected closure to [Ic_r]: the closure of a
    constructor with [m] arguments takes them, then a dummy argument, and
    calls the branch. Branches of constant constructors get [tt]. *)
Definition hU (i : nat) := lam (app (var i) unit_enc).
Definition h1 (i : nat) := lam (lam (app (var i) (var 1))).
Definition h2 (i : nat) := lam (lam (lam (app (app (var i) (var 2)) (var 1)))).

Definition case1_r (x : term) := lam (lam (app (app (var 0) x) Ic_r)).
Definition case2_r (x y : term) := lam (lam (lam (app (app (app (var 0) x) y) Ic_r))).
Definition case3_r (x y z : term) :=
  lam (lam (lam (lam (app (app (app (app (var 0) x) y) z) Ic_r)))).

Ltac Lunfold_r := cbv [case1_r case2_r case3_r hU h1 h2 Ic_r unit_enc]; intro k.
Ltac Lcase1_start := Lunfold_r; Lfun; Lstep; Lfun.
Ltac Lcase_start := Lunfold_r; Lfun; Lstep; Lfun; Lstep; Lfun.
Ltac Lcase3_start := Lunfold_r; Lfun; Lstep; Lfun; Lstep; Lfun; Lstep; Lfun.

(** The unfolding equation of [fix_complexity] is pointwise. *)
Lemma pw_eq_eq {T} (ar : Arity T) : forall x y, pw_eq ar x y -> x = y.
Proof.
  induction ar as [T | A B ar IH]; cbn; [auto |].
  intros f g H. apply functional_extensionality. intro a. apply IH, H.
Qed.

(** ** L is an instance of the cost model *)

Module LCM <: CostModel.
  Definition Repr := LRepr.
  Existing Class Repr.
  Abbreviation Ground A := (Repr A unit).

  Global Instance Repr_unit : Ground unit :=
    ground_repr (fun _ => unit_enc) (fun _ => unit_enc_proc).

  (** The size of ground data is the size of its encoding, as an L term
      (element-wise for lists, options and pairs). *)
  Global Instance Size_unit : Size unit := fun _ => L_facts.size unit_enc.
  Lemma size_tt : 0 < CostModelCore.size tt.
  Proof. cbv. lia. Qed.

  Global Instance Repr_arr {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) :
    Repr (A -> B) (ℂI A CA -> ℂO CB) := arr_repr RA RB.

  (** [x] has complexity [c]: some L value realises it, at every budget. *)
  Definition has_complexity {A CA} {R : Repr A CA} (x : A) (c : CA) : Prop :=
    exists s, forall k, rl R k x c s.

  Definition bound_order {A CA} {R : Repr A CA} (c c' : CA) : Prop := bo R c c'.

  Global Instance bound_order_po {A CA} {R : Repr A CA} : PreOrder (@bound_order A CA R) :=
    ltac:(split; [intro c; apply bo_refl | intros c1 c2 c3; apply bo_trans]).

  Lemma bound_order_arr {A CA B CB} {RA : Repr A CA} {RB : Repr B CB}
    (c c' : ℂI A CA -> ℂO CB) :
    (forall ca, cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.
  Proof. intro H. exact H. Qed.

  (** The complexity bounds ([Complexities]). The bounds of L are its
      complexities: realisability is monotone in the complexity. *)
  Include Complexities.

  Lemma complexity_bound_has {A CA} {R : Repr A CA} (f : A) (c : CA) :
    ComplexityBound f c -> has_complexity f c.
  Proof. intros [(c0 & Hc & s & H)]. exists s. intro k. exact (rl_mono Hc (H k)). Qed.

  (** The bounds in the size of the inputs ([Bounds]). *)
  Include Bounds.
End LCM.

(** Higher-order primitives. *)
Module LBT <: BasicTimeCostModel LCM.
  Import LCM.
  (** Every application is a beta-step. *)
  Definition c_clo := 1.
  Definition c_step := 1.

  Lemma id_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (fun (x : A) => x) (fun ca => (1 ⋉ pot ca) : ℂO CA).
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
      ComplexityBound (fun (_ : A) => b) (fun _ => 1 ⋉ cb).
  Proof.
    intros A B CA CB RA RB b cb [sb Hb]%complexity_bound_has. apply has_complexity_bound.
    exists (lam sb). intro k. pose proof (rl_proc (Hb 0)).
    Lfun. Lstep. apply Hb.
  Qed.

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

  Lemma ehd_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@ehd E A) (fun ce => 1 ⋉ snd (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists ehd_r. intro k. Lfun.
    destruct Ha as (r1 & r2 & -> & Hr1 & Hr2). pose proof (rl_proc Hr1). pose proof (rl_proc Hr2).
    Lstep. Lend Hr2.
  Qed.

  Lemma etl_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@etl E A) (fun ce => 1 ⋉ fst (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists etl_r. intro k. Lfun.
    destruct Ha as (r1 & r2 & -> & Hr1 & Hr2). pose proof (rl_proc Hr1). pose proof (rl_proc Hr2).
    Lstep. Lend Hr1.
  Qed.

  Lemma Lam_complexity : forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => 1 ⋉
       fun ce : ℂI E CE => 1 ⋉
       fun ca : ℂI A CA => 1 ⊕ pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))).
  Proof.
    intros. apply has_complexity_bound. exists Lam_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    assert (He : rl (env_repr _ _) j1 (ECons a0 a1) (c0, c1)
                   (lam (app (app (var 0) s0) s1)))
      by (exists s0, s1; split; [reflexivity | split; [exact (rl_down_ j1 Ha0 ltac:(lia)) | exact Ha1]]).
    Lcall Ha He (j1 - 1). Lstep. Lend R.
  Qed.

  Lemma Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
      ComplexityBound (@Kc A B) (fun ca => 1 ⋉ (fun _ => 1 ⋉ pot ca)).
  Proof.
    intros. apply has_complexity_bound. exists Kc_r. intro k. Lfun. Lstep. Lfun. Lstep. Lend Ha.
  Qed.

  Lemma Ic_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (@Ic A) (fun ca => 1 ⋉ pot ca).
  Proof.
    intros. apply has_complexity_bound. exists Ic_r. intro k. Lfun. Lstep. Lend Ha.
  Qed.

  Lemma compose_hcomplexity : forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 1 ⋉
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 ⋉
       fun ca : ℂI A CA => 1 ⊕ pot <$> cf · (cg · ca)).
  Proof.
    intros. apply has_complexity_bound. exists compose_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    Lcall Ha0 Ha1 (j1 - 1). Lcall Ha R (j1 - 1 - cost (c0 (a1 ⋊ c1))).
    Lstep. Lend R0.
  Qed.

  Lemma Cc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 ⋉
       fun ca : ℂI A CA => 1 ⋉
       fun cx : ℂI X CX => 1 ⊕ pot <$> cf · cx · ca).
  Proof.
    intros. apply has_complexity_bound. exists Cc_r. intro k. Lfun. Lstep. Lfun. Lstep. Lfun.
    Lcall Ha Ha1 (j1 - 1). Lcall R Ha0 (j1 - 1 - cost (c (a1 ⋊ c1))).
    Lstep. Lend R0.
  Qed.

  Lemma Sc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 ⋉
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 1 ⋉
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
Module LNT <: NatTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_S := 1.
  Definition c_case_nat := 1.
  Global Instance Repr_nat : Ground nat := ground_repr nat_enc' nat_enc_proc.

  Global Instance Size_nat : Size nat := fun n => L_facts.size (nat_enc' n).
  Lemma size_O : 0 < CostModelCore.size 0.
  Proof. cbv. lia. Qed.
  Lemma size_S : forall n, CostModelCore.size n < CostModelCore.size (S n).
  Proof. intro n. unfold CostModelCore.size, Size_nat. cbn. lia. Qed.

  Lemma nat_complexity : forall n : nat, ComplexityBound n tt.
  Proof.
    intro n. apply has_complexity_bound. exists (nat_enc' n). intro k. reflexivity.
  Qed.

  Lemma S_complexity : ComplexityBound S (fun x => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (var 0) (var 2))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma nat_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@nat_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cs : ℂI (nat -> A) (ℂI nat unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI nat unit => 1 ⊕
         match val cn with O => pot cz (tt ⋊ tt) | S k => pot cs (k ⋊ tt) end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case2_r (hU 3) (h1 3)). Lcase_start.
    destruct a1 as [| m]; cbn in Ha1; subst s1; cbn [cost res pot val] in *.
    - Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
    - pose proof (nat_enc_proc m).
      Lcall Ha0 (ground_rl nat_enc' nat_enc_proc (j1 - 1) m) (j1 - 1). Lstep. Lend R.
  Qed.

End LNT.

(** [bool]. *)
Module LBO <: BoolTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_case_bool := 1.
  Global Instance Repr_bool : Ground bool := ground_repr bool_enc bool_enc_proc.

  Global Instance Size_bool : Size bool := fun b => L_facts.size (bool_enc b).
  Lemma size_bool : forall b : bool, 0 < CostModelCore.size b.
  Proof. intros []; cbv; lia. Qed.

  Lemma bool_complexity : forall b : bool, ComplexityBound b tt.
  Proof.
    intro b. apply has_complexity_bound. exists (bool_enc b). intro k. reflexivity.
  Qed.

  Lemma bool_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@bool_case A)
      (fun ct : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cf : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cb : ℂI bool unit => 1 ⊕
         if val cb then pot ct (tt ⋊ tt) else pot cf (tt ⋊ tt)).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case2_r (hU 3) (hU 2)). Lcase_start.
    destruct a1; cbn in Ha1; subst s1; cbn [cost res pot val] in *.
    - Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
    - Lcall Ha0 (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
  Qed.

End LBO.

(** Lists. *)
Module LLM <: ListTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_cons := 1.
  Definition c_case_list := 1.
  Global Instance Repr_list {A} (RA : Ground A) : Ground (list A) := list_repr RA.

  Global Instance Size_list {A} (SA : Size A) : Size (list A) :=
    fix size_list l := match l with nil => 4 | a :: l => 5 + SA a + size_list l end.
  Lemma size_nil : forall {A} `{Size A}, 0 < CostModelCore.size (@nil A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_cons : forall {A} `{Size A} (a : A) l,
    CostModelCore.size a + CostModelCore.size l < CostModelCore.size (a :: l).
  Proof. intros. unfold CostModelCore.size at 3. cbn. unfold CostModelCore.size. lia. Qed.

  Lemma nil_complexity : forall {A} `{Ground A}, ComplexityBound (@nil A) tt.
  Proof.
    intros A RA. apply has_complexity_bound. exists (lam (lam (var 1))). intro k. reflexivity.
  Qed.

  Lemma cons_complexity : forall {A : Type} `{Ground A},
      ComplexityBound (@cons A)
                      (fun h => 1 ⋉ ( 
                       fun t => 1 ⋉ tt)).
  Proof.
    intros A RA. apply has_complexity_bound.
    exists (lam (lam (lam (lam (app (app (var 0) (var 3)) (var 2)))))). intro k.
    Lfun. destruct c. Lstep. Lfun. Lstep. cbn [rl Repr_list list_repr list_rl].
    exists s, s0. split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - exact (rl_down_ (j0 - 1) Ha0 ltac:(lia)).
  Qed.

  Lemma list_case_complexity : forall {X A CA} `{Ground X} `{Repr A CA},
    ComplexityBound (@list_case X A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cc : ℂI (X -> list X -> A) (ℂI X unit -> ℂO (ℂI (list X) unit -> ℂO CA)) => 1 ⋉
       fun cl : ℂI (list X) unit => 1 ⊕
         match val cl with
         | nil => pot cz (tt ⋊ tt)
         | cons h t => pot <$> cc · (h ⋊ tt) · (t ⋊ tt)
         end).
  Proof.
    intros X A CA RX RA. apply has_complexity_bound. exists (case2_r (hU 3) (h2 4)). Lcase_start.
    destruct a1 as [| x l]; cbn in Ha1;
      cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in *.
    - subst s1. Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
    - destruct Ha1 as (r & t & -> & Hr & Ht). pose proof (rl_proc Hr).
      assert (Ht' : rl (Repr_list RX) j1 l tt t) by exact Ht. pose proof (rl_proc Ht').
      Lcall Ha0 Hr (j1 - 1). Lcall R Ht' (j1 - 1 - cost (c0 (x ⋊ tt))).
      Lstep. Lend R0.
  Qed.

End LLM.

(** Options. *)
Module LOM <: OptionTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_Some := 1.
  Definition c_case_option := 1.
  Global Instance Repr_option {A} (RA : Ground A) : Ground (option A) := option_repr RA.

  Global Instance Size_option {A} (SA : Size A) : Size (option A) :=
    fun o => match o with None => 3 | Some a => 5 + SA a end.
  Lemma size_None : forall {A} `{Size A}, 0 < CostModelCore.size (@None A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_Some : forall {A} `{Size A} (a : A), CostModelCore.size a < CostModelCore.size (Some a).
  Proof. intros. cbv. lia. Qed.

  Lemma None_complexity : forall {A} `{Ground A}, ComplexityBound (@None A) tt.
  Proof.
    intros A RA. apply has_complexity_bound. exists (lam (lam (var 0))). intro k. reflexivity.
  Qed.

  Lemma Some_complexity : forall {A} `{Ground A},
      ComplexityBound (@Some A) (fun _ => 1 ⋉ tt).
  Proof.
    intros A RA. apply has_complexity_bound. exists (lam (lam (lam (app (var 1) (var 2))))). intro k.
    Lfun. destruct c. Lstep. cbn [rl Repr_option option_repr option_rl].
    exists s. split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma option_case_complexity : forall {X A CA} `{Ground X} `{Repr A CA},
    ComplexityBound (@option_case X A)
      (fun cs : ℂI (X -> A) (ℂI X unit -> ℂO CA) => 1 ⋉
       fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun co : ℂI (option X) unit => 1 ⊕
         match val co with
         | Some x => pot cs (x ⋊ tt)
         | None => pot cz (tt ⋊ tt)
         end).
  Proof.
    intros X A CA RX RA. apply has_complexity_bound. exists (case2_r (h1 4) (hU 2)). Lcase_start.
    destruct a1 as [x |]; cbn in Ha1; cbn [cost res pot val] in *.
    - destruct Ha1 as (r & -> & Hr). pose proof (rl_proc Hr).
      Lcall Ha Hr (j1 - 1). Lstep. Lend R.
    - subst s1. Lcall Ha0 (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
  Qed.

End LOM.

(** Pairs. *)
Module LPM <: ProdTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_pair := 1.
  Definition c_case_prod := 1.
  Global Instance Repr_prod {A B} (RA : Ground A) (RB : Ground B) : Ground (A * B) :=
    prod_repr RA RB.

  Global Instance Size_prod {A B} (SA : Size A) (SB : Size B) : Size (A * B) :=
    fun p => 4 + SA (fst p) + SB (snd p).
  Lemma size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    CostModelCore.size a + CostModelCore.size b < CostModelCore.size (a, b).
  Proof. intros. cbv. lia. Qed.

  Lemma pair_complexity : forall {A B} `{Ground A} `{Ground B},
      ComplexityBound (@pair A B) (fun _ => 1 ⋉ fun _ => 1 ⋉ tt).
  Proof.
    intros A B RA RB. apply has_complexity_bound.
    exists (lam (lam (lam (app (app (var 0) (var 2)) (var 1))))). intro k.
    Lfun. destruct c. Lstep. Lfun. destruct c. Lstep.
    cbn [rl Repr_prod prod_repr prod_rl fst snd]. exists s, s0. split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - eapply rl_down; [| exact Ha0]. lia.
  Qed.

  Lemma prod_case_complexity : forall {X Y A CA} `{Ground X} `{Ground Y} `{Repr A CA},
    ComplexityBound (@prod_case X Y A)
      (fun cf : ℂI (X -> Y -> A) (ℂI X unit -> ℂO (ℂI Y unit -> ℂO CA)) => 1 ⋉
       fun cp : ℂI (X * Y) unit => 1 ⊕
         let (x, y) := val cp in
         pot <$> cf · (x ⋊ tt) · (y ⋊ tt)).
  Proof.
    intros X Y A CA RX RY RA. apply has_complexity_bound. exists (case1_r (h2 4)). Lcase1_start.
    destruct a0 as [x y]; cbn [rl Repr_prod prod_repr prod_rl fst snd] in Ha0;
      cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in *.
    destruct Ha0 as (r1 & r2 & -> & H1 & H2). cbn [fst snd] in H1, H2.
    pose proof (rl_proc H1). pose proof (rl_proc H2).
    Lcall Ha H1 (j0 - 1). Lcall R H2 (j0 - 1 - cost (c (x ⋊ tt))).
    Lstep. Lend R0.
  Qed.

End LPM.

(** [positive], [N], [Z], [comparison] and [Q]. *)
Module LZM <: ZTimeCostModel LCM LBT.
  Import LCM LBT.
  Definition c_ctor_Z := 1.
  Definition c_case_Z := 1.
  Global Instance Repr_positive : Ground positive := ground_repr pos_enc pos_enc_proc.

  Global Instance Repr_N : Ground N := ground_repr N_enc N_enc_proc.

  Global Instance Repr_Z : Ground Z := ground_repr Z_enc Z_enc_proc.

  Global Instance Repr_Q : Ground Q := ground_repr Q_enc Q_enc_proc.

  Global Instance Repr_comparison : Ground comparison := ground_repr comp_enc comp_enc_proc.

  Global Instance Size_positive : Size positive := fun p => L_facts.size (pos_enc p).
  Global Instance Size_N : Size N := fun n => L_facts.size (N_enc n).
  Global Instance Size_Z : Size Z := fun z => L_facts.size (Z_enc z).
  Global Instance Size_Q : Size Q := fun q => L_facts.size (Q_enc q).
  Global Instance Size_comparison : Size comparison := fun c => L_facts.size (comp_enc c).
  Ltac lsize := unfold CostModelCore.size, Size_positive, Size_N, Size_Z, Size_Q, Size_comparison;
    cbn; lia.
  Lemma size_xH : (0 < CostModelCore.size xH)%nat.
  Proof. lsize. Qed.
  Lemma size_xO : (forall p, CostModelCore.size p < CostModelCore.size (xO p))%nat.
  Proof. intro. lsize. Qed.
  Lemma size_xI : (forall p, CostModelCore.size p < CostModelCore.size (xI p))%nat.
  Proof. intro. lsize. Qed.
  Lemma size_N0 : (0 < CostModelCore.size N0)%nat.
  Proof. lsize. Qed.
  Lemma size_Npos : (forall p, CostModelCore.size p < CostModelCore.size (Npos p))%nat.
  Proof. intro. lsize. Qed.
  Lemma size_Z0 : (0 < CostModelCore.size Z0)%nat.
  Proof. lsize. Qed.
  Lemma size_Zpos : (forall p, CostModelCore.size p < CostModelCore.size (Zpos p))%nat.
  Proof. intro. lsize. Qed.
  Lemma size_Zneg : (forall p, CostModelCore.size p < CostModelCore.size (Zneg p))%nat.
  Proof. intro. lsize. Qed.
  Lemma size_Qmake : (forall n d, CostModelCore.size n + CostModelCore.size d < CostModelCore.size (Qmake n d))%nat.
  Proof. intros. lsize. Qed.
  Lemma size_comparison : (forall c : comparison, 0 < CostModelCore.size c)%nat.
  Proof. intros []; lsize. Qed.

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

  Lemma xI_complexity : ComplexityBound xI (fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 2) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma xO_complexity : ComplexityBound xO (fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 1) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Npos_complexity : ComplexityBound Npos (fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (var 0) (var 2))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Zpos_complexity : ComplexityBound Zpos (fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 1) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Zneg_complexity : ComplexityBound Zneg (fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (lam (app (var 0) (var 3)))))). intro k. Lfun. Lstep. Lground.
  Qed.

  Lemma Qmake_complexity : ComplexityBound Qmake (fun _ => 1 ⋉ fun _ => 1 ⋉ tt).
  Proof.
    apply has_complexity_bound. exists (lam (lam (lam (app (app (var 0) (var 2)) (var 1))))). intro k. Lfun. Lstep. Lfun. Lstep. Lground.
  Qed.

  Lemma positive_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@positive_case A)
      (fun cI : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cO : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cH : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI positive unit => 1 ⊕
         match val cp with
         | xI q => pot cI (q ⋊ tt)
         | xO q => pot cO (q ⋊ tt)
         | xH => pot cH (tt ⋊ tt)
         end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case3_r (h1 5) (h1 4) (hU 2)). Lcase3_start.
    destruct a2 as [q | q |]; cbn in Ha2; subst s2; cbn [cost res pot val] in *.
    - pose proof (pos_enc_proc q). Lcall Ha (ground_rl pos_enc pos_enc_proc (j2 - 1) q) (j2 - 1). Lstep. Lend R.
    - pose proof (pos_enc_proc q). Lcall Ha0 (ground_rl pos_enc pos_enc_proc (j2 - 1) q) (j2 - 1). Lstep. Lend R.
    - Lcall Ha1 (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j2 - 1) tt) (j2 - 1). Lstep. Lend R.
  Qed.

  Lemma N_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@N_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI N unit => 1 ⊕
         match val cn with N0 => pot cz (tt ⋊ tt) | Npos p => pot cp (p ⋊ tt) end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case2_r (hU 3) (h1 3)). Lcase_start.
    destruct a1 as [| q]; cbn in Ha1; subst s1; cbn [cost res pot val] in *.
    - Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j1 - 1) tt) (j1 - 1). Lstep. Lend R.
    - pose proof (pos_enc_proc q). Lcall Ha0 (ground_rl pos_enc pos_enc_proc (j1 - 1) q) (j1 - 1). Lstep. Lend R.
  Qed.

  Lemma Z_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Z_case A)
      (fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cp : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cn : ℂI (positive -> A) (ℂI positive unit -> ℂO CA) => 1 ⋉
       fun cx : ℂI Z unit => 1 ⊕
         match val cx with
         | Z0 => pot cz (tt ⋊ tt)
         | Zpos p => pot cp (p ⋊ tt)
         | Zneg p => pot cn (p ⋊ tt)
         end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case3_r (hU 4) (h1 4) (h1 3)). Lcase3_start.
    destruct a2 as [| q | q]; cbn in Ha2; subst s2; cbn [cost res pot val] in *.
    - Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j2 - 1) tt) (j2 - 1). Lstep. Lend R.
    - pose proof (pos_enc_proc q). Lcall Ha0 (ground_rl pos_enc pos_enc_proc (j2 - 1) q) (j2 - 1). Lstep. Lend R.
    - pose proof (pos_enc_proc q). Lcall Ha1 (ground_rl pos_enc pos_enc_proc (j2 - 1) q) (j2 - 1). Lstep. Lend R.
  Qed.

  Lemma comparison_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@comparison_case A)
      (fun ce : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cl : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cg : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cc : ℂI comparison unit => 1 ⊕
         match val cc with
         | Eq => pot ce (tt ⋊ tt)
         | Lt => pot cl (tt ⋊ tt)
         | Gt => pot cg (tt ⋊ tt)
         end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case3_r (hU 4) (hU 3) (hU 2)). Lcase3_start.
    destruct a2; cbn in Ha2; subst s2; cbn [cost res pot val] in *.
    - Lcall Ha (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j2 - 1) tt) (j2 - 1). Lstep. Lend R.
    - Lcall Ha0 (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j2 - 1) tt) (j2 - 1). Lstep. Lend R.
    - Lcall Ha1 (ground_rl (fun _ => unit_enc) (fun _ => unit_enc_proc) (j2 - 1) tt) (j2 - 1). Lstep. Lend R.
  Qed.

  Lemma Q_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Q_case A)
      (fun cf : ℂI (Z -> positive -> A) (ℂI Z unit -> ℂO (ℂI positive unit -> ℂO CA)) => 1 ⋉
       fun cq : ℂI Q unit => 1 ⊕
         match val cq with
         | Qmake n d => pot <$> cf · (n ⋊ tt) · (d ⋊ tt)
         end).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (case1_r (h2 4)). Lcase1_start.
    destruct a0 as [n d]; cbn [rl Repr_Q ground_repr] in Ha0; unfold Q_enc in Ha0;
      cbn [Qnum Qden] in Ha0; subst s0;
      cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in *.
    pose proof (Z_enc_proc n). pose proof (pos_enc_proc d).
    Lcall Ha (ground_rl Z_enc Z_enc_proc (j0 - 1) n) (j0 - 1).
    Lcall R (ground_rl pos_enc pos_enc_proc (j0 - 1) d) (j0 - 1 - cost (c (n ⋊ tt))).
    Lstep. Lend R0.
  Qed.

End LZM.

(** Fixpoints. The unfolding equation, pointwise, gives `f = F f` with functional extensionality. [f] is realised by L's fixpoint operator [rho] applied to a realiser of `F`, by induction on the budget: one unfolding takes 3 beta-steps and costs at least one, and the recursive calls have a smaller budget. *)
Module LFX <: FixTimeCostModel LCM LBT LCB.
  Import LCM LBT.
  Definition c_fix := 1.

  Lemma fix_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
      (ar : Arity B) (f : A -> B)
      (F : (A -> B) -> A -> B)
      (cF : ℂI (A -> B) (ℂI A CA -> ℂO CB) -> ℂO (ℂI A CA -> ℂO CB))
      (cf : ℂI A CA -> ℂO CB),
      1 <= c_fix ->
      is_fixpoint ar F f ->
      ComplexityBound F cF ->
      bound_order (fun ca : ℂI A CA => 1 ⊕ pot <$> (F ⋊ cF) · (f ⋊ cf) · ca) cf ->
      ComplexityBound f cf.
  Proof.
    intros A B CA CB RA RB ar f F cF cf _ Hfix [sF HF]%complexity_bound_has Hrec.
    apply has_complexity_bound.
    assert (Heq : forall a, f a = F f a) by (intro a; apply (pw_eq_eq ar), Hfix).
    pose proof (rl_proc (HF 0)) as HpF.
    assert (Hprho : proc (rho sF)) by (split; [apply rho_cls, HpF | apply rho_lambda]).
    exists (rho sF). intro k. induction k as [k IH] using (well_founded_induction lt_wf).
    apply arr_lam; [exact Hprho |]. intros j a c1 sa Hj Ha Hc.
    pose proof (rl_proc Ha).
    destruct (Hrec (a ⋊ c1)) as [Hcost Hcomp].
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hcost, Hcomp.
    assert (IHj : rl (Repr_arr RA RB) (j - 1) f cf (rho sF)) by (apply IH; Llia).
    Lcall (HF j) IHj (j - 1).
    Lcall R Ha (j - 1 - cost (cF (f ⋊ cf))).
    do 2 eexists; split.
    { apply evalc_sound. unfold rho, r. Leval. }
    split; [Llia |].
    rewrite Heq. eapply rl_mono; [exact Hcomp |]. Lend R0.
  Qed.

End LFX.

(** ** The analyses hold in L

    The analyses are functors over the cost model: they can be applied to
    the L instance. For instance, the bound of [Nat.add] proved in
    [NatComplexity] is an L running time. *)

Module L <: TimeCostModel.
  Include LCM. Include LBT. Include LCB. Include LBO. Include LNT. Include LLM. Include LOM.
  Include LPM. Include LZM. Include LFX.
End L.

