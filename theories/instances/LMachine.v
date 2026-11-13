(** * An environment machine for L, as an instance of the cost model

    [LInstance] measures time in β-steps of L, where a step substitutes
    a value in a term at no cost, and where there is no stack. This file
    takes a machine closer to an implementation: an environment machine
    for the same terms, whose values are closures (a term and the values of
    its free variables), and which counts
    - the read of a variable in the environment, a list: [n + 1] for the
      variable [n];
    - the allocation of a closure, for a λ: [1];
    - a β-step: [1];
    - a frame, pushed and popped, for each subterm of an application that
      is not a value (a variable or a λ): [2]. The body of the function is
      evaluated in tail position, without a frame: a tail call is cheaper
      than another call.
    Data are encoded as in [LInstance] (Scott encodings), as closures.

    It proves the whole time cost model, with the constants of the machine
    ([MachineTimeCostModel], [machine/MachineCostModel]): a combinator costs
    at most [c_step = 16] steps of the machine, the projections of the
    environments being the dearest (environments are Scott-encoded pairs);
    a non-tail evaluation [c_frame = 2]. [LM] gathers the layers, with
    lists and options of ground data, and [LMH] with lists and options of
    any data ([MachineHOTimeCostModel]). *)

From Stdlib Require Import List Lia PeanoNat FunctionalExtensionality PArith NArith ZArith QArith.
From Complexity Require Export MachineCostModel.
From Undecidability.L Require Import L.
Import ListNotations.
Local Open Scope nat_scope.

(** ** The machine *)

(** A closure: the value of [lam s] in the environment [E]. *)
#[warnings="-register-all"]
Inductive value : Type := clos (s : term) (E : list value).

Definition is_value_term (t : term) : bool := match t with app _ _ => false | _ => true end.

(** The cost of the frame of a subterm of an application: [2] if it has
    to be evaluated (pushed, then popped), [0] for a value. *)
Definition frame (t : term) : nat := if is_value_term t then 0 else 2.

(** [ev E s v n]: [s], in the environment [E], evaluates to [v] in [n]
    steps of the machine. *)
Inductive ev : list value -> term -> value -> nat -> Prop :=
| ev_var E n v : nth_error E n = Some v -> ev E (var n) v (S n)
| ev_lam E s : ev E (lam s) (clos s E) 1
| ev_app E s t u E' w v k1 k2 k3 :
    ev E s (clos u E') k1 -> ev E t w k2 -> ev (w :: E') u v k3 ->
    ev E (app s t) v (S (k1 + k2 + k3 + frame s + frame t)).

(** The application of a closure [f] to a value [w]: its body, in its
    environment extended with [w] (in tail position). *)
Definition call (f w v : value) (n : nat) : Prop :=
  match f with clos u E => ev (w :: E) u v n end.

Lemma ev_det E s v n : ev E s v n -> forall v' n', ev E s v' n' -> v = v' /\ n = n'.
Proof.
  induction 1 as [E n v H | E s | E s t u E' w v k1 k2 k3 H1 IH1 H2 IH2 H3 IH3];
    intros v' n' H'; inversion H'; subst.
  - match goal with Hn : nth_error _ _ = Some v' |- _ => rewrite H in Hn; injection Hn as -> end.
    auto.
  - auto.
  - match goal with
    | G1 : ev _ s (clos _ _) _, G2 : ev _ t _ _, G3 : ev _ _ v' _ |- _ =>
        destruct (IH1 _ _ G1) as [Ee ->]; injection Ee as <- <-;
        destruct (IH2 _ _ G2) as [<- ->]; destruct (IH3 _ _ G3) as [<- ->]; auto
    end.
Qed.

Lemma call_det f w v n v' n' : call f w v n -> call f w v' n' -> v = v' /\ n = n'.
Proof. destruct f. intros H1 H2. exact (ev_det _ _ _ _ H1 _ _ H2). Qed.

(** [Mev] builds an evaluation, from the evaluations of the calls of
    abstract closures in the context. *)
Ltac Mev :=
  first
    [ eassumption
    | apply ev_lam
    | eapply ev_var; reflexivity
    | eapply ev_app; [Mev | Mev | first [eassumption | Mev]] ].

(** ** Representations

    As in [LInstance]: a realisability relation [rl k x c v], step-indexed
    by a budget [k] of model cost, and the order on complexities. *)
Record MRepr (A CA : Type) := {
  rl : nat -> A -> CA -> value -> Prop;
  bo : CA -> CA -> Prop;
  rl_down : forall k k' x c v, k' <= k -> rl k x c v -> rl k' x c v;
  rl_mono : forall k x c c' v, bo c c' -> rl k x c v -> rl k x c' v;
  bo_refl : forall c, bo c c;
  bo_trans : forall c1 c2 c3, bo c1 c2 -> bo c2 c3 -> bo c1 c3 }.
Arguments rl {_ _} _ _ _ _ _.
Arguments bo {_ _} _ _ _.
Arguments rl_down {_ _ _ _ _ _ _ _} _ _.
Arguments rl_mono {_ _ _ _ _ _ _ _} _ _.
Arguments bo_refl {_ _} _ _.
Arguments bo_trans {_ _ _ _ _ _} _ _.

Lemma rl_down_ {A CA} {R : MRepr A CA} {k x c v} (k' : nat) :
  rl R k x c v -> k' <= k -> rl R k' x c v.
Proof. intros H Hk. exact (rl_down Hk H). Qed.

Definition ground_repr {A} (e : A -> value) : MRepr A unit.
Proof.
  refine {| rl := fun _ x _ v => v = e x; bo := fun _ _ => True |}; auto.
Defined.

(** Functions: applied to a realiser of an argument whose cost fits in the
    budget, a realiser evaluates its body, in at most this cost, to a
    realiser of the result. *)
Definition arr_rl {A CA B CB} (RA : MRepr A CA) (RB : MRepr B CB)
  (k : nat) (f : A -> B) (cf : ℂI A CA -> ℂO CB) (v : value) : Prop :=
  forall j a c1 w, j <= k -> rl RA j a c1 w -> cost (cf (a ⋊ c1)) <= j ->
    exists r n, call v w r n /\ n <= cost (cf (a ⋊ c1)) /\
      rl RB (j - cost (cf (a ⋊ c1))) (f a) (res (cf (a ⋊ c1))) r.

Definition arr_bo {A CA B CB} (RB : MRepr B CB) (c c' : ℂI A CA -> ℂO CB) : Prop :=
  forall ca, cost (c ca) <= cost (c' ca) /\ bo RB (res (c ca)) (res (c' ca)).

Definition arr_repr {A CA B CB} (RA : MRepr A CA) (RB : MRepr B CB) :
  MRepr (A -> B) (ℂI A CA -> ℂO CB).
Proof.
  refine {| rl := arr_rl RA RB; bo := @arr_bo A CA B CB RB |}.
  - intros k k' f c v Hk H j a c1 w Hj. apply H. lia.
  - intros k f c c' v Hb H j a c1 w Hj Ha Hc. destruct (Hb (a ⋊ c1)) as [Hcost Hcomp].
    destruct (H j a c1 w Hj Ha ltac:(lia)) as (r & n & Hv & Hn & Hr).
    exists r, n. split; [exact Hv | split; [lia |]].
    eapply rl_mono; [exact Hcomp |]. eapply rl_down; [| exact Hr]. lia.
  - intros c ca. split; [lia | apply bo_refl].
  - intros c1 c2 c3 H12 H23 ca. destruct (H12 ca), (H23 ca).
    split; [lia | eapply bo_trans; eauto].
Defined.

(** Introduce an argument of a function being realised. *)
Ltac Mfun :=
  let j := fresh "j" in let a := fresh "a" in let c := fresh "c" in
  let w := fresh "w" in let Hj := fresh "Hj" in let Ha := fresh "Ha" in
  let Hc := fresh "Hc" in let u := fresh "wu" in let E := fresh "wE" in
  intros j a c w Hj Ha Hc; destruct w as [u E];
  cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hc |- *.

(** Apply the realiser [Hf] of a function to the realiser [Ha] of an
    argument, with the budget [J]. *)
Ltac Mcall Hf Ha J :=
  let r := fresh "r" in let n := fresh "n" in let E := fresh "E" in
  let N := fresh "N" in let R := fresh "R" in
  edestruct (Hf J _ _ _ ltac:(lia) (rl_down_ J Ha ltac:(lia)) ltac:(lia)) as (r & n & E & N & R);
  cbn [cost res pot val call] in N, R, E.

(** Evaluate, check the cost, and leave the realisability of the result. *)
Ltac Mstep := do 2 eexists; split; [cbn [call]; Mev | split; [cbn; lia |]].
Ltac Mend H := eapply rl_down; [| exact H]; cbn [cost res pot val] in *; lia.

(** ** Encodings, as closures *)

Definition unit_enc : value := clos (var 0) [].
Definition bool_enc (b : bool) : value := if b then clos (lam (var 1)) [] else clos (lam (var 0)) [].
Fixpoint nat_enc (n : nat) : value :=
  match n with O => clos (lam (var 1)) [] | S n => clos (lam (app (var 0) (var 2))) [nat_enc n] end.

(** Pairs (the environments of closures, [Combinators]): applied to [f],
    [f x y] for the values [x] (at position 2) and [y] (at position 1) of
    their environment. *)
Definition pair_body : term := app (app (var 0) (var 2)) (var 1).

Definition env_rl {E CE A CA} (RE : MRepr E CE) (RA : MRepr A CA) (k : nat) (e : env E A)
  (c : CE * CA) (v : value) : Prop :=
  exists r1 r2 rest, v = clos pair_body (r2 :: r1 :: rest) /\
    rl RE k (etl e) (fst c) r1 /\ rl RA k (ehd e) (snd c) r2.

Definition env_repr {E CE A CA} (RE : MRepr E CE) (RA : MRepr A CA) :
  MRepr (env E A) (CE * CA).
Proof.
  refine {| rl := env_rl RE RA;
            bo := fun c c' => bo RE (fst c) (fst c') /\ bo RA (snd c) (snd c') |}.
  - intros k k' e c v Hk (r1 & r2 & rest & -> & H1 & H2). exists r1, r2, rest.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k e c c' v [B1 B2] (r1 & r2 & rest & -> & H1 & H2). exists r1, r2, rest.
    split; [reflexivity | split; [exact (rl_mono B1 H1) | exact (rl_mono B2 H2)]].
  - intros c. split; apply bo_refl.
  - intros c1 c2 c3 [B1 B2] [B3 B4]. split; [exact (bo_trans B1 B3) | exact (bo_trans B2 B4)].
Defined.

(** ** The cost model *)

Module MCM <: CostModel.
  Definition Repr := MRepr.
  Existing Class Repr.
  Abbreviation Ground A := (Repr A unit).

  Global Instance Repr_unit : Ground unit := ground_repr (fun _ => unit_enc).
  Global Instance Size_unit : Size unit := fun _ => 1.
  Lemma size_tt : 0 < CostModelCore.size tt.
  Proof. cbv. lia. Qed.

  Global Instance Repr_arr {A CA B CB} (RA : Repr A CA) (RB : Repr B CB) :
    Repr (A -> B) (ℂI A CA -> ℂO CB) := arr_repr RA RB.

  Definition has_complexity {A CA} {R : Repr A CA} (x : A) (c : CA) : Prop :=
    exists v, forall k, rl R k x c v.

  Definition bound_order {A CA} {R : Repr A CA} (c c' : CA) : Prop := bo R c c'.

  Global Instance bound_order_po {A CA} {R : Repr A CA} : PreOrder (@bound_order A CA R) :=
    ltac:(split; [intro c; apply bo_refl | intros c1 c2 c3; apply bo_trans]).

  Lemma bound_order_arr {A CA B CB} {RA : Repr A CA} {RB : Repr B CB}
    (c c' : ℂI A CA -> ℂO CB) :
    (forall ca, cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.
  Proof. intro H. exact H. Qed.

  Include Complexities.

  Lemma complexity_bound_has {A CA} {R : Repr A CA} (f : A) (c : CA) :
    ComplexityBound f c -> has_complexity f c.
  Proof. intros [(c0 & Hc & v & H)]. exists v. intro k. exact (rl_mono Hc (H k)). Qed.

  Include Bounds.
  Include HOBounds.
End MCM.

Module MBT <: BasicTimeCostModel MCM.
  Import MCM.
  (** A partial application of a combinator allocates a closure; a full
      application costs at most [16] steps (the projections of an
      environment); a frame [2]. *)
  Definition c_clo := 1.
  Definition c_step := 16.
  Definition c_frame := 2.

  Lemma id_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (fun (x : A) => x) (fun ca => (16 +> pot ca) : ℂO CA).
  Proof.
    intros A CA R. apply has_complexity_bound. exists (clos (var 0) []). intro k. Mfun.
    Mstep. Mend Ha.
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
    destruct (Hf c c v cv sv ltac:(lia) (Hv c) ltac:(lia)) as (r0 & n0 & E0 & _ & R0).
    exists r0. intro k.
    destruct (Hf (k + c) (k + c) v cv sv ltac:(lia) (Hv (k + c)) ltac:(lia))
      as (r1 & n1 & E1 & _ & R1).
    destruct (call_det _ _ _ _ _ _ E0 E1) as [<- _].
    eapply rl_down; [| exact R1]. lia.
  Qed.

  Lemma compose_complexity : forall {A B C CA CB CC}
      `{Repr A CA} `{Repr B CB} `{Repr C CC}
      (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
      ComplexityBound f cf ->
      ComplexityBound g cg ->
      ComplexityBound (compose f g : A -> C)
                      (fun ca => 16 ⊕ pot <$> (f ⋊ cf) · (2 ⊕ (g ⋊ cg) · ca)).
  Proof.
    intros A B C CA CB CC RA RB RC f cf g cg [sf Hf]%complexity_bound_has
      [sg Hg]%complexity_bound_has.
    apply has_complexity_bound.
    destruct sf as [uf Ef], sg as [ug Eg].
    exists (clos (app (var 2) (app (var 1) (var 0))) [clos ug Eg; clos uf Ef]). intro k. Mfun.
    Mcall (Hg j) Ha (j - 16).
    Mcall (Hf j) R (j - 16 - 2 - cost (cg (a ⋊ c))).
    Mstep. Mend R0.
  Qed.

  Lemma constant_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB} b {cb},
      ComplexityBound (b : B) (cb : CB) ->
      ComplexityBound (fun (_ : A) => b) (fun _ => 16 +> cb).
  Proof.
    intros A B CA CB RA RB b cb [sb Hb]%complexity_bound_has. apply has_complexity_bound.
    exists (clos (var 1) [sb]). intro k. Mfun. Mstep. apply Hb.
  Qed.

  Lemma tt_complexity : ComplexityBound tt tt.
  Proof. apply has_complexity_bound. exists unit_enc. intro k. reflexivity. Qed.
End MBT.

(** ** Combinators *)

Module MCB <: CombinatorTimeCostModel MCM MBT.
  Import MCM MBT.
  Global Instance Repr_env {E CE A CA} (RE : Repr E CE) (RA : Repr A CA) :
    Repr (env E A) (CE * CA) := env_repr RE RA.

  (** A pair applied to a selector: [15] steps for the second component,
      [16] for the first. *)
  Lemma ehd_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@ehd E A) (fun ce => 16 +> snd (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists (clos (app (var 0) (lam (lam (var 0)))) []).
    intro k. Mfun. destruct Ha as (r1 & r2 & rest & Ep & Hr1 & Hr2). injection Ep as -> ->.
    Mstep. Mend Hr2.
  Qed.

  Lemma etl_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@etl E A) (fun ce => 16 +> fst (pot ce)).
  Proof.
    intros. apply has_complexity_bound. exists (clos (app (var 0) (lam (lam (var 1)))) []).
    intro k. Mfun. destruct Ha as (r1 & r2 & rest & Ep & Hr1 & Hr2). injection Ep as -> ->.
    Mstep. Mend Hr1.
  Qed.

  Lemma Lam_complexity : forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => 1 +>
       fun ce : ℂI E CE => 1 +>
       fun ca : ℂI A CA => 16 ⊕ pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))).
  Proof.
    intros E CE A CA B CB RE RA RB. apply has_complexity_bound.
    exists (clos (lam (lam (app (var 2) (lam pair_body)))) []). intro k.
    Mfun. Mstep. Mfun. Mstep. Mfun.
    assert (He : rl (env_repr RE RA) (j1 - 16) (ECons a0 a1) (c0, c1)
                   (clos pair_body (clos wu1 wE1 :: clos wu0 wE0 :: [clos wu wE]))).
    { exists (clos wu0 wE0), (clos wu1 wE1), [clos wu wE]. split; [reflexivity |].
      split; [exact (rl_down_ (j1 - 16) Ha0 ltac:(lia)) | exact (rl_down_ (j1 - 16) Ha1 ltac:(lia))]. }
    Mcall Ha He (j1 - 16). Mstep. Mend R.
  Qed.

  Lemma Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
      ComplexityBound (@Kc A B) (fun ca => 1 +> (fun _ => 16 +> pot ca)).
  Proof.
    intros. apply has_complexity_bound. exists (clos (lam (var 1)) []). intro k.
    Mfun. Mstep. Mfun. Mstep. Mend Ha.
  Qed.

  Lemma Ic_complexity : forall {A CA} `{Repr A CA},
      ComplexityBound (@Ic A) (fun ca => 16 +> pot ca).
  Proof.
    intros. apply has_complexity_bound. exists (clos (var 0) []). intro k. Mfun. Mstep. Mend Ha.
  Qed.

  Lemma compose_hcomplexity : forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 1 +>
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +>
       fun ca : ℂI A CA => 16 ⊕ pot <$> cf · (2 ⊕ cg · ca)).
  Proof.
    intros. apply has_complexity_bound.
    exists (clos (lam (lam (app (var 2) (app (var 1) (var 0))))) []). intro k.
    Mfun. Mstep. Mfun. Mstep. Mfun.
    Mcall Ha0 Ha1 (j1 - 16). Mcall Ha R (j1 - 16 - 2 - cost (c0 (a1 ⋊ c1))).
    Mstep. Mend R0.
  Qed.

  Lemma Cc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 +>
       fun ca : ℂI A CA => 1 +>
       fun cx : ℂI X CX => 16 ⊕ pot <$> (2 ⊕ cf · cx) · ca).
  Proof.
    intros. apply has_complexity_bound.
    exists (clos (lam (lam (app (app (var 2) (var 0)) (var 1)))) []). intro k.
    Mfun. Mstep. Mfun. Mstep. Mfun.
    Mcall Ha Ha1 (j1 - 16). destruct r as [ur Er].
    Mcall R Ha0 (j1 - 16 - 2 - cost (c (a1 ⋊ c1))).
    Mstep. Mend R0.
  Qed.

  Lemma Sc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 +>
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 1 +>
       fun cx : ℂI X CX => 16 ⊕ pot <$> (2 ⊕ cf · cx) · (2 ⊕ cg · cx)).
  Proof.
    intros. apply has_complexity_bound.
    exists (clos (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0))))) []). intro k.
    Mfun. Mstep. Mfun. Mstep. Mfun.
    Mcall Ha Ha1 (j1 - 16). destruct r as [ur Er].
    Mcall Ha0 Ha1 (j1 - 16 - 2 - cost (c (a1 ⋊ c1))).
    Mcall R R0 (j1 - 16 - 2 - cost (c (a1 ⋊ c1)) - 2 - cost (c0 (a1 ⋊ c1))).
    Mstep. Mend R1.
  Qed.

  Include CombinatorTactics MCM MBT.
End MCB.

(** ** Case analyses

    As in [LInstance]: the realiser of a case combinator applies the
    matched value, a Scott encoding, to a handler for each constructor, then
    to a dummy argument. The handler of a constructor without arguments is
    [λ _. b e], for its branch [b]; the handler of a constructor with
    arguments builds the environment of its branch, with pairs in the shape
    that [ehd] and [etl] read ([pair_body]), then waits for the dummy. *)

(** The case realiser for two constructors, of handlers [h1] and [h2]: the
    body of [λ z c o e. o e h1 h2 (λ x. x)]. *)
Definition case2_body (h1 h2 : term) : term :=
  lam (lam (lam (app (app (app (app (var 1) (var 0)) h1) h2) (lam (var 0))))).

(** The handler of a constructor without arguments, in the context
    [_; e; o; c; z] (or [_; e; o; t; f] for booleans): the branch at
    position [b + 1], applied to [e]. *)
Definition h0 (b : nat) : term := lam (app (var (S b)) (var 1)).

(** The handler of a constructor with one argument [m]: the pair [(e, m)],
    then [λ _. c p], for the branch [c] at position [b] of the body of the
    realiser ([b + 3] in the handler). *)
Definition h1_pair_at (b : nat) : term :=
  lam (app (lam (lam (app (var (b + 3)) (var 1)))) (lam pair_body)).
Definition h1_pair : term := h1_pair_at 2.

(** The handler of a constructor with two arguments [h] and [t] (as
    [cons]): the pairs [(e, h)] and [((e, h), t)]. *)
Definition h2_pair_at (b : nat) : term :=
  lam (app (lam (lam (app (lam (lam (app (var (b + 5)) (var 1)))) (lam pair_body)))) (lam pair_body)).
Definition h2_pair : term := h2_pair_at 2.

(** The case realisers for one and three constructors. *)
Definition case1_body (h : term) : term :=
  lam (lam (app (app (app (var 1) (var 0)) h) (lam (var 0)))).
Definition case3_body (h1 h2 h3 : term) : term :=
  lam (lam (lam (lam (app (app (app (app (app (var 1) (var 0)) h1) h2) h3) (lam (var 0)))))).

Definition list_cons_body : term := lam (app (app (var 0) (var 3)) (var 2)).

Fixpoint list_rl {A} (P : A -> value -> Prop) (l : list A) (v : value) : Prop :=
  match l with
  | nil => v = clos (lam (var 1)) []
  | cons x l => exists r t, v = clos list_cons_body [t; r] /\ P x r /\ list_rl P l t
  end.

Definition list_repr {A} (RA : MRepr A unit) : MRepr (list A) unit.
Proof.
  refine {| rl := fun k l _ v => list_rl (fun x r => rl RA k x tt r) l v;
            bo := fun _ _ => True |}.
  - intros k k' l c v Hk; revert v; induction l as [| x l IH]; cbn; intros v; [auto |].
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_down Hk Hr) | apply IH, Ht]].
  - intros k l c c' v _ H. exact H.
  - auto.
  - auto.
Defined.

Ltac Mcase_start := intro k; Mfun; Mstep; Mfun; Mstep; Mfun; Mstep; Mfun.
Ltac Mcase1_start := intro k; Mfun; Mstep; Mfun; Mstep; Mfun.
Ltac Mcase3_start := intro k; Mfun; Mstep; Mfun; Mstep; Mfun; Mstep; Mfun; Mstep; Mfun.

Module MBO <: BoolTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_case_bool := 25.
  Global Instance Repr_bool : Ground bool := ground_repr bool_enc.
  Global Instance Size_bool : Size bool := fun _ => 1.
  Lemma size_bool : forall b : bool, 0 < CostModelCore.size b.
  Proof. intros; cbv; lia. Qed.

  Lemma bool_complexity : forall b : bool, ComplexityBound b tt.
  Proof. intro b. apply has_complexity_bound. exists (bool_enc b). intro k. reflexivity. Qed.

  Lemma bool_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@bool_case E A)
      (fun ct : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cf : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cb : ℂI (E -> bool) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 25 ⊕ 2 ⊕ cost (pot cb ce) ⊕
         if val cb (val ce) then pot ct ce else pot cf ce).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h0 3) (h0 2)) []). unfold case2_body, h0. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 25 - 2). unfold bool_case.
    set (b := j2 - 25 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2); cbn in R; subst r; cbn [cost res pot val] in *.
    - Mcall Ha Ha2 b. Mstep. Mend R.
    - Mcall Ha0 Ha2 b. Mstep. Mend R.
  Qed.
End MBO.

Module MNT <: NatTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_S := 1.
  Definition c_case_nat := 33.
  Global Instance Repr_nat : Ground nat := ground_repr nat_enc.
  Global Instance Size_nat : Size nat := fun n => S n.
  Lemma size_O : 0 < CostModelCore.size 0.
  Proof. cbv. lia. Qed.
  Lemma size_S : forall n, CostModelCore.size n < CostModelCore.size (S n).
  Proof. intro n. cbv. lia. Qed.

  Lemma nat_complexity : forall n : nat, ComplexityBound n tt.
  Proof. intro n. apply has_complexity_bound. exists (nat_enc n). intro k. reflexivity. Qed.

  Lemma S_complexity : ComplexityBound S (fun x => 1 >|).
  Proof.
    apply has_complexity_bound. exists (clos (lam (lam (app (var 0) (var 2)))) []). intro k.
    Mfun. Mstep. cbn in Ha |- *. rewrite Ha. reflexivity.
  Qed.

  Lemma nat_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@nat_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cs : ℂI (env E nat -> A) (ℂI (env E nat) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (E -> nat) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 33 ⊕ 2 ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | O => pot cz ce
         | S k => pot cs (ECons (val ce) k ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h0 3) h1_pair) []). unfold case2_body, h0, h1_pair, h1_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 33 - 2). unfold nat_case.
    set (b := j2 - 33 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [| m]; cbn in R; subst r; cbn [cost res pot val] in *.
    - Mcall Ha Ha2 b. Mstep. Mend R.
    - assert (He : rl (env_repr RE Repr_nat) b (ECons a2 m) (c2, tt)
                     (clos pair_body [nat_enc m; clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE])).
      { exists (clos wu2 wE2), (nat_enc m), [clos wu1 wE1; clos wu0 wE0; clos wu wE].
        split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha0 He b. Mstep. Mend R.
  Qed.
End MNT.

Module MLM <: ListTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_cons := 1.
  Definition c_case_list := 46.
  Global Instance Repr_list {A} (RA : Ground A) : Ground (list A) := list_repr RA.

  Global Instance Size_list {A} (SA : Size A) : Size (list A) :=
    fix size_list l := match l with nil => 4 | a :: l => 5 + SA a + size_list l end.
  Lemma size_nil : forall {A} `{Size A}, 0 < CostModelCore.size (@nil A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_cons : forall {A} `{Size A} (a : A) l,
    CostModelCore.size a + CostModelCore.size l < CostModelCore.size (a :: l).
  Proof. intros. unfold CostModelCore.size at 3. cbn. unfold CostModelCore.size. lia. Qed.

  Lemma nil_complexity : forall {A} `{Ground A}, ComplexityBound (@nil A) tt.
  Proof. intros A RA. apply has_complexity_bound. exists (clos (lam (var 1)) []). intro k. reflexivity. Qed.

  Lemma cons_complexity : forall {A : Type} `{Ground A},
      ComplexityBound (@cons A) (fun h => 1 +> (fun t => 1 >|)).
  Proof.
    intros A RA. apply has_complexity_bound. exists (clos (lam (lam list_cons_body)) []). intro k.
    Mfun. destruct c. Mstep. Mfun. Mstep. cbn [rl Repr_list list_repr list_rl].
    exists (clos wu wE), (clos wu0 wE0). split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - exact (rl_down_ (j0 - 1) Ha0 ltac:(lia)).
  Qed.

  Lemma list_case_complexity : forall {X E CE A CA} `{Ground X} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@list_case X E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cc : ℂI (env (env E X) (list X) -> A)
                   (ℂI (env (env E X) (list X)) ((CE * unit) * unit) -> ℂO CA) => 1 +>
       fun cl : ℂI (E -> list X) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 46 ⊕ 2 ⊕ cost (pot cl ce) ⊕
         match val cl (val ce) with
         | nil => pot cz ce
         | cons h t => pot cc (ECons (ECons (val ce) h) t ⋊ ((pot ce, tt), tt))
         end).
  Proof.
    intros X E CE A CA RX RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h0 3) h2_pair) []). unfold case2_body, h0, h2_pair, h2_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 46 - 2). unfold list_case.
    set (b := j2 - 46 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [| x l]; cbn in R; cbn [cost res pot val] in *.
    - subst r. Mcall Ha Ha2 b. Mstep. Mend R.
    - destruct R as (r1 & t & -> & Hr & Ht).
      set (rest := [clos wu1 wE1; clos wu0 wE0; clos wu wE]).
      set (p1 := clos pair_body (r1 :: clos wu2 wE2 :: rest)).
      assert (He : rl (env_repr (env_repr RE RX) (Repr_list RX)) b (ECons (ECons a2 x) l) ((c2, tt), tt)
                     (clos pair_body (t :: p1 :: r1 :: clos wu2 wE2 :: rest))).
      { exists p1, t, (r1 :: clos wu2 wE2 :: rest). split; [reflexivity |].
        split; [| exact Ht].
        exists (clos wu2 wE2), r1, rest. split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Mcall Ha0 He b. subst p1 rest. Mstep. Mend R.
  Qed.
End MLM.

(** ** Options, pairs and binary numbers (of ground data) *)

Definition option_rl {A} (P : A -> value -> Prop) (o : option A) (v : value) : Prop :=
  match o with
  | Some x => exists r, v = clos (lam (app (var 1) (var 2))) [r] /\ P x r
  | None => v = clos (lam (var 0)) []
  end.

Definition option_repr {A} (RA : MRepr A unit) : MRepr (option A) unit.
Proof.
  refine {| rl := fun k o _ v => option_rl (fun x r => rl RA k x tt r) o v;
            bo := fun _ _ => True |}.
  - intros k k' [x |] c v Hk; cbn; [| auto].
    intros (r & -> & Hr). exists r. split; [reflexivity | exact (rl_down Hk Hr)].
  - intros k o c c' v _ H. exact H.
  - auto.
  - auto.
Defined.

Definition prod_rl {A B} (P1 : A -> value -> Prop) (P2 : B -> value -> Prop) (p : A * B)
  (v : value) : Prop :=
  exists r1 r2, v = clos pair_body [r2; r1] /\ P1 (fst p) r1 /\ P2 (snd p) r2.

Definition prod_repr {A B} (RA : MRepr A unit) (RB : MRepr B unit) : MRepr (A * B) unit.
Proof.
  refine {| rl := fun k p _ v => prod_rl (fun x r => rl RA k x tt r) (fun y r => rl RB k y tt r) p v;
            bo := fun _ _ => True |}.
  - intros k k' p c v Hk (r1 & r2 & -> & H1 & H2). exists r1, r2.
    split; [reflexivity | split; [exact (rl_down Hk H1) | exact (rl_down Hk H2)]].
  - intros k p c c' v _ H. exact H.
  - auto.
  - auto.
Defined.

Fixpoint pos_enc (p : positive) : value :=
  match p with
  | xI q => clos (lam (lam (app (var 2) (var 3)))) [pos_enc q]
  | xO q => clos (lam (lam (app (var 1) (var 3)))) [pos_enc q]
  | xH => clos (lam (lam (var 0))) []
  end.
Definition N_enc (n : N) : value :=
  match n with N0 => clos (lam (var 1)) [] | Npos p => clos (lam (app (var 0) (var 2))) [pos_enc p] end.
Definition Z_enc (z : Z) : value :=
  match z with
  | Z0 => clos (lam (lam (var 2))) []
  | Zpos p => clos (lam (lam (app (var 1) (var 3)))) [pos_enc p]
  | Zneg p => clos (lam (lam (app (var 0) (var 3)))) [pos_enc p]
  end.
Definition comp_enc (c : comparison) : value :=
  match c with
  | Eq => clos (lam (lam (var 2))) []
  | Lt => clos (lam (lam (var 1))) []
  | Gt => clos (lam (lam (var 0))) []
  end.
Definition Q_enc (q : Q) : value := clos pair_body [pos_enc (Qden q); Z_enc (Qnum q)].

Module MOM <: OptionTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_Some := 1.
  Definition c_case_option := 35.
  Global Instance Repr_option {A} (RA : Ground A) : Ground (option A) := option_repr RA.
  Global Instance Size_option {A} (SA : Size A) : Size (option A) :=
    fun o => match o with None => 3 | Some a => 5 + SA a end.
  Lemma size_None : forall {A} `{Size A}, 0 < CostModelCore.size (@None A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_Some : forall {A} `{Size A} (a : A), CostModelCore.size a < CostModelCore.size (Some a).
  Proof. intros. cbv. lia. Qed.

  Lemma None_complexity : forall {A} `{Ground A}, ComplexityBound (@None A) tt.
  Proof. intros A RA. apply has_complexity_bound. exists (clos (lam (var 0)) []). intro k. reflexivity. Qed.

  Lemma Some_complexity : forall {A} `{Ground A}, ComplexityBound (@Some A) (fun _ => 1 >|).
  Proof.
    intros A RA. apply has_complexity_bound. exists (clos (lam (lam (app (var 1) (var 2)))) []).
    intro k. Mfun. destruct c. Mstep. cbn [rl Repr_option option_repr option_rl].
    exists (clos wu wE). split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma option_case_complexity : forall {X E CE A CA} `{Ground X} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * unit) -> ℂO CA) => 1 +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 35 ⊕ 2 ⊕ cost (pot co ce) ⊕
         match val co (val ce) with
         | Some x => pot cs (ECons (val ce) x ⋊ (pot ce, tt))
         | None => pot cz ce
         end).
  Proof.
    intros X E CE A CA RX RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h1_pair_at 3) (h0 2)) []). unfold case2_body, h0, h1_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 35 - 2). unfold option_case.
    set (b := j2 - 35 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [x |]; cbn in R; cbn [cost res pot val] in *.
    - destruct R as (rx & -> & Hr).
      assert (He : rl (env_repr RE RX) b (ECons a2 x) (c2, tt)
                     (clos pair_body [rx; clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE])).
      { exists (clos wu2 wE2), rx, [clos wu1 wE1; clos wu0 wE0; clos wu wE]. split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Mcall Ha He b. Mstep. Mend R.
    - subst r. Mcall Ha0 Ha2 b. Mstep. Mend R.
  Qed.
End MOM.

Module MPM <: ProdTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_pair := 1.
  Definition c_case_prod := 39.
  Global Instance Repr_prod {A B} (RA : Ground A) (RB : Ground B) : Ground (A * B) := prod_repr RA RB.
  Global Instance Size_prod {A B} (SA : Size A) (SB : Size B) : Size (A * B) :=
    fun p => 4 + SA (fst p) + SB (snd p).
  Lemma size_pair : forall {A B} `{Size A} `{Size B} (a : A) (b : B),
    CostModelCore.size a + CostModelCore.size b < CostModelCore.size (a, b).
  Proof. intros. cbv. lia. Qed.

  Lemma pair_complexity : forall {A B} `{Ground A} `{Ground B},
      ComplexityBound (@pair A B) (fun _ => 1 +> fun _ => 1 >|).
  Proof.
    intros A B RA RB. apply has_complexity_bound. exists (clos (lam (lam pair_body)) []). intro k.
    Mfun. destruct c. Mstep. Mfun. destruct c. Mstep.
    cbn [rl Repr_prod prod_repr prod_rl fst snd]. exists (clos wu wE), (clos wu0 wE0).
    split; [reflexivity | split].
    - eapply rl_down; [| exact Ha]. lia.
    - eapply rl_down; [| exact Ha0]. lia.
  Qed.

  Lemma prod_case_complexity :
    forall {X Y E CE A CA} `{Ground X} `{Ground Y} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@prod_case X Y E A)
      (fun cf : ℂI (env (env E X) Y -> A) (ℂI (env (env E X) Y) ((CE * unit) * unit) -> ℂO CA) =>
         1 +>
       fun cp : ℂI (E -> X * Y) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 39 ⊕ 2 ⊕ cost (pot cp ce) ⊕
         let (x, y) := val cp (val ce) in
         pot cf (ECons (ECons (val ce) x) y ⋊ ((pot ce, tt), tt))).
  Proof.
    intros X Y E CE A CA RX RY RE RA. apply has_complexity_bound.
    exists (clos (case1_body (h2_pair_at 2)) []). unfold case1_body, h2_pair_at. Mcase1_start.
    Mcall Ha0 Ha1 (j1 - 39 - 2). unfold prod_case.
    set (b := j1 - 39 - 2 - cost (c0 (a1 ⋊ c1))).
    destruct (a0 a1) as [x y]; cbn [rl Repr_prod prod_repr prod_rl fst snd] in R;
      cbn [cost res pot val] in *.
    destruct R as (r1 & r2 & -> & Hr1 & Hr2).
    set (rest := [clos wu0 wE0; clos wu wE]).
    set (p1 := clos pair_body (r1 :: clos wu1 wE1 :: rest)).
    assert (He : rl (env_repr (env_repr RE RX) RY) b (ECons (ECons a1 x) y) ((c1, tt), tt)
                   (clos pair_body (r2 :: p1 :: r1 :: clos wu1 wE1 :: rest))).
    { exists p1, r2, (r1 :: clos wu1 wE1 :: rest). split; [reflexivity |].
      split; [| exact Hr2].
      exists (clos wu1 wE1), r1, rest. split; [reflexivity |].
      split; [exact (rl_down_ b Ha1 ltac:(unfold b; lia)) | exact Hr1]. }
    Mcall Ha He b. subst p1 rest. Mstep. Mend R.
  Qed.
End MPM.

Module MZM <: ZTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_ctor_Z := 1.
  Definition c_case_Z := 43.
  Global Instance Repr_positive : Ground positive := ground_repr pos_enc.
  Global Instance Repr_N : Ground N := ground_repr N_enc.
  Global Instance Repr_Z : Ground Z := ground_repr Z_enc.
  Global Instance Repr_Q : Ground Q := ground_repr Q_enc.
  Global Instance Repr_comparison : Ground comparison := ground_repr comp_enc.

  Global Instance Size_positive : Size positive := fun p => Pos.size_nat p.
  Global Instance Size_N : Size N := fun n => S (N.size_nat n).
  Global Instance Size_Z : Size Z := fun z => match z with Z0 => 1 | Zpos p | Zneg p => S (Pos.size_nat p) end.
  Global Instance Size_Q : Size Q := fun q => S (Size_Z (Qnum q) + Pos.size_nat (Qden q)).
  Global Instance Size_comparison : Size comparison := fun _ => 1.
  Ltac msize := unfold CostModelCore.size, Size_positive, Size_N, Size_Z, Size_Q, Size_comparison;
    cbn; try lia.
  Lemma pos_size_pos p : 0 < Pos.size_nat p.
  Proof. destruct p; cbn; lia. Qed.
  Lemma size_xH : (0 < CostModelCore.size xH)%nat.
  Proof. msize. Qed.
  Lemma size_xO : (forall p, CostModelCore.size p < CostModelCore.size (xO p))%nat.
  Proof. intro. msize. Qed.
  Lemma size_xI : (forall p, CostModelCore.size p < CostModelCore.size (xI p))%nat.
  Proof. intro. msize. Qed.
  Lemma size_N0 : (0 < CostModelCore.size N0)%nat.
  Proof. msize. Qed.
  Lemma size_Npos : (forall p, CostModelCore.size p < CostModelCore.size (Npos p))%nat.
  Proof. intro. msize. Qed.
  Lemma size_Z0 : (0 < CostModelCore.size Z0)%nat.
  Proof. msize. Qed.
  Lemma size_Zpos : (forall p, CostModelCore.size p < CostModelCore.size (Zpos p))%nat.
  Proof. intro. msize. Qed.
  Lemma size_Zneg : (forall p, CostModelCore.size p < CostModelCore.size (Zneg p))%nat.
  Proof. intro. msize. Qed.
  Lemma size_Qmake : (forall n d, CostModelCore.size n + CostModelCore.size d < CostModelCore.size (Qmake n d))%nat.
  Proof. intros n d. msize. destruct n; cbn; lia. Qed.
  Lemma size_comparison : (forall c : comparison, 0 < CostModelCore.size c)%nat.
  Proof. intros. msize. Qed.

  Lemma positive_complexity : forall p : positive, ComplexityBound p tt.
  Proof. intro x. apply has_complexity_bound. exists (pos_enc x). intro k. reflexivity. Qed.
  Lemma N_complexity : forall n : N, ComplexityBound n tt.
  Proof. intro x. apply has_complexity_bound. exists (N_enc x). intro k. reflexivity. Qed.
  Lemma Z_complexity : forall z : Z, ComplexityBound z tt.
  Proof. intro x. apply has_complexity_bound. exists (Z_enc x). intro k. reflexivity. Qed.
  Lemma Q_complexity : forall q : Q, ComplexityBound q tt.
  Proof. intro x. apply has_complexity_bound. exists (Q_enc x). intro k. reflexivity. Qed.
  Lemma comparison_complexity : forall c : comparison, ComplexityBound c tt.
  Proof. intro x. apply has_complexity_bound. exists (comp_enc x). intro k. reflexivity. Qed.

  Ltac Mctor := intro k; Mfun; Mstep; cbn in * |- *;
    match goal with H : clos _ _ = _ |- _ => rewrite H end; reflexivity.
  Lemma xI_complexity : ComplexityBound xI (fun _ => 1 >|).
  Proof. apply has_complexity_bound. exists (clos (lam (lam (lam (app (var 2) (var 3))))) []). Mctor. Qed.
  Lemma xO_complexity : ComplexityBound xO (fun _ => 1 >|).
  Proof. apply has_complexity_bound. exists (clos (lam (lam (lam (app (var 1) (var 3))))) []). Mctor. Qed.
  Lemma Npos_complexity : ComplexityBound Npos (fun _ => 1 >|).
  Proof. apply has_complexity_bound. exists (clos (lam (lam (app (var 0) (var 2)))) []). Mctor. Qed.
  Lemma Zpos_complexity : ComplexityBound Zpos (fun _ => 1 >|).
  Proof. apply has_complexity_bound. exists (clos (lam (lam (lam (app (var 1) (var 3))))) []). Mctor. Qed.
  Lemma Zneg_complexity : ComplexityBound Zneg (fun _ => 1 >|).
  Proof. apply has_complexity_bound. exists (clos (lam (lam (lam (app (var 0) (var 3))))) []). Mctor. Qed.
  Lemma Qmake_complexity : ComplexityBound Qmake (fun _ => 1 +> fun _ => 1 >|).
  Proof.
    apply has_complexity_bound. exists (clos (lam (lam pair_body)) []). intro k.
    Mfun. Mstep. Mfun. Mstep. cbn in Ha, Ha0 |- *. rewrite Ha, Ha0. reflexivity.
  Qed.

  Lemma positive_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@positive_case E A)
      (fun cI : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cO : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cH : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (E -> positive) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 43 ⊕ 2 ⊕ cost (pot cp ce) ⊕
         match val cp (val ce) with
         | xI q => pot cI (ECons (val ce) q ⋊ (pot ce, tt))
         | xO q => pot cO (ECons (val ce) q ⋊ (pot ce, tt))
         | xH => pot cH ce
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case3_body (h1_pair_at 4) (h1_pair_at 3) (h0 2)) []).
    unfold case3_body, h1_pair_at, h0. Mcase3_start.
    Mcall Ha2 Ha3 (j3 - 43 - 2). unfold positive_case.
    set (b := j3 - 43 - 2 - cost (c2 (a3 ⋊ c3))).
    set (env := [clos wu3 wE3; clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE]).
    destruct (a2 a3) as [q | q |]; cbn in R; subst r; cbn [cost res pot val] in *.
    - assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt) (clos pair_body (pos_enc q :: env))).
      { exists (clos wu3 wE3), (pos_enc q), (List.tl env). split; [reflexivity |].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha He b. subst env. Mstep. Mend R.
    - assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt) (clos pair_body (pos_enc q :: env))).
      { exists (clos wu3 wE3), (pos_enc q), (List.tl env). split; [reflexivity |].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha0 He b. subst env. Mstep. Mend R.
    - Mcall Ha1 Ha3 b. subst env. Mstep. Mend R.
  Qed.

  Lemma N_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@N_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (E -> N) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 43 ⊕ 2 ⊕ cost (pot cn ce) ⊕
         match val cn (val ce) with
         | N0 => pot cz ce
         | Npos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h0 3) (h1_pair_at 2)) []). unfold case2_body, h0, h1_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 43 - 2). unfold N_case.
    set (b := j2 - 43 - 2 - cost (c1 (a2 ⋊ c2))).
    set (env := [clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE]).
    destruct (a1 a2) as [| q]; cbn in R; subst r; cbn [cost res pot val] in *.
    - Mcall Ha Ha2 b. subst env. Mstep. Mend R.
    - assert (He : rl (env_repr RE Repr_positive) b (ECons a2 q) (c2, tt) (clos pair_body (pos_enc q :: env))).
      { exists (clos wu2 wE2), (pos_enc q), (List.tl env). split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha0 He b. subst env. Mstep. Mend R.
  Qed.

  Lemma Z_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Z_case E A)
      (fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cp : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cn : ℂI (env E positive -> A) (ℂI (env E positive) (CE * unit) -> ℂO CA) => 1 +>
       fun cx : ℂI (E -> Z) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 43 ⊕ 2 ⊕ cost (pot cx ce) ⊕
         match val cx (val ce) with
         | Z0 => pot cz ce
         | Zpos p => pot cp (ECons (val ce) p ⋊ (pot ce, tt))
         | Zneg p => pot cn (ECons (val ce) p ⋊ (pot ce, tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case3_body (h0 4) (h1_pair_at 3) (h1_pair_at 2)) []).
    unfold case3_body, h1_pair_at, h0. Mcase3_start.
    Mcall Ha2 Ha3 (j3 - 43 - 2). unfold Z_case.
    set (b := j3 - 43 - 2 - cost (c2 (a3 ⋊ c3))).
    set (env := [clos wu3 wE3; clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE]).
    destruct (a2 a3) as [| q | q]; cbn in R; subst r; cbn [cost res pot val] in *.
    - Mcall Ha Ha3 b. subst env. Mstep. Mend R.
    - assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt) (clos pair_body (pos_enc q :: env))).
      { exists (clos wu3 wE3), (pos_enc q), (List.tl env). split; [reflexivity |].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha0 He b. subst env. Mstep. Mend R.
    - assert (He : rl (env_repr RE Repr_positive) b (ECons a3 q) (c3, tt) (clos pair_body (pos_enc q :: env))).
      { exists (clos wu3 wE3), (pos_enc q), (List.tl env). split; [reflexivity |].
        split; [exact (rl_down_ b Ha3 ltac:(unfold b; lia)) | reflexivity]. }
      Mcall Ha1 He b. subst env. Mstep. Mend R.
  Qed.

  Lemma comparison_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@comparison_case E A)
      (fun cq : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cl : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cg : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun cc : ℂI (E -> comparison) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 43 ⊕ 2 ⊕ cost (pot cc ce) ⊕
         match val cc (val ce) with
         | Eq => pot cq ce
         | Lt => pot cl ce
         | Gt => pot cg ce
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case3_body (h0 4) (h0 3) (h0 2)) []). unfold case3_body, h0. Mcase3_start.
    Mcall Ha2 Ha3 (j3 - 43 - 2). unfold comparison_case.
    set (b := j3 - 43 - 2 - cost (c2 (a3 ⋊ c3))).
    destruct (a2 a3); cbn in R; subst r; cbn [cost res pot val] in *.
    - Mcall Ha Ha3 b. Mstep. Mend R.
    - Mcall Ha0 Ha3 b. Mstep. Mend R.
    - Mcall Ha1 Ha3 b. Mstep. Mend R.
  Qed.

  Lemma Q_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@Q_case E A)
      (fun cf : ℂI (env (env E Z) positive -> A)
                   (ℂI (env (env E Z) positive) ((CE * unit) * unit) -> ℂO CA) => 1 +>
       fun cq : ℂI (E -> Q) (ℂI E CE -> ℂO unit) => 1 +>
       fun ce : ℂI E CE => 43 ⊕ 2 ⊕ cost (pot cq ce) ⊕
         match val cq (val ce) with
         | Qmake n d => pot cf (ECons (ECons (val ce) n) d ⋊ ((pot ce, tt), tt))
         end).
  Proof.
    intros E CE A CA RE RA. apply has_complexity_bound.
    exists (clos (case1_body (h2_pair_at 2)) []). unfold case1_body, h2_pair_at. Mcase1_start.
    Mcall Ha0 Ha1 (j1 - 43 - 2). unfold Q_case.
    set (b := j1 - 43 - 2 - cost (c0 (a1 ⋊ c1))).
    destruct (a0 a1) as [zn pd]; cbn in R; subst r; cbn [cost res pot val Qnum Qden] in *.
    set (rest := [clos wu0 wE0; clos wu wE]).
    set (p1 := clos pair_body (Z_enc zn :: clos wu1 wE1 :: rest)).
    assert (He : rl (env_repr (env_repr RE Repr_Z) Repr_positive) b (ECons (ECons a1 zn) pd) ((c1, tt), tt)
                   (clos pair_body (pos_enc pd :: p1 :: Z_enc zn :: clos wu1 wE1 :: rest))).
    { exists p1, (pos_enc pd), (Z_enc zn :: clos wu1 wE1 :: rest). split; [reflexivity |].
      split; [| reflexivity].
      exists (clos wu1 wE1), (Z_enc zn), rest. split; [reflexivity |].
      split; [exact (rl_down_ b Ha1 ltac:(unfold b; lia)) | reflexivity]. }
    Mcall Ha He b. subst p1 rest. Mstep. Mend R.
  Qed.
End MZM.

(** ** Lists and options of any data

    The same encodings and realisers as for ground data; the realisers of
    the elements carry their complexities, and a value and its complexity
    have the same shape ([LInstance]). *)

Fixpoint hlist_rl {A CA} (P : A -> CA -> value -> Prop) (l : list A) (c : list CA) (v : value) : Prop :=
  match l, c with
  | nil, nil => v = clos (lam (var 1)) []
  | cons x l, cons cx c => exists r t, v = clos list_cons_body [t; r] /\ P x cx r /\ hlist_rl P l c t
  | _, _ => False
  end.

Definition hlist_repr {A CA} (RA : MRepr A CA) : MRepr (list A) (list CA).
Proof.
  refine {| rl := fun k l c v => hlist_rl (rl RA k) l c v; bo := Forall2 (bo RA) |}.
  - intros k k' l c v Hk; revert c v; induction l as [| x l IH]; intros [| cx c] v; cbn;
      try contradiction; [auto |].
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_down Hk Hr) | apply IH, Ht]].
  - intros k l c c' v Hb; revert l v; induction Hb as [| cx cx' c c' Hx Hc IH];
      intros [| x l] v; cbn; try contradiction; [auto |].
    intros (r & t & -> & Hr & Ht). exists r, t.
    split; [reflexivity | split; [exact (rl_mono Hx Hr) | apply IH, Ht]].
  - intros c. induction c; constructor; [apply bo_refl | assumption].
  - intros c1 c2 c3 H12; revert c3; induction H12 as [| x y l1 l2 Hxy H IH]; intros c3 H23;
      inversion H23; subst; constructor; [eapply bo_trans; eassumption | apply IH; assumption].
Defined.

Definition hoption_rl {A CA} (P : A -> CA -> value -> Prop) (o : option A) (c : option CA)
  (v : value) : Prop :=
  match o, c with
  | Some x, Some cx => exists r, v = clos (lam (app (var 1) (var 2))) [r] /\ P x cx r
  | None, None => v = clos (lam (var 0)) []
  | _, _ => False
  end.

Definition hoption_repr {A CA} (RA : MRepr A CA) : MRepr (option A) (option CA).
Proof.
  refine {| rl := fun k o c v => hoption_rl (rl RA k) o c v; bo := option_le (bo RA) |}.
  - intros k k' o c v Hk H; destruct o as [x |], c as [cx |]; cbn in *; try contradiction; [| exact H].
    destruct H as (r & -> & Hr). exists r. split; [reflexivity | exact (rl_down Hk Hr)].
  - intros k o c c' v Hb H; destruct o as [x |], c as [cx |], c' as [cx' |]; cbn in *;
      try contradiction; [| exact H].
    destruct H as (r & -> & Hr). exists r. split; [reflexivity | exact (rl_mono Hb Hr)].
  - intros [cx |]; cbn; [apply bo_refl | trivial].
  - intros [c1 |] [c2 |] [c3 |] H12 H23; cbn in *; try contradiction;
      [eapply bo_trans; eassumption | trivial].
Defined.

Module MHLM <: HListTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_cons := 1.
  Definition c_case_list := 46.
  Global Instance Repr_list {A CA} (RA : Repr A CA) : Repr (list A) (list CA) := hlist_repr RA.
  Global Instance Size_list {A} (SA : Size A) : Size (list A) :=
    fix size_list l := match l with nil => 4 | a :: l => 5 + SA a + size_list l end.
  Lemma size_nil : forall {A} `{Size A}, 0 < CostModelCore.size (@nil A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_cons : forall {A} `{Size A} (a : A) l,
    CostModelCore.size a + CostModelCore.size l < CostModelCore.size (a :: l).
  Proof. intros. unfold CostModelCore.size at 3. cbn. unfold CostModelCore.size. lia. Qed.

  Lemma bound_order_list : forall {A CA} `{Repr A CA} (c c' : list CA),
    Forall2 bound_order c c' -> bound_order c c'.
  Proof. intros A CA RA c c' H. exact H. Qed.

  Lemma nil_complexity : forall {A CA} `{Repr A CA}, ComplexityBound (@nil A) (@nil CA).
  Proof. intros A CA RA. apply has_complexity_bound. exists (clos (lam (var 1)) []). intro k. reflexivity. Qed.

  Lemma cons_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@cons A) (fun ch => 1 +> fun ct => 1 +> (pot ch :: pot ct)).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (clos (lam (lam list_cons_body)) []). intro k.
    Mfun. Mstep. Mfun. Mstep. cbn [rl Repr_list hlist_repr hlist_rl].
    exists (clos wu wE), (clos wu0 wE0). split; [reflexivity | split].
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
       fun ce : ℂI E CE => 46 ⊕ 2 ⊕ cost (pot cl ce) ⊕
         match val cl (val ce), res (pot cl ce) with
         | cons h t, cons ch ct => pot cc (ECons (ECons (val ce) h) t ⋊ ((pot ce, ch), ct))
         | _, _ => pot cz ce
         end).
  Proof.
    intros X CX E CE A CA RX RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h0 3) h2_pair) []). unfold case2_body, h0, h2_pair, h2_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 46 - 2). unfold list_case.
    set (b := j2 - 46 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [| x l]; destruct (res (c1 (a2 ⋊ c2))) as [| cx cl];
      cbn in R; cbn [cost res pot val] in *; try contradiction.
    - subst r. Mcall Ha Ha2 b. Mstep. Mend R.
    - destruct R as (r1 & t & -> & Hr & Ht).
      set (rest := [clos wu1 wE1; clos wu0 wE0; clos wu wE]).
      set (p1 := clos pair_body (r1 :: clos wu2 wE2 :: rest)).
      assert (He : rl (env_repr (env_repr RE RX) (Repr_list RX)) b (ECons (ECons a2 x) l) ((c2, cx), cl)
                     (clos pair_body (t :: p1 :: r1 :: clos wu2 wE2 :: rest))).
      { exists p1, t, (r1 :: clos wu2 wE2 :: rest). split; [reflexivity |].
        split; [| exact Ht].
        exists (clos wu2 wE2), r1, rest. split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Mcall Ha0 He b. subst p1 rest. Mstep. Mend R.
  Qed.
End MHLM.

Module MHOM <: HOptionTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_Some := 1.
  Definition c_case_option := 35.
  Global Instance Repr_option {A CA} (RA : Repr A CA) : Repr (option A) (option CA) := hoption_repr RA.
  Global Instance Size_option {A} (SA : Size A) : Size (option A) :=
    fun o => match o with None => 3 | Some a => 5 + SA a end.
  Lemma size_None : forall {A} `{Size A}, 0 < CostModelCore.size (@None A).
  Proof. intros. cbv. lia. Qed.
  Lemma size_Some : forall {A} `{Size A} (a : A), CostModelCore.size a < CostModelCore.size (Some a).
  Proof. intros. cbv. lia. Qed.

  Lemma bound_order_option : forall {A CA} `{Repr A CA} (c c' : option CA),
    option_le bound_order c c' -> bound_order c c'.
  Proof. intros A CA RA c c' H. exact H. Qed.

  Lemma None_complexity : forall {A CA} `{Repr A CA}, ComplexityBound (@None A) (@None CA).
  Proof. intros A CA RA. apply has_complexity_bound. exists (clos (lam (var 0)) []). intro k. reflexivity. Qed.

  Lemma Some_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Some A) (fun ca => 1 +> Some (pot ca)).
  Proof.
    intros A CA RA. apply has_complexity_bound. exists (clos (lam (lam (app (var 1) (var 2)))) []).
    intro k. Mfun. Mstep. cbn [rl Repr_option hoption_repr hoption_rl].
    exists (clos wu wE). split; [reflexivity | eapply rl_down; [| exact Ha]; lia].
  Qed.

  Lemma option_case_complexity :
    forall {X CX E CE A CA} `{Repr X CX} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@option_case X E A)
      (fun cs : ℂI (env E X -> A) (ℂI (env E X) (CE * CX) -> ℂO CA) => 1 +>
       fun cz : ℂI (E -> A) (ℂI E CE -> ℂO CA) => 1 +>
       fun co : ℂI (E -> option X) (ℂI E CE -> ℂO (option CX)) => 1 +>
       fun ce : ℂI E CE => 35 ⊕ 2 ⊕ cost (pot co ce) ⊕
         match val co (val ce), res (pot co ce) with
         | Some x, Some cx => pot cs (ECons (val ce) x ⋊ (pot ce, cx))
         | _, _ => pot cz ce
         end).
  Proof.
    intros X CX E CE A CA RX RE RA. apply has_complexity_bound.
    exists (clos (case2_body (h1_pair_at 3) (h0 2)) []). unfold case2_body, h0, h1_pair_at. Mcase_start.
    Mcall Ha1 Ha2 (j2 - 35 - 2). unfold option_case.
    set (b := j2 - 35 - 2 - cost (c1 (a2 ⋊ c2))).
    destruct (a1 a2) as [x |]; destruct (res (c1 (a2 ⋊ c2))) as [cx |];
      cbn in R; cbn [cost res pot val] in *; try contradiction.
    - destruct R as (rx & -> & Hr).
      assert (He : rl (env_repr RE RX) b (ECons a2 x) (c2, cx)
                     (clos pair_body [rx; clos wu2 wE2; clos wu1 wE1; clos wu0 wE0; clos wu wE])).
      { exists (clos wu2 wE2), rx, [clos wu1 wE1; clos wu0 wE0; clos wu wE]. split; [reflexivity |].
        split; [exact (rl_down_ b Ha2 ltac:(unfold b; lia)) | exact Hr]. }
      Mcall Ha He b. Mstep. Mend R.
    - subst r. Mcall Ha0 Ha2 b. Mstep. Mend R.
  Qed.
End MHOM.

(** ** Fixpoints

    L has no recursion primitive: the realiser of a recursive function ties
    the knot by self-application, as [rho] in [LInstance]. Applied to an
    environment [e], it returns a closure ([BODY1], one step); applied to an
    argument, the closure rebuilds itself by self-application ([WB]), builds
    the pair of [e] and of itself ([MK], in the shape of [pair_body]), and
    calls the realiser of the functional on the pair, then on the argument
    ([XB]). The recursive function in the pair is the closure [ETAB], which
    does the same. An unfolding costs at most [c_fix = 36] steps. *)
Definition MK : term := lam (lam (lam pair_body)).
Definition ETAB : term := app (app (var 2) (var 2)) (var 0).
(** In the context [x; w; y0; e; sF]: [sF (MK e (λ z. w w z)) x]. *)
Definition XB : term := app (app (var 4) (app (app MK (var 3)) (lam ETAB))) (var 0).
Definition WB : term := lam XB.
Definition BODY1 : term := app (app (lam WB) (lam WB)) (var 0).

(** The unfolding equation of [fix_complexity] is pointwise. *)
Lemma pw_eq_eq {T} (ar : Arity T) : forall x y, pw_eq ar x y -> x = y.
Proof.
  induction ar as [T | A B ar IH]; cbn; [auto |].
  intros f g H. apply functional_extensionality. intro a. apply IH, H.
Qed.

Module MFX <: FixTimeCostModel MCM MBT MCB.
  Import MCM MBT MCB.
  Definition c_fix := 36.

  Lemma fix_complexity : forall {E CE A B CA CB} `{Repr E CE} `{Repr A CA} `{Repr B CB}
      (ar : Arity B) (f : E -> A -> B)
      (F : env E (A -> B) -> A -> B)
      (cF : ℂI (env E (A -> B)) (CE * (ℂI A CA -> ℂO CB)) -> ℂO (ℂI A CA -> ℂO CB))
      (cf : ℂI E CE -> ℂO (ℂI A CA -> ℂO CB)),
      1 <= c_fix ->
      (forall e, is_fixpoint ar (fun g => F (ECons e g)) (f e)) ->
      ComplexityBound F cF ->
      bound_order
        (fun ce : ℂI E CE => 1 +> fun ca : ℂI A CA =>
           36 ⊕ pot <$> (F ⋊ cF) · (ECons (val ce) (f (val ce)) ⋊ (pot ce, res (cf ce))) · ca)
        cf ->
      ComplexityBound f cf.
  Proof.
    intros E CE A B CA CB RE RA RB ar f F cF cf _ Hfix [sF HF]%complexity_bound_has Hrec.
    apply has_complexity_bound.
    assert (Heq : forall e a, f e a = F (ECons e (f e)) a)
      by (intros e a; apply (pw_eq_eq ar), (Hfix e)).
    destruct sF as [uF EF].
    exists (clos (lam BODY1) [clos uF EF]). intro k. Mfun.
    destruct (Hrec (a ⋊ c)) as [Hcost0 Hcomp0].
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hcost0, Hcomp0.
    set (cfe := res (cf (a ⋊ c))) in *.
    set (e := clos wu wE) in *. set (sF := clos uF EF) in *.
    (* the closures of the recursive function of [e], at every budget up to [j] *)
    assert (Hknot : forall k', k' <= j -> forall x0 y0,
               rl (Repr_arr RA RB) k' (f a) cfe (clos ETAB [x0; clos WB [y0; e; sF]; y0; e; sF])).
    { intro k'. induction k' as [k' IH] using (well_founded_induction lt_wf).
      intros Hk' x0 y0. Mfun.
      destruct (Hcomp0 (a0 ⋊ c0)) as [Hcost Hcomp].
      cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hcost, Hcomp.
      set (x := clos wu0 wE0) in *. set (w := clos WB [y0; e; sF]).
      set (eta := clos ETAB [x; w; y0; e; sF]).
      assert (He : rl (env_repr RE (Repr_arr RA RB)) (j0 - 36) (ECons a (f a)) (c, cfe)
                     (clos pair_body [eta; e; x; w; y0; e; sF])).
      { exists e, eta, [x; w; y0; e; sF]. split; [reflexivity |].
        split; [exact (rl_down_ (j0 - 36) Ha ltac:(lia)) | apply IH; lia]. }
      Mcall (HF j0) He (j0 - 36). destruct r as [ur Er].
      Mcall R Ha0 (j0 - 36 - cost (cF (ECons a (f a) ⋊ (c, cfe)))).
      do 2 eexists; split.
      { cbn [call]. unfold ETAB, WB, XB, MK. subst eta w x e sF. Mev. }
      split; [cbn; lia |].
      rewrite Heq. eapply rl_mono; [exact Hcomp |]. Mend R0. }
    (* applied to [e], the realiser returns the closure [BODY1] *)
    do 2 eexists; split; [cbn [call]; apply ev_lam | split; [lia |]].
    Mfun.
    destruct (Hcomp0 (a0 ⋊ c0)) as [Hcost Hcomp].
    cbn [cost res pot val cost_add CostModelCore.app fmap ret_I ret bind] in Hcost, Hcomp.
    set (x := clos wu0 wE0) in *. set (w := clos WB [x; e; sF]).
    set (eta := clos ETAB [x; w; x; e; sF]).
    assert (He : rl (env_repr RE (Repr_arr RA RB)) (j0 - 36) (ECons a (f a)) (c, cfe)
                   (clos pair_body [eta; e; x; w; x; e; sF])).
    { exists e, eta, [x; w; x; e; sF]. split; [reflexivity |].
      split; [exact (rl_down_ (j0 - 36) Ha ltac:(lia)) | apply Hknot; lia]. }
    Mcall (HF j0) He (j0 - 36). destruct r as [ur Er].
    Mcall R Ha0 (j0 - 36 - cost (cF (ECons a (f a) ⋊ (c, cfe)))).
    do 2 eexists; split.
    { cbn [call]. unfold BODY1, ETAB, WB, XB, MK. subst eta w x e sF. Mev. }
    split; [cbn; lia |].
    rewrite Heq. eapply rl_mono; [exact Hcomp |]. Mend R0.
  Qed.

  Include FixRules MCM MBT MCB.
End MFX.

(** ** The instance *)
Module LM <: MachineTimeCostModel.
  Include MCM. Include MBT. Include MCB. Include MBO. Include MNT. Include MLM. Include MOM.
  Include MPM. Include MZM. Include MFX.
End LM.

(** With lists and options of any data. *)
Module LMH <: MachineHOTimeCostModel.
  Include MCM. Include MBT. Include MCB. Include MBO. Include MNT. Include MHLM. Include MHOM.
  Include MPM. Include MZM. Include MFX.
End LMH.
