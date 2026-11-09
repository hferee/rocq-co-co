(** * A feasible type-3 functional that is not basic feasible

    Irwin, Kapron and Royer's example: the type-3 functionals

    - [V F x = 1] if [F (C x) <> F zero], [0] otherwise,
    - [W F x = 2^x] if [F (C x) <> F zero], [0] otherwise,

    where [C x] is the characteristic function of [2^x] and [zero] the
    constant function [0], for [F : (N -> N) -> N]. [V] is basic feasible.
    [W] is not: when [F] is 0-1 valued, the length of the values of a BFF is
    bounded by a polynomial in [|x|], but [|W F x| = x + 1] when [F]
    distinguishes [C x] from [zero]. Yet [W] is not harder than [V]: if
    [F (C x) <> F zero], then [F] has queried its argument at [2^x], the
    only point where [C x] and [zero] differ, so that a machine running [F]
    has written down [2^x], and [W] can write it once more.

    References:
    J. S. Royer. A feasible type-3 functional that fails to be basic
    feasible. DIMACS workshop on computational complexity and programming
    languages, 1996.

    R. J. Irwin, J. S. Royer, B. M. Kapron. On characterizations of the basic
    feasible functionals, Part I. Journal of Functional Programming
    11(1):117-153, 2001.

    The functionals are defined below over binary numbers ([N]), with the
    test [y = 2^x] in polynomial time ([pow2_eq_pos]), and their costs are
    analysed in [Type3Complexity]: the cost of [W] is the cost of [V] plus,
    when [F] distinguishes [C x] from [zero], the cost of writing [2^x],
    linear in [x], that is exponential in [|x|] ([W_cost]). The argument
    above bounds it by the cost of [F] only under an assumption that the
    cost model does not provide: that [F] pays for the size of its queries
    ([W_cost_paid]).

    [V] is a BFF: it is equal, as a functional, to a PV^ω term ([V_BFF]).
    [W] is not: no BFF is equal to it ([W_not_BFF]), since every BFF has a
    polynomial majorant.
    In terms of higher-order polynomial bounds in the cost model
    ([BFFFeasibility]): [V] has one ([V_hpoly]), [W] has none, whatever its
    complexity ([W_not_hpoly]). *)

From Complexity Require Import PosComplexity BFFFeasibility.
From Stdlib Require Import PArith NArith NArithRing.
From Stdlib Require List.
Import List.ListNotations.

(** ** Definitions *)

(** [zeros p q]: [q] followed by [p] zeros, that is [q 2^p], in time linear
    in [p]. *)
Fixpoint zeros (p q : positive) : positive :=
  match p with
  | xH => xO q
  | xO p' => zeros p' (zeros p' q)
  | xI p' => xO (zeros p' (zeros p' q))
  end.

(** [pow2 x = 2^x]. *)
Definition pow2 (x : N) : N := match x with N0 => 1 | Npos p => Npos (zeros p xH) end.

(** [pow2_eq_pos x p]: [p = 2^x], removing the last zero of [p] and
    decrementing [x] at each step. *)
Fixpoint pow2_eq_pos (x : N) (p : positive) : bool :=
  match p with
  | xH => match x with N0 => true | Npos _ => false end
  | xO q => match x with N0 => false | Npos _ => pow2_eq_pos (N.pred x) q end
  | xI _ => false
  end.

(** [C x]: the characteristic function of [2^x]. *)
Definition C (x y : N) : N :=
  match y with N0 => 0 | Npos p => if pow2_eq_pos x p then 1 else 0 end.

Definition zero (_ : N) : N := 0.

Definition V (F : (N -> N) -> N) (x : N) : N := if N.eqb (F (C x)) (F zero) then 0 else 1.

Definition W (F : (N -> N) -> N) (x : N) : N := if N.eqb (F (C x)) (F zero) then 0 else pow2 x.

(** ** Specifications *)

Lemma double_add (n : N) : (2 * n = n + n)%N.
Proof. lia. Qed.

Lemma zeros_spec p q : Npos (zeros p q) = (Npos q * 2 ^ Npos p)%N.
Proof.
  revert q; induction p as [p IH|p IH|]; intro q; cbn [zeros].
  - change (Npos (zeros p (zeros p q))~0) with (2 * Npos (zeros p (zeros p q)))%N.
    change (Npos p~1) with (2 * Npos p + 1)%N.
    rewrite IH, IH, (double_add (Npos p)), !N.pow_add_r, N.pow_1_r. ring.
  - change (Npos p~0) with (2 * Npos p)%N. rewrite IH, IH, (double_add (Npos p)), N.pow_add_r. ring.
  - change (Npos q~0) with (2 * Npos q)%N. rewrite N.pow_1_r. ring.
Qed.

Lemma pow2_spec x : pow2 x = (2 ^ x)%N.
Proof. destruct x as [|p]; [reflexivity|]. cbn [pow2]. rewrite zeros_spec. ring. Qed.

Lemma pow2_eq_pos_spec x p : pow2_eq_pos x p = true <-> Npos p = (2 ^ x)%N.
Proof.
  revert x; induction p as [p IH|p IH|]; intro x; cbn [pow2_eq_pos].
  - split; [discriminate|]. intro H. destruct x as [|q]; [discriminate|].
    assert (E : N.even (Npos p~1) = N.even (2 ^ Npos q)) by (rewrite H; reflexivity).
    rewrite N.even_pow in E by lia. discriminate.
  - destruct x as [|q]; [split; discriminate|]. rewrite IH.
    rewrite <- (N.succ_pred (Npos q)) at 2 by discriminate. rewrite N.pow_succ_r'.
    change (Npos p~0) with (2 * Npos p)%N. lia.
  - destruct x as [|q]; [split; reflexivity|]. split; [discriminate|].
    intro H. pose proof (N.pow_gt_1 2 (Npos q)) as Hq. lia.
Qed.

Lemma C_spec x y : C x y = if (y =? 2 ^ x)%N then 1%N else 0%N.
Proof.
  destruct y as [|p]; cbn [C].
  - pose proof (N.pow_nonzero 2 x). destruct (N.eqb_spec 0 (2 ^ x)); lia.
  - destruct (pow2_eq_pos x p) eqn:E, (N.eqb_spec (Npos p) (2 ^ x));
      try reflexivity; apply pow2_eq_pos_spec in E || rewrite <- pow2_eq_pos_spec in *; congruence.
Qed.

(** [C x] and [zero] differ only at [2^x]. *)
Lemma C_zero x y : y <> (2 ^ x)%N -> C x y = zero y.
Proof. intro H. rewrite C_spec. destruct (N.eqb_spec y (2 ^ x)); [contradiction | reflexivity]. Qed.

Lemma W_spec F x : W F x = if (F (C x) =? F zero)%N then 0%N else (2 ^ x)%N.
Proof. unfold W. rewrite pow2_spec. reflexivity. Qed.

(** ** [V] is a basic feasible functional

    [V'] is [V] written in PV^ω ([BFF]): [pw2 x] is the characteristic
    function of [2^x] and [eqN] the equality test, defined with the
    recursion on notation [R]. It is the denotation of the term [V'_pv]
    of PV^ω, and it is equal to [V] as a functional ([V'_V]): on equal
    arguments, [V'] and [V] have equal values. *)
Definition V'_t : PTerm pv ((tN ⇒ tN ⇒ tN) ⇒ (tN ⇒ tN ⇒ tN) ⇒ ((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) :=
  <{ λ eqN pw2 F x, cond (eqN (F (pw2 x)) (F (λ _, 0))) 1 0 }>.
Definition V' (F : (N -> N) -> N) (x : N) : N := Eval cbn in pden V'_t eqN pw2 F x.
Definition V'_pv : term pv [] _ := tapp (tapp (db V'_t) eqN_pv) pw2_pv.

Lemma V'_V : ext_eq (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) V' V.
Proof.
  intros F G HFG x y Hxy. cbn in HFG, Hxy |- *. subst y. unfold V', V.
  assert (H1 : F (pw2 x) = G (C x)).
  { apply HFG. intros a b <-. rewrite pw2_spec, C_spec. reflexivity. }
  assert (H2 : F (fun _ => 0%N) = G zero) by (apply HFG; intros a b <-; reflexivity).
  rewrite H1, H2, eqN_spec. destruct (G (C x) =? G zero)%N; reflexivity.
Qed.

Theorem V_BFF : is_BFF (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) V.
Proof. exact (bff_ext (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) V' V (BFF_eval _ V'_pv) V'_V). Qed.


Lemma size_nat_zeros p q : Pos.size_nat (zeros p q) = Pos.to_nat p + Pos.size_nat q.
Proof.
  revert q; induction p as [p IH|p IH|]; intro q; cbn [zeros Pos.size_nat];
    rewrite ?IH, ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO; cbn; lia.
Qed.

(** The length of [W F x] is [x + 1] when [F] distinguishes [C x] from
    [zero]: exponential in [|x|]. *)
Lemma size_nat_pow2 x : N.size_nat (pow2 x) = S (N.to_nat x).
Proof. destruct x as [|p]; [reflexivity|]. cbn [pow2 N.size_nat N.to_nat]. rewrite size_nat_zeros. cbn. lia. Qed.

Lemma size_nat_pred x : N.size_nat (N.pred x) <= N.size_nat x.
Proof.
  destruct x as [|[p|p|]]; cbn; try lia.
  pose proof (BitSize.size_nat_pred_double p). lia.
Qed.

Lemma pow_size_nat_le p : 2 ^ (Pos.size_nat p - 1) <= Pos.to_nat p.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size_nat]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO;
    try (pose proof (BitSize.size_nat_pos p); replace (S (Pos.size_nat p) - 1)
           with (S (Pos.size_nat p - 1)) by lia; rewrite Nat.pow_succ_r'); cbn; lia.
Qed.

(** ** [W] is not a basic feasible functional *)

(** The bound [n ↦ m (λ _, 1) (n + 1)] on the lengths of [W F x], for a
    majorant [m] of [W] and a 0-1 valued [F], with [|x| = n + 1]. *)
Definition W_bound (m : hpoly (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) : hpoly (tN ⇒ tN) :=
  tapp (db <{ λ g n, g (λ _, 1) (n + 1) }>
          : hpoly ((((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) ⇒ tN ⇒ tN)) m.

(** Every term of PV^ω has a polynomial majorant ([BFF_majorant]). Applied
    to the majorant [fun _ => 1] of a 0-1 valued [F], it gives a
    higher-order polynomial of type [N ⇒ N], bounded by a polynomial
    ([hpoly_growth]). But it would bound the length [x + 1] of [W F x] when
    [F] distinguishes [C x] from [zero], which is exponential in [|x|]
    ([pow2_not_poly]). *)
Corollary W_not_BFF : ~ is_BFF (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) W.
Proof.
  intros (t & HE). pose proof (BFF_majorant _ t) as Hv. set (m := csubst pv_maj t) in Hv.
  apply (pow2_not_poly (W_bound m)). intro n.
  change (2 ^ n <= ⟦m⟧ (fun _ => 1) (n + 1)). rewrite Nat.add_1_r.
  set (x0 := pow2 (N.of_nat n)).
  set (F := fun f : N -> N => if (f (pow2 x0) =? 0)%N then 0%N else 1%N).
  assert (HF : vmaj ((tN ⇒ tN) ⇒ tN) F (fun _ => 1%nat)).
  { intros g a _ _. unfold F. destruct (_ =? 0)%N; cbn; lia. }
  assert (Hx0 : N.size_nat x0 = S n).
  { unfold x0. rewrite size_nat_pow2, Nat2N.id. reflexivity. }
  assert (Hv0 : N.to_nat x0 = 2 ^ n).
  { unfold x0. rewrite pow2_spec, N2Nat.inj_pow, Nat2N.id. reflexivity. }
  pose proof (Hv F (fun _ => 1%nat) ltac:(intros ? ? ?; cbn; lia) HF x0 (S n)
                ltac:(cbn; lia) ltac:(cbn; lia)) as Hb.
  assert (HFF : ext_eq ((tN ⇒ tN) ⇒ tN) F F).
  { intros f g Hfg. cbn in *. unfold F. rewrite (Hfg (pow2 x0) (pow2 x0) eq_refl). reflexivity. }
  assert (HW : ⟦t⟧ F x0 = W F x0) by exact (HE F F HFF x0 x0 eq_refl).
  assert (HCx : F (C x0) = 1%N).
  { unfold F. rewrite C_spec, pow2_spec, N.eqb_refl. reflexivity. }
  cbn in Hb. rewrite HW in Hb. unfold W in Hb. rewrite HCx in Hb. cbn in Hb.
  rewrite size_nat_pow2, Hv0 in Hb. lia.
Qed.

(** ** Complexity *)

(** The potentials of [C x] and [zero], given to [F] by [V] and [W]: the
    costs of their applications. *)
Definition C_pot (x : N) (cy : ℂI N unit) : ℂO unit :=
  (N.size_nat (val cy) * (16 * N.size_nat x + 52) + 16) ⋉ tt.
Definition zero_pot (cy : ℂI N unit) : ℂO unit := 1 ⋉ tt.

(** The costs of [V F x] and [W F x], from the potential [pF] of [F]: [F]
    is applied to [C x] and to [zero], and its values are compared. [W]
    then writes [2^x] when they differ, in time linear in [x]. *)
Definition V_cost (F : (N -> N) -> N) (pF : ℂI (N -> N) (ℂI N unit -> ℂO unit) -> ℂO unit)
  (x : N) : nat :=
  cost (pF (C x ⋊ C_pot x)) + cost (pF (zero ⋊ zero_pot)) + 50 * N.size_nat (F (C x)) + 55.
Arguments V_cost F pF x /.

Definition W_cost (F : (N -> N) -> N) (pF : ℂI (N -> N) (ℂI N unit -> ℂO unit) -> ℂO unit)
  (x : N) : nat :=
  V_cost F pF x + if (F (C x) =? F zero)%N then 3 else 96 * N.to_nat x + 9.
Arguments W_cost F pF x /.

(** ** Feasibility of W.



    [W_complexity] below gives the cost of [W]: [W_cost] is [V_cost] plus,
    when [F] distinguishes [C x] from [zero], [96 x + 9] for writing
    [2^x], which is exponential in the length of [x]
    ([x >= 2^(|x| - 1)], [pow_size_nat_le]). It is a constant for each [F]
    (only finitely many [x] are such that [F] queries [2^x] on [zero]),
    but not uniformly in the potential of [F]: nothing in the cost model
    relates the values queried by [F] to its costs. Values are free
    constants of programs, and a call costs one step whatever the size of
    its argument (as a beta-step of L).

    Royer's argument does relate them, for oracle machines, which write
    their queries: if [F (C x) <> F zero], then [F] queried its argument
    at [2^x], and the call [F (C x)] paid at least [x] steps for writing
    it (a lower bound on the cost [pF (C x ⋊ C_pot x)]). Under this
    assumption, the cost of [W] is at most a constant times the cost of [V]
    ([W_cost_paid]), so that [W] is as feasible as [V], although it is not
    basic feasible. *)
Lemma W_cost_paid F pF x :
  ((F (C x) =? F zero)%N = false -> N.to_nat x <= cost (pF (C x ⋊ C_pot x))) ->
  W_cost F pF x <= 97 * V_cost F pF x.
Proof.
  intro Hq. cbn [W_cost V_cost].
  destruct (F (C x) =? F zero)%N; [lia | specialize (Hq eq_refl); lia].
Qed.

Module Type3Complexity (Import M : TimePos).

  Module BF := BFFFeasibility M.
  Import BF.

  (** [zeros p q] makes [2 p - 1] calls. *)
  Global Instance zeros_complexity : ComplexityBound zeros
    (fun cp => 5 ⋉ fun cq => (48 * (2 * Pos.to_nat (val cp) - 1)) ⋉ tt).
  Proof. cbound. all: pose proof (Pos2Nat.is_pos cp); lia. Qed.

  Global Instance pow2_complexity : ComplexityBound pow2
    (fun cx => (96 * N.to_nat (val cx) + 2) ⋉ tt) := _.

  Global Instance pred_N_complexity : ComplexityBound Pos.pred_N
    (fun cp => (16 * Pos.size_nat (val cp)) ⋉ tt) := _.

  Global Instance N_pred_complexity : ComplexityBound N.pred
    (fun cx => (16 * N.size_nat (val cx) + 2) ⋉ tt) := _.

  Global Instance N_eqb_complexity : ComplexityBound N.eqb
    (fun cx => 2 ⋉ fun cy => (50 * N.size_nat (val cx) + 33) ⋉ tt) := _.

  Global Instance pow2_eq_pos_complexity : ComplexityBound pow2_eq_pos
    (fun cx => 5 ⋉ fun cp => (Pos.size_nat (val cp) * (16 * N.size_nat (val cx) + 52)) ⋉ tt).
  Proof.
    cbound.
    all: match goal with |- context [Pos.pred_N ?p] => pose proof (size_nat_pred (Npos p)) as H end;
      cbn [N.pred N.size_nat] in H; nia.
  Qed.

  Global Instance C_complexity : ComplexityBound C
    (fun cx => 4 ⋉ C_pot (val cx)) := _.

  Global Instance zero_complexity : ComplexityBound zero zero_pot := _.

  Global Instance V_complexity : ComplexityBound V
    (fun cF => 2 ⋉ fun cx => V_cost (val cF) (pot cF) (val cx) ⋉ tt) := _.

  Global Instance W_complexity : ComplexityBound W
    (fun cF => 2 ⋉ fun cx => W_cost (val cF) (pot cF) (val cx) ⋉ tt).
  Proof. cbound. all: rewrite E; lia. Qed.

  (** ** Higher-order polynomial bounds ([BFFFeasibility]) *)

  Lemma size_C x y : N.size_nat (C x y) <= 1.
  Proof. rewrite C_spec. destruct (y =? 2 ^ x)%N; cbn; lia. Qed.

  (** [V'], the denotation of a term of PV^ω equal to [V], has a
      higher-order polynomial bound, as every term ([BFF_hpoly_bound]). *)
  Global Instance V'_hpoly : HPolyBound (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) V' :=
    BFF_hpoly_bound _ V'_pv.

  (** [V] has a higher-order polynomial bound: its costs are those of [F]
      on [C x] and on [zero], whose majorants are polynomials in [|x|]. *)
  Lemma V_hpoly : HPolyBound (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) V.
  Proof.
    refine (hpoly_intro _ _
      (db <{ λ mF a, 51 * mF (λ b, b * (16 * a + 52) + 16) + mF (λ _, 1) + 55 }>)
      _ V_complexity _).
    simpl_hp. intros F cF mF HmF HF. split; [cbn; lia|].
    intros x cx a _ Hx. cbn [maj baseM] in *.
    assert (HC : maj (tN ⇒ tN) (C x) (C_pot x) (fun b => b * (16 * a + 52) + 16)).
    { intros y cy b _ Hy. cbn in *. pose proof (size_C x y). split; nia. }
    assert (HCm : monotone (tN ⇒ tN) (fun b => b * (16 * a + 52) + 16)).
    { intros b b' Hb. cbn in *. nia. }
    assert (Hz : maj (tN ⇒ tN) zero zero_pot (fun _ => 1)).
    { intros y cy b _ _. cbn. lia. }
    assert (Hzm : monotone (tN ⇒ tN) (fun _ => 1)) by (intros ? ? ?; cbn; lia).
    destruct (HF _ _ _ HCm HC) as [HC1 HC2]. destruct (HF _ _ _ Hzm Hz) as [Hz1 _].
    cbn -[Nat.mul] in *. split; [lia|].
    unfold V. destruct (_ =? _)%N; cbn; lia.
  Qed.

  (** [W] has no higher-order polynomial bound, whatever its complexity: a
      majorant also bounds the lengths of the values ([maj] at [N]). The
      0-1 valued [F f = [f (2^x) <> 0]], with no cost, is majorized by
      [fun _ => 1], but the length [x + 1] of [W F x] is exponential in
      [|x|], whereas a higher-order polynomial of type [N ⇒ N] is bounded by
      a polynomial ([hpoly_growth], [pow2_not_poly]). *)
  Lemma W_not_hpoly : ~ HPolyBound (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) W.
  Proof.
    intros (c & m & _ & Hm).
    apply (pow2_not_poly (W_bound m)). intro n.
    change (2 ^ n <= ⟦m⟧ (fun _ => 1) (n + 1)). rewrite Nat.add_1_r.
    set (x0 := pow2 (N.of_nat n)).
    set (F := fun f : N -> N => if (f (pow2 x0) =? 0)%N then 0%N else 1%N).
    assert (HF : maj ((tN ⇒ tN) ⇒ tN) F (fun _ => 0 ⋉ tt) (fun _ => 1)).
    { intros g cg mg _ _. cbn. split; [lia|]. unfold F. destruct (_ =? 0)%N; cbn; lia. }
    assert (Hv : N.to_nat x0 = 2 ^ n).
    { unfold x0. rewrite pow2_spec, N2Nat.inj_pow, Nat2N.id. reflexivity. }
    assert (Hx0 : N.size_nat x0 = S n).
    { unfold x0. rewrite size_nat_pow2, Nat2N.id. reflexivity. }
    assert (HCx : F (C x0) = 1%N).
    { unfold F. rewrite C_spec, pow2_spec, N.eqb_refl. reflexivity. }
    destruct (Hm F _ (fun _ => 1) ltac:(intros ? ? ?; cbn; lia) HF) as [_ H].
    destruct (H x0 tt (S n) ltac:(cbn; lia) ltac:(cbn; lia)) as [_ Hs].
    cbn in Hs. unfold W in Hs. rewrite HCx in Hs. cbn in Hs. rewrite size_nat_pow2, Hv in Hs.
    lia.
  Qed.
End Type3Complexity.
