(** * A feasible type-3 functional that is not basic feasible

    Irwin, Kapron and Royer's example: the type-3 functionals

    - `V F x = 1` if `F (C x) <> F zero`, [0] otherwise,
    - `W F x = 2^x` if `F (C x) <> F zero`, [0] otherwise,

    where `C x` is the characteristic function of [2^x] and [zero] the
    constant function [0], for `F : (N -> N) -> N`. `V` is basic feasible.
    [W] is not: when `F` is 0-1 valued, the length of the values of a BFF is
    bounded by a polynomial in [|x|], but `|W F x| = x + 1` when `F`
    distinguishes `C x` from [zero]. Yet [W] is not harder than `V`: if
    `F (C x) <> F zero`, then `F` has queried its argument at [2^x], the
    only point where `C x` and [zero] differ, so that a machine running `F`
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
    analysed in [Type3Complexity]: the cost of [W] is the cost of `V` plus,
    when `F` distinguishes `C x` from [zero], the cost of writing [2^x],
    linear in [x], that is exponential in [|x|] ([W_cost]). The argument
    above bounds it by the cost of `F` only under an assumption that the
    cost model does not provide: that `F` pays for the size of its queries
    ([W_cost_paid]). The assumption holds when the potential of `F` is a
    size bound ([CSized], [sized_query]).

    `V` is a BFF: it is equal, as a functional, to a PV^ω term ([V_BFF]).
    [W] is not: no BFF is equal to it ([W_not_BFF]), since every BFF has a
    polynomial majorant.
    In terms of higher-order polynomial bounds in the cost model
    ([BFFFeasibility]): `V` has one ([V_hpoly]), [W] has none, whatever its
    complexity ([W_not_hpoly]). On sized arguments, both have one
    ([V_hpolyS], [W_hpolyS], [W_sized_contrast]). *)

From Complexity Require Import PosComplexity BFFFeasibility BitSize ListFacts.
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

(** `C x`: the characteristic function of [2^x]. *)
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

(** `C x` and [zero] differ only at [2^x]. *)
Lemma C_zero x y : y <> (2 ^ x)%N -> C x y = zero y.
Proof. intro H. rewrite C_spec. destruct (N.eqb_spec y (2 ^ x)); [contradiction | reflexivity]. Qed.

Lemma W_spec F x : W F x = if (F (C x) =? F zero)%N then 0%N else (2 ^ x)%N.
Proof. unfold W. rewrite pow2_spec. reflexivity. Qed.

(** ** `V` is a basic feasible functional

    [V'] is `V` written in PV^ω ([BFF]): [pw2 x] is the characteristic
    function of [2^x] and [eqN] the equality test, defined with the
    recursion on notation `R`. It is the denotation of the term [V'_pv]
    of PV^ω, and it is equal to `V` as a functional ([V'_V]): on equal
    arguments, [V'] and `V` have equal values. *)
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

(** The length of `W F x` is [x + 1] when `F` distinguishes `C x` from
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

(** The bound [n ↦ m (λ _, 1) (n + 1)] on the lengths of `W F x`, for a
    majorant [m] of [W] and a 0-1 valued `F`, with [|x| = n + 1]. *)
Definition W_bound (m : hpoly (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) : hpoly (tN ⇒ tN) :=
  tapp (db <{ λ g n, g (λ _, 1) (n + 1) }>
          : hpoly ((((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) ⇒ tN ⇒ tN)) m.

(** Every term of PV^ω has a polynomial majorant ([BFF_majorant]). Applied
    to the majorant [fun _ => 1] of a 0-1 valued `F`, it gives a
    higher-order polynomial of type [N ⇒ N], bounded by a polynomial
    ([hpoly_growth]). But it would bound the length [x + 1] of `W F x` when
    `F` distinguishes `C x` from [zero], which is exponential in [|x|]
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

(** The potentials of `C x` and [zero], given to `F` by `V` and [W]: the
    costs of their applications. *)
Definition C_pot (x : N) (cy : ℂI N unit) : ℂO unit :=
  (N.size_nat (val cy) * (16 * N.size_nat x + 52) + 16) ⋉ tt.
Definition zero_pot (cy : ℂI N unit) : ℂO unit := 1 ⋉ tt.

(** The costs of `V F x` and `W F x`, from the potential `pF` of `F`: `F`
    is applied to `C x` and to [zero], and its values are compared. [W]
    then writes [2^x] when they differ, in time linear in [x]. *)
Definition V_cost (F : (N -> N) -> N) (pF : ℂI (N -> N) (ℂI N unit -> ℂO unit) -> ℂO unit)
  (x : N) : nat :=
  cost (pF (C x ⋊ C_pot x)) + cost (pF (zero ⋊ zero_pot)) + 50 * N.size_nat (F (C x)) + 55.
Arguments V_cost F pF x /.

(* A running-time bound for W. Note that it is intentional : it depends on the values of F, not simply on its output size. *)
Definition W_cost (F : (N -> N) -> N) (pF : ℂI (N -> N) (ℂI N unit -> ℂO unit) -> ℂO unit)
  (x : N) : nat :=
  V_cost F pF x + if (F (C x) =? F zero)%N then 3 else 96 * N.to_nat x + 9.
Arguments W_cost F pF x /.

(** ** Feasibility of W.



    [W_complexity] below gives the cost of [W]: [W_cost] is [V_cost] plus,
    when `F` distinguishes `C x` from [zero], [96 x + 9] for writing
    [2^x], which is exponential in the length of [x]
    ([x >= 2^(|x| - 1)], [pow_size_nat_le]). It is a constant for each `F`
    (only finitely many [x] are such that `F` queries [2^x] on [zero]),
    but not uniformly in the potential of `F`: nothing in the cost model
    relates the values queried by `F` to its costs. Values are free
    constants of programs, and a call costs one step whatever the size of
    its argument (as a beta-step of L).

    Royer's argument does relate them, for oracle machines, which write
    their queries: if `F (C x) <> F zero`, then `F` queried its argument
    at [2^x], and the call `F (C x)` paid at least [x] steps for writing
    it (a lower bound on the cost `pF (C x ⋊ C_pot x)`). Under this
    assumption, the cost of [W] is at most a constant times the cost of `V`
    ([W_cost_paid]), so that [W] is as feasible as `V`, although it is not
    basic feasible. *)
Lemma W_cost_paid F pF x :
  ((F (C x) =? F zero)%N = false -> N.to_nat x <= cost (pF (C x ⋊ C_pot x))) ->
  W_cost F pF x <= 97 * V_cost F pF x.
Proof.
  intro Hq. cbn [W_cost V_cost].
  destruct (F (C x) =? F zero)%N; [lia | specialize (Hq eq_refl); lia].
Qed.

Module Type3Complexity (Import Time : TimePos).

  Module BF := BFFFeasibility Time.
  Import BF.

  (** ** Sized arguments ([HOBounds])

      The potentials of `C x` and [zero] are size bounds ([CSized]);
      [C_pot x] is also a size of [zero], which only differs from [C x] at
      [2^x]. *)
  Lemma C_sized x : CSized (bits (tN ⇒ tN)) (C x) (C_pot x).
  Proof.
    apply CSized_1. intros y.
    assert (N.size_nat (C x (val y)) <= 1) by (rewrite C_spec; destruct (_ =? _)%N; cbn; lia).
    unfold C_pot. cbn [cost]. nia.
  Qed.

  Lemma zero_sized x : CSized (bits (tN ⇒ tN)) zero (C_pot x).
  Proof. apply CSized_const. intros y. cbn. lia. Qed.

  Lemma zero_sized_pot : CSized (bits (tN ⇒ tN)) zero zero_pot.
  Proof. apply CSized_const. intros y. cbn. lia. Qed.

  (** If [F] is sized by [cF] and distinguishes [C x] from [zero],
      then it asks [C x] the question [2^x], whose weight is more than [x]:
      the cost of [cF] on [C x] is more than [x]. It is the hypothesis of
      [W_cost_paid], from the size of [F] alone. *)
  Theorem sized_query F cF x :
    CSized (bits ((tN ⇒ tN) ⇒ tN)) F cF ->
    F (C x) <> F zero ->
    N.to_nat x < cost (cF (C x ⋊ C_pot x)).
  Proof.
    intros HF Hd. destruct (CSized_2 _ _ _ _ _ _ F cF (C x) (C_pot x) HF (C_sized x)) as (ys & Hw & Hm).
    destruct (List.in_dec N.eq_dec (2 ^ x)%N ys) as [Hin | Hout].
    - (* [F] asks [2^x], which costs more than [x + 1] to [C x], whose
         answers are free but at most [1] *)
      match type of Hw with context [List.list_sum (List.map ?w ys)] =>
        assert (Hs : w (2 ^ x)%N <= List.list_sum (List.map w ys)) by exact (list_sum_In _ _ (List.in_map w _ _ Hin));
        assert (Hx : S (S (N.to_nat x)) <= w (2 ^ x)%N)
      end.
      { unfold C_pot. cbn [cost val]. rewrite size_nat_pow. nia. }
      match type of Hw with context [List.list_max ?l] => assert (Hr : List.list_max l <= 1) end.
      { apply List.list_max_le, List.Forall_forall. intros n Hn.
        apply List.in_map_iff in Hn as (y & <- & _). rewrite C_spec. destruct (_ =? _)%N; cbn; lia. }
      norm_types. lia.
    - (* otherwise [zero] answers like [C x] to all the questions *)
      exfalso. apply Hd. symmetry. apply (Hm zero (zero_sized x)).
      intros y Hy. symmetry. apply C_zero. intros ->. exact (Hout Hy).
  Qed.

  (** If `F` has a size bound [sF], [W] costs at most `V` plus [96] times
      the size of `F` on `C x` ([sized_query]), and its value is not
      longer than this size. *)
  Lemma W_cost_sized F cF sF x :
    CSized (bits ((tN ⇒ tN) ⇒ tN)) F sF ->
    W_cost F cF x <= V_cost F cF x + 96 * cost (sF (C x ⋊ C_pot x)) + 9.
  Proof.
    intros HF. cbn [W_cost]. destruct (F (C x) =? F zero)%N eqn:E; [lia|].
    pose proof (sized_query F sF x HF (proj1 (N.eqb_neq _ _) E)). lia.
  Qed.

  Lemma W_size_sized F cF x :
    CSized (bits ((tN ⇒ tN) ⇒ tN)) F cF -> N.size_nat (W F x) <= cost (cF (C x ⋊ C_pot x)).
  Proof.
    intros HF. rewrite W_spec. destruct (N.eqb_spec (F (C x)) (F zero)) as [|Hd]; [cbn; lia|].
    rewrite size_nat_pow. pose proof (sized_query F cF x HF Hd). lia.
  Qed.

  (** The argument of [W_not_hpoly], which asks [2^x] at the cost [|x|], is
      not sized by its potential. *)
  Lemma free_query_unsized x :
    ~ CSized (bits ((tN ⇒ tN) ⇒ tN)) (fun f => if (f (2 ^ x) =? 0)%N then 0%N else 1%N)
        (fun _ => N.size_nat x ⋉ tt).
  Proof.
    intros H.
    assert (Hq : N.to_nat x < N.size_nat x).
    { apply (sized_query _ _ x H). rewrite !C_spec, N.eqb_refl. cbn. unfold zero. discriminate. }
    destruct x as [|p]; [cbn in Hq; lia|].
    pose proof (size_nat_le_to_nat p). cbn [N.size_nat N.to_nat] in Hq. lia.
  Qed.


  (** [zeros p q] makes [2 p - 1] calls. *)
  Global Instance zeros_complexity : Time.ComplexityBound zeros
    (fun cp => 5 ⋉ fun cq => (48 * (2 * Pos.to_nat (val cp) - 1)) ⋉ tt).
  Proof. cbound. all: pose proof (Pos2Nat.is_pos cp); lia. Qed.

  Global Instance pow2_complexity : Time.ComplexityBound pow2
    (fun cx => (96 * N.to_nat (val cx) + 2) ⋉ tt) := _.

  Global Instance pred_N_complexity : Time.ComplexityBound Pos.pred_N
    (fun cp => (16 * Pos.size_nat (val cp)) ⋉ tt) := _.

  Global Instance N_pred_complexity : Time.ComplexityBound N.pred
    (fun cx => (16 * N.size_nat (val cx) + 2) ⋉ tt) := _.

  Global Instance N_eqb_complexity : Time.ComplexityBound N.eqb
    (fun cx => 2 ⋉ fun cy => (50 * N.size_nat (val cx) + 33) ⋉ tt) := _.

  Global Instance pow2_eq_pos_complexity : Time.ComplexityBound pow2_eq_pos
    (fun cx => 5 ⋉ fun cp => (Pos.size_nat (val cp) * (16 * N.size_nat (val cx) + 52)) ⋉ tt).
  Proof.
    cbound.
    all: match goal with |- context [Pos.pred_N ?p] => pose proof (size_nat_pred (Npos p)) as H end;
      cbn [N.pred N.size_nat] in H; nia.
  Qed.

  Global Instance C_complexity : Time.ComplexityBound C
    (fun cx => 4 ⋉ C_pot (val cx)) := _.

  Global Instance zero_complexity : Time.ComplexityBound zero zero_pot := _.

  Global Instance V_complexity : Time.ComplexityBound V
    (fun cF => 2 ⋉ fun cx => V_cost (val cF) (pot cF) (val cx) ⋉ tt) := _.

  Global Instance W_complexity : Time.ComplexityBound W
    (fun cF => 2 ⋉ fun cx => W_cost (val cF) (pot cF) (val cx) ⋉ tt).
  Proof. cbound. all: rewrite E; lia. Qed.

  (** ** Bounds in the size of the arguments ([Bounds])

      The bounds above are in the lengths of the numbers ([N.size_nat],
      [Pos.size_nat]), as the majorants of [BFFFeasibility] are. In the sizes
      of the model ([Size]), which bound the lengths ([N_size_fact],
      [positive_size_fact]), the first-order functions have the following
      bounds. *)
  Global Instance pred_N_linear_bound : Time.LinearBound Pos.pred_N := _.
  Global Instance N_pred_linear_bound : Time.LinearBound N.pred := _.
  Global Instance N_eqb_linear_bound : Time.LinearBound N.eqb := _.
  Global Instance pow2_eq_pos_polynomial_bound : Time.PolynomialBound pow2_eq_pos := _.
  Global Instance C_polynomial_bound : Time.PolynomialBound C := _.
  Global Instance zero_constant_bound : Time.ConstantBound zero := _.

  (** [pow2] and [zeros] are linear in the value of their first argument,
      that is exponential in its size: they have no polynomial bound. *)
  Lemma pos_to_nat_le_pow_size (p : positive) : Pos.to_nat p <= 2 ^ size p.
  Proof.
    pose proof (to_nat_lt_pow_size_nat p). pose proof (size_nat_le_size p).
    pose proof (Nat.pow_le_mono_r 2 _ _ ltac:(lia) H0). lia.
  Qed.

  Lemma N_to_nat_le_pow_size (x : N) : N.to_nat x <= 2 ^ size x.
  Proof.
    destruct x as [|p]; [cbn; lia|].
    pose proof (pos_to_nat_le_pow_size p). pose proof (size_Npos p).
    pose proof (Nat.pow_le_mono_r 2 _ _ ltac:(lia) (Nat.lt_le_incl _ _ H0)). cbn [N.to_nat]. lia.
  Qed.

  Lemma zeros_size_bound : Time.FirstOrderBound zeros (fun ss => 96 * 2 ^ List.nth 0 ss 0 + 5).
  Proof. cost_split. all: pose proof (pos_to_nat_le_pow_size ca); lia. Qed.

  Lemma pow2_size_bound : Time.FirstOrderBound pow2 (fun ss => 96 * 2 ^ List.nth 0 ss 0 + 2).
  Proof. cost_split. pose proof (N_to_nat_le_pow_size ca). lia. Qed.

  (** ** Higher-order polynomial bounds ([BFFFeasibility]) *)

  Lemma size_C x y : N.size_nat (C x y) <= 1.
  Proof. rewrite C_spec. destruct (y =? 2 ^ x)%N; cbn; lia. Qed.

  (** [V'], the denotation of a term of PV^ω equal to `V`, has a
      higher-order polynomial bound, as every term ([BFF_hpoly_bound]). *)
  Global Instance V'_hpoly : Time.HPolyBound (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) V' :=
    BFF_hpoly_bound _ V'_pv.

  (** The majorants: [C_maj a] of `C x` for [|x| <= a], [fun _ => 1] of
      [zero], the majorant of `V` in the majorant [mF] of `F` and the bound
      [a] of [|x|], and the majorant of [W] on arguments with a size bound
      ([smaj]): in the majorants [mF] of the complexity of `F` and [nF] of
      its size, and the bounds [a] and [b] of [|x|]. They are the higher-order polynomials
      written with [db] below, named so that [lia] sees them as atoms. *)
  Definition C_maj (a : nat) : M (tN ⇒ tN) := fun b => b * (16 * a + 52) + 16.
  Definition V_maj (mF : M ((tN ⇒ tN) ⇒ tN)) (a : nat) : nat :=
    51 * mF (C_maj a) + mF (fun _ => 1) + 55.
  Definition W_maj (mF nF : M ((tN ⇒ tN) ⇒ tN)) (a b : nat) : nat :=
    V_maj mF a + 96 * nF (C_maj a) + 9.

  (** The same majorants as higher-order polynomials: [C_poly a] is the
      majorant of the potential [C_pot x] for [|x| <= a], and [V_poly],
      [W_poly] are written with it. They evaluate to [C_maj], [V_maj] and
      [W_maj]. *)
  Definition C_poly : hpoly (tN ⇒ tN ⇒ tN) := db <{ λ a b, b * (16 * a + 52) + 16 }>.

  Definition V_poly : hpoly (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) :=
    tapp (db <{ λ c mF a, 51 * mF (c a) + mF (λ _, 1) + 55 }>
          : hpoly ((tN ⇒ tN ⇒ tN) ⇒ ((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) C_poly.

  Definition W_poly : hpoly (dbl (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) :=
    tapp (tapp (db <{ λ v c mF nF a b, v mF a + 96 * nF (c a) + 9 }>
          : hpoly ((((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN) ⇒ (tN ⇒ tN ⇒ tN) ⇒
                   ((tN ⇒ tN) ⇒ tN) ⇒ ((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN ⇒ tN)) V_poly) C_poly.

  Lemma C_maj_mono a : monotone (tN ⇒ tN) (C_maj a).
  Proof. intros b b' Hb. cbn in *. unfold C_maj. nia. Qed.

  Lemma const_mono k : monotone (tN ⇒ tN) (fun _ => k).
  Proof. intros ? ? ?. cbn. lia. Qed.

  Lemma maj_C x a : N.size_nat x <= a -> maj (bits (tN ⇒ tN)) (C x) (C_pot x) (C_maj a).
  Proof. intros Hx y cy b _ Hy. cbn in *. unfold C_maj. pose proof (size_C x y). split; nia. Qed.

  Lemma maj_zero : maj (bits (tN ⇒ tN)) zero zero_pot (fun _ => 1).
  Proof. intros y cy b _ _. cbn. lia. Qed.

  (** The costs of `F` in `V`, on `C x` and on [zero], are bounded by its
      majorant: so is [V_cost]. *)
  Lemma V_cost_bound F cF mF x a :
    monotone ((tN ⇒ tN) ⇒ tN) mF -> maj (bits ((tN ⇒ tN) ⇒ tN)) F cF mF -> N.size_nat x <= a ->
    cost (cF (C x ⋊ C_pot x)) <= mF (C_maj a) /\ V_cost F cF x <= V_maj mF a.
  Proof.
    intros HmF HF Hx.
    destruct (HF _ _ _ (C_maj_mono a) (maj_C x a Hx)) as [HC1 HC2].
    destruct (HF _ _ _ (const_mono 1) maj_zero) as [Hz1 _].
    unfold V_maj. cbn [maj bits baseM V_cost] in *. norm_types. split; lia.
  Qed.

  (** `V` has a higher-order polynomial bound: its costs are those of `F`
      on `C x` and on [zero] ([V_cost_bound]). *)
  Lemma V_hpoly : Time.HPolyBound (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) V.
  Proof.
    refine (hpoly_intro _ _ V_poly _ V_complexity _).
    change ⟦_⟧ with V_maj.
    intros F cF mF HmF HF. split; [cbn; unfold V_maj; lia|].
    intros x cx a _ Hx. destruct (V_cost_bound F cF mF x a HmF HF Hx) as [_ HV].
    cbn [maj bits cost res val pot baseM]. split; [exact HV|].
    unfold V, V_maj. destruct (_ =? _)%N; cbn; lia.
  Qed.

  (** [W] has no higher-order polynomial bound, whatever its complexity: a
      majorant also bounds the lengths of the values ([maj] at [N]). The
      0-1 valued `F f = (if f (2^x) =? 0 then 0 else 1)`, with no cost, is majorized by
      [fun _ => 1], but the length [x + 1] of `W F x` is exponential in
      [|x|], whereas a higher-order polynomial of type [N ⇒ N] is bounded by
      a polynomial ([hpoly_growth], [pow2_not_poly]). *)
  Lemma W_not_hpoly : ~ Time.HPolyBound (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W.
  Proof.
    intros (c & m & _ & Hm).
    apply (pow2_not_poly (W_bound m)). intro n.
    change (2 ^ n <= ⟦m⟧ (fun _ => 1) (n + 1)). rewrite Nat.add_1_r.
    set (x0 := pow2 (N.of_nat n)).
    set (F := fun f : N -> N => if (f (pow2 x0) =? 0)%N then 0%N else 1%N).
    assert (HF : maj (bits ((tN ⇒ tN) ⇒ tN)) F (fun _ => 0 ⋉ tt) (fun _ => 1)).
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

  (** ** Bounds on sized arguments ([BFFFeasibility]) *)

  Corollary V_hpolyS : Time.HPolyBoundS (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) V.
  Proof. exact (hpoly_hpolyS _ _ V_hpoly). Qed.

  (** On an argument `F` of complexity [cF] majorized by [mF], with a size
      bound [sF] majorized by [nF], [W] costs at most `V` ([V_cost_bound]
      in [mF]) plus [96] times the size of `F` on `C x` ([W_cost_sized],
      in [nF]); its value is not longer than this size ([W_size_sized]). *)
  Lemma W_smaj : smaj (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W
    (fun cF => 2 ⋉ fun cx => W_cost (val cF) (pot cF) (val cx) ⋉ tt) W_maj.
  Proof.
    intros F cF mF sF nF HmF HnF HF HFs HFn. split; [cbn; unfold W_maj, V_maj; lia|].
    intros x cx a sx b _ _ Hx _ _.
    destruct (V_cost_bound F cF mF x a HmF HF Hx) as [_ HV].
    destruct (V_cost_bound F sF nF x a HnF HFn Hx) as [HS _].
    pose proof (W_cost_sized F cF sF x HFs) as HW. pose proof (W_size_sized F sF x HFs) as HZ.
    cbn [smaj bits cost res val pot baseM dbl]. unfold W_maj. split; lia.
  Qed.

  Theorem W_hpolyS : Time.HPolyBoundS (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W.
  Proof. refine (hpoly_introS _ _ W_poly _ W_complexity _). change ⟦_⟧ with W_maj. exact W_smaj. Qed.

  (** ** The complexities are size bounds

      The complexities of `C`, [zero], `V` and [W] are size bounds of them
      ([SizedComplexities] with [k = 0]). `V` and [W] ask `F` about `C x`
      and [zero], and read [x]. [W] creates its value [2^x], of length
      [x + 1], and pays for it in [W_cost]. *)
  Lemma C_complexity_sized : CSized (bits (tN ⇒ tN ⇒ tN)) C (fun cx => 4 ⋉ C_pot (val cx)).
  Proof.
    intros [[x []] [[y []] []]] _. exists ([tt], ([tt], tt)).
    split; [split; [repeat constructor | split; [repeat constructor | exact I]]|]. split.
    - pose proof (size_C x y). unfold C_pot. cbn. lia.
    - intros [[x' []] [[y' []] []]] _ (_ & Hx & _ & Hy & _).
      inversion_clear Hx as [|? ? Ex _]. inversion_clear Hy as [|? ? Ey _]. cbn in *. now subst.
  Qed.

  Lemma V_complexity_sized : CSized (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) V
    (fun cF => 2 ⋉ fun cx => V_cost (val cF) (pot cF) (val cx) ⋉ tt).
  Proof.
    intros [[F cF] [[x []] []]] _. exists ([(C x ⋊ C_pot x, tt); (zero ⋊ zero_pot, tt)], ([tt], tt)).
    split.
    { split; [repeat constructor; [exact (C_sized x) | exact zero_sized_pot] | split; [repeat constructor | exact I]]. }
    split.
    - assert (N.size_nat (V F x) <= 1) by (unfold V; destruct (_ =? _)%N; cbn; lia).
      cbn -[V]. norm_types. lia.
    - intros [[F' cF'] [[x' []] []]] _ (_ & HF & _ & Hx & _).
      inversion_clear HF as [|? ? E1 HF']. inversion_clear HF' as [|? ? E2 _].
      inversion_clear Hx as [|? ? Ex _]. cbn in *. subst x'. unfold V. now rewrite E1, E2.
  Qed.

  Lemma W_complexity_sized : CSized (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W
    (fun cF => 2 ⋉ fun cx => W_cost (val cF) (pot cF) (val cx) ⋉ tt).
  Proof.
    intros [[F cF] [[x []] []]] _. exists ([(C x ⋊ C_pot x, tt); (zero ⋊ zero_pot, tt)], ([tt], tt)).
    split.
    { split; [repeat constructor; [exact (C_sized x) | exact zero_sized_pot] | split; [repeat constructor | exact I]]. }
    split.
    - assert (N.size_nat (W F x) <= if (F (C x) =? F zero)%N then 0 else S (N.to_nat x)).
      { rewrite W_spec. destruct (_ =? _)%N; [cbn; lia | rewrite size_nat_pow; lia]. }
      cbn -[W]. norm_types. destruct (_ =? _)%N; lia.
    - intros [[F' cF'] [[x' []] []]] _ (_ & HF & _ & Hx & _).
      inversion_clear HF as [|? ? E1 HF']. inversion_clear HF' as [|? ? E2 _].
      inversion_clear Hx as [|? ? Ex _]. cbn in *. subst x'. unfold W. now rewrite E1, E2.
  Qed.

  (** The contrast: no bound over all the potentials of [F], one over the
      sized ones. *)
  Corollary W_sized_contrast :
    ~ Time.HPolyBound (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W /\ Time.HPolyBoundS (bits (((tN ⇒ tN) ⇒ tN) ⇒ tN ⇒ tN)) W.
  Proof. exact (conj W_not_hpoly W_hpolyS). Qed.
End Type3Complexity.
