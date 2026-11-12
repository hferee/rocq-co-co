(** * Complexity of the basic feasible functionals ([BFF])

    The bounds of the constants of PV^ω, as defined in [BFF]. Each one is
    proved by [cbound], with the smallest constants for its shape. The
    first-order constants have linear bounds in the size of their arguments,
    except [smash], whose bound is polynomial ([Bounds]).

    The bound of the recursor `R` is higher-order: its cost ([R_cost]) is a
    function of the potentials of `F` and `h`, that is of the costs of
    their applications. When these costs and the lengths of the values of
    `h` are bounded by monotone functions of the lengths of the arguments,
    the cost of `R` is bounded by a second-order polynomial in these bounds
    ([R_cost_bound]): `R` preserves feasibility. *)

From Complexity Require Export TimeCostModel BFF.
From Stdlib Require Import NArith.

(** The constants of the cost of [rec_pos] ([rec_cost], [step_bound]):
    [rec_len] per bit of the comparison of the lengths ([bnd]), [rec_last]
    for the last bit of [q], [rec_step] for each other bit. They are
    abbreviations, so that the costs are numbers, and the proofs see them as
    numbers. *)
Abbreviation rec_len := 26 (only parsing).
Abbreviation rec_last := 55 (only parsing).
Abbreviation rec_step := 105 (only parsing).

(** The cost of `rec_pos a F h q`, from the potentials `pF` and `ph` of `F`
    and `h`: at each bit of [q], from the last one, the applications of `F`
    and `h`, and the comparison of the lengths of their values ([bnd]). *)
Fixpoint rec_cost (a : N) (F : N -> N -> N) (h : N -> N)
  (pF : ℂI N unit -> ℂO (ℂI N unit -> ℂO unit)) (ph : ℂI N unit -> ℂO unit)
  (q : positive) : nat :=
  let r := match q with xH => a | xO q' | xI q' => rec_pos a F h q' end in
  cost (pF (Npos q ⋊ tt)) + cost (res (pF (Npos q ⋊ tt)) (r ⋊ tt)) + cost (ph (Npos q ⋊ tt))
  + rec_len * Nat.min (N.size_nat (F (Npos q) r)) (N.size_nat (h (Npos q)))
  + match q with xH => rec_last | xO q' | xI q' => rec_step + rec_cost a F h pF ph q' end.

(** The cost of `R a F h w`. *)
Definition R_cost (a : N) (F : N -> N -> N) (h : N -> N)
  (pF : ℂI N unit -> ℂO (ℂI N unit -> ℂO unit)) (ph : ℂI N unit -> ℂO unit) (w : N) : nat :=
  match w with N0 => 0 | Npos q => rec_cost a F h pF ph q end.

(** ** Feasibility of the recursion

    When the costs of `F` and `h` are bounded by monotone functions `bF` and
    `bh` of the lengths of their arguments, and the lengths of the values of
    `h` by a monotone function `lh`, the cost of `R a F h w` is bounded by
    [|w| * step_bound |w|], a second-order polynomial in `bF`, `bh` and
    `lh`. The values of the recursion are bounded by the length of `h`
    ([R_size]), so that `F` is only applied to arguments of bounded length:
    this is why `R` preserves feasibility. *)
Section Feasibility.
  Variables (a : N) (F : N -> N -> N) (h : N -> N)
    (pF : ℂI N unit -> ℂO (ℂI N unit -> ℂO unit)) (ph : ℂI N unit -> ℂO unit)
    (bF : nat -> nat -> nat) (bh lh : nat -> nat).

  Hypothesis HF : forall w r,
    cost (pF (w ⋊ tt)) + cost (res (pF (w ⋊ tt)) (r ⋊ tt)) <= bF (N.size_nat w) (N.size_nat r).
  Hypothesis Hh : forall w, cost (ph (w ⋊ tt)) <= bh (N.size_nat w).
  Hypothesis Hl : forall w, N.size_nat (h w) <= lh (N.size_nat w).
  Hypothesis MF : forall n n' m m', n <= n' -> m <= m' -> bF n m <= bF n' m'.
  Hypothesis Mh : forall n n', n <= n' -> bh n <= bh n'.
  Hypothesis Ml : forall n n', n <= n' -> lh n <= lh n'.

  (** The cost of a step of the recursion on numbers of length [n]. *)
  Definition step_bound (n : nat) : nat :=
    bF n (Nat.max (N.size_nat a) (lh n)) + bh n + rec_len * lh n + rec_step.

  Lemma step_bound_mono n n' : n <= n' -> step_bound n <= step_bound n'.
  Proof.
    intro H. unfold step_bound. pose proof (Mh n n' H). pose proof (Ml n n' H).
    assert (bF n (Nat.max (N.size_nat a) (lh n)) <= bF n' (Nat.max (N.size_nat a) (lh n')))
      by (apply MF; lia).
    lia.
  Qed.

  (** One step, on [w] of length [n], from the value [r] of the recursion. *)
  Lemma step_le w r n :
    N.size_nat w = n -> N.size_nat r <= Nat.max (N.size_nat a) (lh n) ->
    cost (pF (w ⋊ tt)) + cost (res (pF (w ⋊ tt)) (r ⋊ tt)) + cost (ph (w ⋊ tt))
    + rec_len * Nat.min (N.size_nat (F w r)) (N.size_nat (h w)) + rec_step <= step_bound n.
  Proof.
    intros Hw Hr. unfold step_bound. pose proof (HF w r). pose proof (Hh w). pose proof (Hl w).
    assert (bF (N.size_nat w) (N.size_nat r) <= bF n (Nat.max (N.size_nat a) (lh n)))
      by (apply MF; lia).
    rewrite Hw in *. lia.
  Qed.

  Lemma rec_cost_bound q : rec_cost a F h pF ph q <= Pos.size_nat q * step_bound (Pos.size_nat q).
  Proof.
    induction q as [q IH|q IH|].
    1, 2: cbn [rec_cost]; cbn [Pos.size_nat]; rewrite Nat.mul_succ_l;
      pose proof (step_bound_mono (Pos.size_nat q) (S (Pos.size_nat q)) (Nat.le_succ_diag_r _));
      pose proof (Nat.mul_le_mono_l _ _ (Pos.size_nat q) H);
      (* the value of the recursion is bounded by the length of [h] *)
      pose proof (R_size a F h (Npos q) ltac:(discriminate)) as Hr; cbn [R] in Hr;
      pose proof (Hl (Npos q)); pose proof (Ml (Pos.size_nat q) (S (Pos.size_nat q)) ltac:(lia));
      match goal with |- context [N.size_nat (F ?w ?r)] =>
        pose proof (step_le w r (S (Pos.size_nat q)) eq_refl ltac:(cbn [N.size_nat] in *; lia))
      end; lia.
    - cbn [rec_cost Pos.size_nat]. pose proof (step_le 1 a 1 eq_refl ltac:(lia)). lia.
  Qed.

  Lemma R_cost_bound w : R_cost a F h pF ph w <= N.size_nat w * step_bound (N.size_nat w).
  Proof. destruct w as [|q]; [reflexivity | apply rec_cost_bound]. Qed.
End Feasibility.

Module BFFComplexity (Import Time : TimeCostModel).

  (** ** Sizes *)
  Lemma pos_size_nat_le_size (p : positive) : Pos.size_nat p <= size p.
  Proof.
    induction p; cbn; [pose proof (size_xI p) | pose proof (size_xO p) | pose proof size_xH]; lia.
  Qed.

  Lemma N_size_nat_le_size (n : N) : N.size_nat n <= size n.
  Proof.
    destruct n as [|p]; cbn; [lia|]. pose proof (pos_size_nat_le_size p). pose proof (size_Npos p). lia.
  Qed.
  Global Instance N_size_fact (n : N) : SizeFact n (N.size_nat n <= size n) := N_size_nat_le_size n.

  (** ** Constants *)

  Global Instance s0_complexity : Time.ComplexityBound s0 (fun cx => 7 ⋉ tt) := _.

  Global Instance s1_complexity : Time.ComplexityBound s1 (fun cx => 7 ⋉ tt) := _.

  Global Instance tr_complexity : Time.ComplexityBound tr (fun cx => 7 ⋉ tt) := _.

  Global Instance par_complexity : Time.ComplexityBound par (fun cx => 5 ⋉ tt) := _.

  Global Instance cond_complexity : Time.ComplexityBound cond
    (fun cx => 1 ⋉ fun cy => 2 ⋉ fun cz => 8 ⋉ tt) := _.

  Global Instance pad_pos_complexity : Time.ComplexityBound pad_pos
    (fun cx => 4 ⋉ fun cq => (28 * Pos.size_nat (val cq)) ⋉ tt) := _.

  Global Instance pad_complexity : Time.ComplexityBound pad
    (fun cx => 1 ⋉ fun cy => (28 * N.size_nat (val cy) + 13) ⋉ tt) := _.

  Global Instance chop_pos_complexity : Time.ComplexityBound chop_pos
    (fun cx => 4 ⋉ fun cq => (28 * Pos.size_nat (val cq)) ⋉ tt) := _.

  Global Instance chop_complexity : Time.ComplexityBound chop
    (fun cx => 1 ⋉ fun cy => (28 * N.size_nat (val cy) + 13) ⋉ tt) := _.

  Global Instance smash_pos_complexity : Time.ComplexityBound smash_pos
    (fun cx => 4 ⋉ fun cq =>
       (Pos.size_nat (val cq) * (28 * N.size_nat (val cx) + 41)) ⋉ tt) := _.

  Global Instance smash_complexity : Time.ComplexityBound smash
    (fun cx => 1 ⋉ fun cy =>
       (N.size_nat (val cy) * (28 * N.size_nat (val cx) + 41) + 13) ⋉ tt) := _.

  Global Instance pos_len_le_complexity : Time.ComplexityBound pos_len_le
    (fun cp => 4 ⋉ fun cq =>
       (26 * Nat.min (Pos.size_nat (val cp)) (Pos.size_nat (val cq)) + 6) ⋉ tt) := _.

  Global Instance len_le_complexity : Time.ComplexityBound len_le
    (fun ct => 1 ⋉ fun cu =>
       (26 * Nat.min (N.size_nat (val ct)) (N.size_nat (val cu)) + 23) ⋉ tt) := _.

  Global Instance bnd_complexity : Time.ComplexityBound bnd
    (fun ct => 1 ⋉ fun cb =>
       (26 * Nat.min (N.size_nat (val ct)) (N.size_nat (val cb)) + 31) ⋉ tt) := _.

  (** ** Bounded recursion on notation *)

  Global Instance rec_pos_complexity : Time.ComplexityBound rec_pos
    (fun ca => 4 ⋉
     fun cF => 2 ⋉
     fun ch => 2 ⋉
     fun cq =>
       rec_cost (val ca) (val cF) (val ch) (pot cF) (pot ch) (val cq) ⋉ tt) := _.

  Global Instance R_complexity : Time.ComplexityBound R
    (fun ca => 1 ⋉
     fun cF => 2 ⋉
     fun ch => 2 ⋉
     fun cw =>
       (R_cost (val ca) (val cF) (val ch) (pot cF) (pot ch) (val cw) + 35) ⋉ tt) := _.

  Lemma twice_complexity : Time.ComplexityBound twice
    (fun cf => 1 ⋉ fun cx =>
       (cost (pot cf (val cx ⋊ tt)) + cost (pot cf (val cf (val cx) ⋊ tt)) + 6) ⋉ tt).
  Proof. cbound. Qed.

  (** ** Bounds in the size of the arguments *)
  Global Instance s0_linear_bound : Time.LinearBound s0 := _.
  Global Instance s1_linear_bound : Time.LinearBound s1 := _.
  Global Instance tr_linear_bound : Time.LinearBound tr := _.
  Global Instance par_linear_bound : Time.LinearBound par := _.
  Global Instance cond_linear_bound : Time.LinearBound cond := _.
  Global Instance pad_linear_bound : Time.LinearBound pad := _.
  Global Instance chop_linear_bound : Time.LinearBound chop := _.
  Global Instance len_le_linear_bound : Time.LinearBound len_le := _.
  Global Instance bnd_linear_bound : Time.LinearBound bnd := _.
  Global Instance smash_polynomial_bound : Time.PolynomialBound smash := _.
End BFFComplexity.
