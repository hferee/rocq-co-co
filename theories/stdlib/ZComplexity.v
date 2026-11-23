(** * Functions on [Z]

    As in [PosComplexity], with the bit sizes ([zsize], [BitSize]). The
    constants of the division, the gcd and the power are not the smallest
    ones. *)

From Complexity Require Export PosComplexity.
From Complexity Require Import BitSize.
From Stdlib Require Import PArith ZArith.

(** No timeout in the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** Trailing zeros

    [Pos.pred_double] only recurses over the trailing zeros of its
    argument: they give the amortised analysis of [Z.pos_sub] below. *)

Fixpoint ptz (p : positive) : nat := match p with xO q => S (ptz q) | _ => 0 end.

Definition ztz (z : Z) : nat := match z with Z0 => 0 | Zpos p | Zneg p => ptz p end.

Lemma ptz_lt_size p : ptz p < Pos.size_nat p.
Proof. induction p; cbn; lia. Qed.

Lemma ztz_le_zsize z : ztz z <= zsize z.
Proof. destruct z; cbn; try pose proof (ptz_lt_size p); lia. Qed.

Lemma ptz_pred_double p : ptz (Pos.pred_double p) = 0.
Proof. destruct p; reflexivity. Qed.

Lemma ztz_double z : ztz (Z.double z) <= S (ztz z).
Proof. destruct z; cbn; lia. Qed.

Lemma ztz_succ_double z : ztz (Z.succ_double z) = 0.
Proof. destruct z; cbn; try apply ptz_pred_double; reflexivity. Qed.

Lemma ztz_pred_double z : ztz (Z.pred_double z) = 0.
Proof. destruct z; cbn; try apply ptz_pred_double; reflexivity. Qed.

(** ** Sizes of intermediate results

    Those of the division, the gcd and the power: the quotient and the
    remainder of [Z.pos_div_eucl] (which grows for a negative divisor), the
    cofactors of [Pos.ggcdn], and the powers of [Pos.iter (Z.mul z)]. *)
Section Intermediate.
  Local Open Scope Z_scope.

  Lemma pos_div_eucl_inv a b :
    0 <= fst (Z.pos_div_eucl a b) < 2 * Z.pos a /\
    0 <= snd (Z.pos_div_eucl a b) <= (2 * Z.pos a - 1) * (Z.abs b + 1).
  Proof.
    assert (HB : 0 <= Z.abs b /\ b <= Z.abs b /\ - b <= Z.abs b) by lia.
    set (B := Z.abs b) in *. clearbody B.
    induction a as [a IH | a IH |]; cbn [Z.pos_div_eucl].
    - destruct (Z.pos_div_eucl a b) as [q r]; cbn [fst snd] in *.
      rewrite (Pos2Z.inj_xI a). destruct (2 * r + 1 <? b) eqn:E; cbn [fst snd];
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; nia.
    - destruct (Z.pos_div_eucl a b) as [q r]; cbn [fst snd] in *.
      rewrite (Pos2Z.inj_xO a). destruct (2 * r <? b) eqn:E; cbn [fst snd];
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; nia.
    - destruct (2 <=? b); cbn [fst snd]; lia.
  Qed.

  Lemma pos_div_eucl_size a b :
    (zsize (fst (Z.pos_div_eucl a b)) <= S (Pos.size_nat a))%nat /\
    (zsize (snd (Z.pos_div_eucl a b)) <= Pos.size_nat a + zsize b + 2)%nat.
  Proof.
    pose proof (pos_div_eucl_inv a b) as [[Hq0 Hq] [Hr0 Hr]].
    assert (Ha : (zsize (2 * Z.pos a - 1) <= S (Pos.size_nat a))%nat).
    { change (S (Pos.size_nat a)) with (zsize (Z.pos a~0)). apply zsize_mono. lia. }
    assert (Hb : (zsize (Z.abs b + 1) <= S (zsize b))%nat).
    { destruct b as [|p|p]; cbn [Z.abs]; [cbn; lia | |];
        change (S (zsize (Z.pos p))) with (zsize (Z.pos p~0));
        [| change (S (zsize (Z.neg p))) with (zsize (Z.pos p~0))];
        apply zsize_mono; lia. }
    split.
    - change (S (Pos.size_nat a)) with (zsize (Z.pos a~0)). apply zsize_mono. lia.
    - pose proof (zsize_mul (2 * Z.pos a - 1) (Z.abs b + 1)).
      assert (zsize (snd (Z.pos_div_eucl a b)) <= zsize ((2 * Z.pos a - 1) * (Z.abs b + 1)))%nat
        by (apply zsize_mono; lia).
      lia.
  Qed.

  (** The accumulator of [Pos.iter (Z.mul z)]. *)
  Lemma iter_mul_size z x n :
    (zsize (Pos.iter (Z.mul z) x n) <= zsize x + Pos.to_nat n * zsize z)%nat.
  Proof.
    revert x. induction n as [n IH | n IH |]; intro x; cbn [Pos.iter];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1.
    - pose proof (zsize_mul z (Pos.iter (Z.mul z) (Pos.iter (Z.mul z) x n) n)).
      pose proof (IH x). pose proof (IH (Pos.iter (Z.mul z) x n)). lia.
    - pose proof (IH x). pose proof (IH (Pos.iter (Z.mul z) x n)). lia.
    - pose proof (zsize_mul z x). lia.
  Qed.
End Intermediate.

(** The cofactors of [Pos.ggcdn] are at most the arguments. *)
Lemma size_nat_cofactor g u x : x = (g * u)%positive -> Pos.size_nat u <= Pos.size_nat x.
Proof. intros ->. apply size_nat_le. nia. Qed.

Lemma ggcdn_size n a b :
  Pos.size_nat (fst (snd (Pos.ggcdn n a b))) <= Pos.size_nat a /\
  Pos.size_nat (snd (snd (Pos.ggcdn n a b))) <= Pos.size_nat b.
Proof.
  pose proof (Pos.ggcdn_correct_divisors n a b) as H.
  destruct (Pos.ggcdn n a b) as [g [aa bb]]; cbn [fst snd]. destruct H as [Ha Hb].
  split; eapply size_nat_cofactor; eassumption.
Qed.

(** [Pos.sub] goes through the type [mask] of [Pos.sub_mask], which the
    model does not represent; it is the function [pos_sub_pos], whose bound
    it gets ([complexity_pw] below). *)
Definition pos_sub_pos (x y : positive) : positive := Z.to_pos (Z.pos_sub x y).

Lemma pos_sub_to_pos x y : Pos.sub x y = pos_sub_pos x y.
Proof.
  unfold pos_sub_pos. destruct (Pos.compare_spec x y) as [-> | H | H].
  - rewrite Pos.sub_diag, Z.pos_sub_diag. reflexivity.
  - rewrite (Pos.sub_lt _ _ H), (Z.pos_sub_lt _ _ H). reflexivity.
  - rewrite (Z.pos_sub_gt _ _ H). reflexivity.
Qed.

(** [Z.pow_pos z] is [Pos.iter (Z.mul z) 1]: the iteration, for any
    accumulator, eta-reduced so that [cbound] sees a fixpoint under
    [fun z]. *)
Definition iter_mul (z : Z) : Z -> positive -> Z := Pos.iter (Z.mul z).

Module ZComplexity (Import Time : TimePos).

  (** ** Sizes *)
  Lemma zsize_le_size (z : Z) : zsize z <= size z.
  Proof.
    destruct z as [|p|p]; cbn;
      [pose proof size_Z0 | pose proof (size_Zpos p) | pose proof (size_Zneg p)];
      try pose proof (size_nat_le_size p); lia.
  Qed.
  Global Instance Z_size_fact (z : Z) : SizeFact z (zsize z <= size z) := zsize_le_size z.

  (** The facts on the sizes of the goal. *)
  Ltac zfacts := rewrite ?zsize_opp in *; size_facts.

  (** ** Opposite, absolute value, doubling *)

  Global Instance Z_opp_complexity : Time.ComplexityBound Z.opp (fun cz => 5 >|) := _.

  Global Instance Z_abs_complexity : Time.ComplexityBound Z.abs (fun cz => 5 >|) := _.

  Global Instance Z_double_complexity : Time.ComplexityBound Z.double (fun cz => 7 >|) := _.

  Global Instance Z_succ_double_complexity : Time.ComplexityBound Z.succ_double
    (fun cz => (14 * zsize (val cz) + 6) >|).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_pred_double_complexity : Time.ComplexityBound Z.pred_double
    (fun cz => (14 * zsize (val cz) + 6) >|).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Subtraction of positive numbers

      [Z.pos_sub] is recursive on its second argument. Each step may apply
      [Z.pred_double] or [Z.succ_double] to the result of the recursive call,
      at a cost linear in its size: the bound is quadratic. *)
  Global Instance Z_pos_sub_complexity : Time.ComplexityBound Z.pos_sub
    (fun cx => 4 +> fun cy =>
       (Pos.size_nat (val cy) *
          (14 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)))) >|).
  Proof. cbound. all: try pose proof (zsize_pos_sub cx cy); size_facts; nia. Qed.

  (** ** Arithmetic *)

  (** Additions of numbers of different signs use [Z.pos_sub]: quadratic,
      and linear by an amortised analysis (below). *)
  Global Instance Z_add_complexity : Time.ComplexityBound Z.add
    (fun cx => 1 +> fun cy =>
       (14 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy))) >|).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_sub_complexity : Time.ComplexityBound Z.sub
    (fun cx => 1 +> fun cy =>
       (14 * (zsize (val cx) + zsize (val cy)) * (zsize (val cx) + zsize (val cy)) + 12) >|).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_mul_complexity : Time.ComplexityBound Z.mul
    (fun cx => 1 +> fun cy =>
       (zsize (val cx) * (38 * (zsize (val cx) + zsize (val cy))) + 16) >|).
  Proof. cbound. all: zfacts; nia. Qed.

  (** ** Comparisons *)

  Global Instance CompOpp_complexity : Time.ComplexityBound CompOpp
    (fun cc => 3 >|) := _.

  Global Instance Z_compare_complexity : Time.ComplexityBound Z.compare
    (fun cx => 1 +> fun cy => (42 * zsize (val cy) + 19) >|).
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_eqb_complexity : Time.ComplexityBound Z.eqb
    (fun cx => 1 +> fun cy => (28 * zsize (val cx) + 17) >|).
  Proof. cbound. all: zfacts; lia. Qed.

  (** The case analysis of the comparison costs according to its result. *)
  Global Instance Z_ltb_complexity : Time.ComplexityBound Z.ltb
    (fun cx => 1 +> fun cy => (42 * zsize (val cy) + 27) >|) := _.

  Global Instance Z_leb_complexity : Time.ComplexityBound Z.leb
    (fun cx => 1 +> fun cy => (42 * zsize (val cy) + 27) >|) := _.

  (** ** Conversions *)

  Global Instance Z_of_nat_complexity : Time.ComplexityBound Z.of_nat
    (fun cn => (val cn * (27 * zsize (Z.of_nat (val cn))) + 3) >|).
  Proof. cbound. all: zfacts; nia. Qed.

  Global Instance Z_to_nat_complexity : Time.ComplexityBound Z.to_nat
    (fun cz => (14 * Z.to_nat (val cz) + 54 * zsize (val cz) + 4) >|).
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Linear bounds for addition and subtraction (amortised)

      [Z.succ_double] and [Z.pred_double] call [Pos.pred_double], which only
      walks over the trailing zeros of the result of the recursive call of
      [Z.pos_sub]; each of them was produced by an earlier step and is
      consumed once. The potential is [15] times the trailing zeros of the
      result. Typeclass search prefers these bounds (priority [0]). *)

  Global Instance Pos_pred_double_tz_complexity : Time.ComplexityBound Pos.pred_double
    (fun cp => (14 * ptz (val cp) + 10) >|) | 0 := _.

  Global Instance Z_succ_double_tz_complexity : Time.ComplexityBound Z.succ_double
    (fun cz => (14 * ztz (val cz) + 16) >|) | 0 := _.

  Global Instance Z_pred_double_tz_complexity : Time.ComplexityBound Z.pred_double
    (fun cz => (14 * ztz (val cz) + 16) >|) | 0 := _.

  Global Instance Z_pos_sub_linear_complexity : Time.ComplexityBound Z.pos_sub
    (fun cx => 4 +> fun cy =>
       (26 * (Pos.size_nat (val cx) + Pos.size_nat (val cy))
          - 15 * ztz (Z.pos_sub (val cx) (val cy))) >|) | 0.
  Proof.
    cbound. all: try pose proof (zsize_pos_sub cx cy);
      try pose proof (ztz_le_zsize (Z.pos_sub cx cy));
      try pose proof (ztz_double (Z.pos_sub cx cy));
      rewrite ?ztz_succ_double, ?ztz_pred_double, ?ptz_pred_double;
      try pose proof (ptz_lt_size cx); try pose proof (ptz_lt_size cy); size_facts; lia.
  Qed.

  Global Instance Z_add_linear_complexity : Time.ComplexityBound Z.add
    (fun cx => 1 +> fun cy =>
       (26 * (zsize (val cx) + zsize (val cy)) + 17) >|) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  Global Instance Z_sub_linear_complexity : Time.ComplexityBound Z.sub
    (fun cx => 1 +> fun cy =>
       (26 * (zsize (val cx) + zsize (val cy)) + 29) >|) | 0.
  Proof. cbound. all: zfacts; lia. Qed.

  (** ** Division, gcd and power

      In the sizes of their intermediate results (above), with constants
      that are not the smallest ones. *)

  (** Pointwise-equal functions have the same bounds, up to [2]: [Pos.sub]
      gets that of [pos_sub_pos]. *)
  Lemma complexity_pw {A B CA CB} `{Repr A CA} {RB : Repr B CB} (ar : Arity B) `{!PwExt RB ar}
    (f g : A -> B) (cg : ℂI A CA -> ℂO CB) :
    (forall a, pw_eq ar (f a) (g a)) -> Time.ComplexityBound g cg ->
    Time.ComplexityBound f (fun ca => 2 ⊕ cg ca).
  Proof.
    intros Hfg Hg.
    eapply (fix_closed_complexity ar f (fun _ => g) (fun _ => 1 +> cg));
      [cfix_pos | exact Hfg | apply constant_complexity, Hg |].
    apply bound_order_arr. intros ca _. cbn. split; [autounfold with costs; lia | reflexivity].
  Qed.

  Global Instance Z_to_pos_complexity : Time.ComplexityBound Z.to_pos (fun cz => 10 >|).
  Proof. cbound. Qed.

  Global Instance Z_sgn_complexity : Time.ComplexityBound Z.sgn (fun cz => 10 >|).
  Proof. cbound. Qed.

  Global Instance Pos_size_nat_complexity : Time.ComplexityBound Pos.size_nat
    (fun cp => (30 * Pos.size_nat (val cp) + 10) >|).
  Proof. cbound. Qed.

  (** *** Division *)

  (** The sizes of the quotient and of the remainder of the recursive call. *)
  Local Ltac div_facts :=
    repeat match goal with
    | E : Z.pos_div_eucl ?a ?b = (?q, ?r) |- _ =>
        let Hq := fresh "Hq" in let Hr := fresh "Hr" in
        pose proof (pos_div_eucl_size a b) as [Hq Hr]; rewrite E in Hq, Hr; cbn [fst snd] in Hq, Hr;
        pose proof (zsize_double q); pose proof (zsize_double r);
        pose proof (zsize_add (Z.double r) 1); pose proof (zsize_add (Z.double q) 1);
        cbn [zsize Pos.size_nat] in *; unfold Z.double in *; clear E
    end; size_facts.

  (** The inequalities left are not simplified ([csimplify]): it would
      take seconds. *)
  #[local] Ltac2 Set csimplify := Init.false.

  Global Instance Z_pos_div_eucl_complexity : Time.ComplexityBound Z.pos_div_eucl
    (fun ca => 4 +> fun cb =>
       (Pos.size_nat (val ca) * (100 * Pos.size_nat (val ca) + 200 * zsize (val cb) + 500)
        + 100) >|).
  Proof. cbound. all: div_facts; timeout 5 lia. Qed.

  Global Instance Z_div_eucl_complexity : Time.ComplexityBound Z.div_eucl
    (fun ca => 4 +> fun cb =>
       (zsize (val ca) * (100 * zsize (val ca) + 200 * zsize (val cb) + 600)
          + 100 * zsize (val cb) + 300) >|).
  Proof. cbound. all: div_facts; timeout 5 lia. Qed.

  #[local] Ltac2 Set csimplify := Init.true.

  Global Instance Z_div_complexity : Time.ComplexityBound Z.div
    (fun ca => 4 +> fun cb =>
       (zsize (val ca) * (100 * zsize (val ca) + 200 * zsize (val cb) + 600)
          + 100 * zsize (val cb) + 400) >|).
  Proof. cbound. all: div_facts; timeout 5 lia. Qed.

  Global Instance Z_modulo_complexity : Time.ComplexityBound Z.modulo
    (fun ca => 4 +> fun cb =>
       (zsize (val ca) * (100 * zsize (val ca) + 200 * zsize (val cb) + 600)
          + 100 * zsize (val cb) + 400) >|).
  Proof. cbound. all: div_facts; timeout 5 lia. Qed.

  (** *** Gcd *)

  Global Instance pos_sub_pos_complexity : Time.ComplexityBound pos_sub_pos
    (fun cx => 10 +> fun cy => (30 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)) + 30) >|).
  Proof. cbound. all: timeout 5 lia. Qed.

  Global Instance Pos_sub_complexity : Time.ComplexityBound Pos.sub
    (fun cx => 12 +> fun cy => (30 * (Pos.size_nat (val cx) + Pos.size_nat (val cy)) + 30) >|).
  Proof.
    exact (complexity_pw (ar_fun positive positive (ar_val positive)) Pos.sub pos_sub_pos _
             (fun x y => pos_sub_to_pos x y) pos_sub_pos_complexity).
  Qed.

  (** The sizes of the cofactors of the recursive call, and of the
      difference that it receives. *)
  Local Ltac ggcd_facts :=
    repeat match goal with
    | E : Pos.ggcdn ?n ?a ?b = (?g, (?u, ?v)) |- _ =>
        let H := fresh "Hs" in
        pose proof (ggcdn_size n a b) as H; rewrite E in H; cbn [fst snd] in H; clear E
    | E : Pos.ggcdn ?n ?a ?b = (?g, ?p) |- _ => clear E
    end;
    try match goal with
        |- context [Pos.size_nat (Pos.sub ?x ?y)] => pose proof (size_nat_sub x y) end;
    cbn [Pos.size_nat] in *.

  #[local] Ltac2 Set csimplify := Init.false.

  (** [Pos.ggcdn n a b] recurses at most [n] times, on arguments whose
      sizes do not grow. *)
  Global Instance Pos_ggcdn_complexity : Time.ComplexityBound Pos.ggcdn
    (fun cn => 10 +> fun ca => 10 +> fun cb =>
       (val cn * (200 * (Pos.size_nat (val ca) + Pos.size_nat (val cb)) + 300) + 20) >|).
  Proof. cbound. all: ggcd_facts; timeout 5 nia. Qed.

  #[local] Ltac2 Set csimplify := Init.true.

  Global Instance Pos_ggcd_complexity : Time.ComplexityBound Pos.ggcd
    (fun ca => 10 +> fun cb =>
       ((Pos.size_nat (val ca) + Pos.size_nat (val cb)) *
          (200 * (Pos.size_nat (val ca) + Pos.size_nat (val cb)) + 400) + 100) >|).
  Proof. cbound. all: timeout 5 nia. Qed.

  Global Instance Z_ggcd_complexity : Time.ComplexityBound Z.ggcd
    (fun ca => 10 +> fun cb =>
       ((zsize (val ca) + zsize (val cb)) * (200 * (zsize (val ca) + zsize (val cb)) + 400)
        + 200) >|).
  Proof. cbound. all: timeout 5 nia. Qed.

  (** *** Power

      [Z.pow x y] multiplies [y] times by [x] (unary in [y]): its cost is
      quadratic in [y], and in the size of [x]. *)

  (** The sizes of the accumulators of the recursive calls. *)
  Local Ltac pow_facts z :=
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *;
    repeat match goal with
    | |- context [zsize (?F ?x ?n)] =>
        lazymatch goal with H : (zsize (F x n) <= _)%nat |- _ => fail | _ => idtac end;
        let H := fresh "Hw" in
        assert (H : (zsize (F x n) <= zsize x + Pos.to_nat n * zsize z)%nat)
          by exact (iter_mul_size z x n)
    end;
    try match goal with |- context [Pos.to_nat ?n] => pose proof (Pos2Nat.is_pos n) end;
    try pose proof (zsize_pos z).

  Global Instance iter_mul_complexity : Time.ComplexityBound iter_mul
    (fun cz => 10 +> fun cx => 10 +> fun cn =>
       (Pos.to_nat (val cn) *
          (100 * zsize (val cz) * (zsize (val cx) + Pos.to_nat (val cn) * zsize (val cz)) + 100)
        + 10) >|).
  Proof. unfold iter_mul, Pos.iter. cbound. all: pow_facts cz; timeout 5 nia. Qed.

  Global Instance Z_pow_pos_complexity : Time.ComplexityBound Z.pow_pos
    (fun cz => 23 +> fun cn =>
       (Pos.to_nat (val cn)
          * (100 * zsize (val cz) * (1 + Pos.to_nat (val cn) * zsize (val cz)) + 100)
        + 20) >|).
  Proof. change Z.pow_pos with (fun z => iter_mul z 1). cbound. all: timeout 5 lia. Qed.

  Global Instance Z_pow_complexity : Time.ComplexityBound Z.pow
    (fun cx => 1 +> fun cy =>
       (Z.to_nat (val cy) * (100 * zsize (val cx) * (1 + Z.to_nat (val cy) * zsize (val cx)) + 100)
        + 60) >|).
  Proof. cbound. all: timeout 5 lia. Qed.

  (** ** Bounds in the sizes

      From the linear bounds of [Z.pos_sub], [Z.add] and [Z.sub]. [Z.to_nat]
      is exponential: its result is unary. *)
  Global Instance Z_opp_linear_bound : Time.LinearBound Z.opp := _.
  Global Instance Z_abs_linear_bound : Time.LinearBound Z.abs := _.
  Global Instance Z_double_linear_bound : Time.LinearBound Z.double := _.
  Global Instance Z_succ_double_linear_bound : Time.LinearBound Z.succ_double :=
    ltac:(clinear_using Z_succ_double_complexity).
  Global Instance Z_pred_double_linear_bound : Time.LinearBound Z.pred_double :=
    ltac:(clinear_using Z_pred_double_complexity).
  Global Instance Z_pos_sub_linear_bound : Time.LinearBound Z.pos_sub := _.
  Global Instance Z_add_linear_bound : Time.LinearBound Z.add := _.
  Global Instance Z_sub_linear_bound : Time.LinearBound Z.sub := _.
  Global Instance Z_mul_polynomial_bound : Time.PolynomialBound Z.mul := _.
  Global Instance CompOpp_linear_bound : Time.LinearBound CompOpp := _.
  Global Instance Z_compare_linear_bound : Time.LinearBound Z.compare := _.
  Global Instance Z_eqb_linear_bound : Time.LinearBound Z.eqb := _.
  Global Instance Z_ltb_linear_bound : Time.LinearBound Z.ltb := _.
  Global Instance Z_leb_linear_bound : Time.LinearBound Z.leb := _.

  Global Instance Z_of_nat_polynomial_bound : Time.PolynomialBound Z.of_nat.
  Proof.
    cpolynomial.
    all: match goal with |- context [Z.of_nat ?n] => pose proof (zsize_of_nat n) end.
    all: nia.
  Qed.

  (** ** Bounds in the sizes, with their constants

      From the bounds above: a bit size is at most the size ([SizeFact]). *)

  Lemma Z_succ_double_size_complexity :
    Time.ComplexityBound Z.succ_double
      (fun (cz : ℂI Z _) => (14 * #|val cz| + 6) >|).
  Proof. csize_using Z_succ_double_complexity. Qed.

  Lemma Z_pred_double_size_complexity :
    Time.ComplexityBound Z.pred_double
      (fun (cz : ℂI Z _) => (14 * #|val cz| + 6) >|).
  Proof. csize_using Z_pred_double_complexity. Qed.

  Lemma Z_pos_sub_size_complexity :
    Time.ComplexityBound Z.pos_sub
      (fun (cx : ℂI positive _) => 4 +> fun (cy : ℂI positive _) =>
         (#|val cy| * (14 * (#|val cx| + #|val cy|))) >|).
  Proof. csize_using Z_pos_sub_complexity. Qed.

  Lemma Z_add_size_complexity :
    Time.ComplexityBound Z.add
      (fun (cx : ℂI Z _) => 1 +> fun (cy : ℂI Z _) =>
         (14 * (#|val cx| + #|val cy|) * (#|val cx| + #|val cy|)) >|).
  Proof. csize_using Z_add_complexity. Qed.

  Lemma Z_sub_size_complexity :
    Time.ComplexityBound Z.sub
      (fun (cx : ℂI Z _) => 1 +> fun (cy : ℂI Z _) =>
         (14 * (#|val cx| + #|val cy|) * (#|val cx| + #|val cy|) + 12) >|).
  Proof. csize_using Z_sub_complexity. Qed.

  Lemma Z_mul_size_complexity :
    Time.ComplexityBound Z.mul
      (fun (cx : ℂI Z _) => 1 +> fun (cy : ℂI Z _) =>
         (#|val cx| * (38 * (#|val cx| + #|val cy|)) + 16) >|).
  Proof. csize_using Z_mul_complexity. Qed.

  Lemma Z_compare_size_complexity :
    Time.ComplexityBound Z.compare
      (fun cx => 1 +> fun (cy : ℂI Z _) => (42 * #|val cy| + 19) >|).
  Proof. csize_using Z_compare_complexity. Qed.

  Lemma Z_eqb_size_complexity :
    Time.ComplexityBound Z.eqb
      (fun (cx : ℂI Z _) => 1 +> fun cy => (28 * #|val cx| + 17) >|).
  Proof. csize_using Z_eqb_complexity. Qed.

  Lemma Z_ltb_size_complexity :
    Time.ComplexityBound Z.ltb
      (fun cx => 1 +> fun (cy : ℂI Z _) => (42 * #|val cy| + 27) >|).
  Proof. csize_using Z_ltb_complexity. Qed.

  Lemma Z_leb_size_complexity :
    Time.ComplexityBound Z.leb
      (fun cx => 1 +> fun (cy : ℂI Z _) => (42 * #|val cy| + 27) >|).
  Proof. csize_using Z_leb_complexity. Qed.

  Lemma Z_add_linear_size_complexity :
    Time.ComplexityBound Z.add
      (fun (cx : ℂI Z _) => 1 +> fun (cy : ℂI Z _) => (26 * (#|val cx| + #|val cy|) + 17) >|).
  Proof. csize_using Z_add_linear_complexity. Qed.

  Lemma Z_sub_linear_size_complexity :
    Time.ComplexityBound Z.sub
      (fun (cx : ℂI Z _) => 1 +> fun (cy : ℂI Z _) => (26 * (#|val cx| + #|val cy|) + 29) >|).
  Proof. csize_using Z_sub_linear_complexity. Qed.

End ZComplexity.
