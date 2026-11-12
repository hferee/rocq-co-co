(** * Counting the operations of Strassen's matrix product

    Matrices of size [2^k × 2^k] are quadtrees of depth [k] ([qmat],
    [full]), and Strassen's product splits them in four blocks and makes
    seven recursive products ([strassen]), instead of eight. Strassen's
    algorithm needs subtractions: the entries are integers ([Z]).

    The model ([StrassenTimeCostModel]) is [ArithOpsTimeCostModel] with the
    integer operations and the quadtrees: an addition costs [c_add], a
    subtraction [c_sub], a multiplication [c_mul], an unfolding of a
    fixpoint [c_fix], and everything else is free. On matrices of size
    [2^k × 2^k], the product takes [7^k] multiplications,
    [4 (7^k - 4^k)] additions and [2 (7^k - 4^k)] subtractions
    ([strassen_count]).

    The depth [k] is given as a list of length [k], since the model has no
    case analysis on [nat] (as for [HornerCount]). The bound of [strassen]
    holds for all inputs: its cost is a function of the inputs
    ([strassen_cost]), which follows the algorithm, and which is computed
    on the quadtrees of depth [k].

    The matrices of CoqEAL (Dénès, Mörtberg & Siles, A refinement-based
    approach to computational algebra in Coq, ITP 2012), which has a
    verified Strassen product, are MathComp matrices, with dependent sizes
    and generic rings: their functions cannot be analysed here as they
    are. *)

From Complexity Require Import TimeArith.
From Stdlib Require Import List ZArith.
Import ListNotations.

(** ** Matrices as quadtrees *)

Inductive qmat : Type :=
| QLeaf (z : Z)
| QNode (a11 a12 a21 a22 : qmat).

(** Case combinator (see [Combinators]). *)
Definition qmat_case {E A : Type} (fl : env E Z -> A)
  (fn : env (env (env (env E qmat) qmat) qmat) qmat -> A) (q : E -> qmat) (e : E) : A :=
  match q e with
  | QLeaf z => fl (ECons e z)
  | QNode a b c d => fn (ECons (ECons (ECons (ECons e a) b) c) d)
  end.

#[global] Typeclasses Opaque qmat_case.
#[global] Hint Unfold qmat_case : comb.

(** `full k a`: `a` is a matrix of size [2^k × 2^k]. *)
Fixpoint full (k : nat) (a : qmat) : Prop :=
  match k, a with
  | O, QLeaf _ => True
  | S k, QNode a11 a12 a21 a22 => full k a11 /\ full k a12 /\ full k a21 /\ full k a22
  | _, _ => False
  end.

Fixpoint qleaves (a : qmat) : nat :=
  match a with QLeaf _ => 1 | QNode a b c d => qleaves a + qleaves b + qleaves c + qleaves d end.

Fixpoint qnodes (a : qmat) : nat :=
  match a with QLeaf _ => 0 | QNode a b c d => 1 + qnodes a + qnodes b + qnodes c + qnodes d end.

(** ** Sums, differences and Strassen's product *)

Fixpoint qadd (a b : qmat) : qmat :=
  match a, b with
  | QLeaf x, QLeaf y => QLeaf (x + y)
  | QNode a11 a12 a21 a22, QNode b11 b12 b21 b22 =>
      QNode (qadd a11 b11) (qadd a12 b12) (qadd a21 b21) (qadd a22 b22)
  | _, _ => QLeaf 0
  end.

Fixpoint qsub (a b : qmat) : qmat :=
  match a, b with
  | QLeaf x, QLeaf y => QLeaf (x - y)
  | QNode a11 a12 a21 a22, QNode b11 b12 b21 b22 =>
      QNode (qsub a11 b11) (qsub a12 b12) (qsub a21 b21) (qsub a22 b22)
  | _, _ => QLeaf 0
  end.

Fixpoint strassen (d : list unit) (a b : qmat) {struct d} : qmat :=
  match d with
  | [] => match a, b with QLeaf x, QLeaf y => QLeaf (x * y) | _, _ => QLeaf 0 end
  | _ :: d =>
      match a, b with
      | QNode a11 a12 a21 a22, QNode b11 b12 b21 b22 =>
          let m1 := strassen d (qadd a11 a22) (qadd b11 b22) in
          let m2 := strassen d (qadd a21 a22) b11 in
          let m3 := strassen d a11 (qsub b12 b22) in
          let m4 := strassen d a22 (qsub b21 b11) in
          let m5 := strassen d (qadd a11 a12) b22 in
          let m6 := strassen d (qsub a21 a11) (qadd b11 b12) in
          let m7 := strassen d (qsub a12 a22) (qadd b21 b22) in
          QNode (qadd (qsub (qadd m1 m4) m5) m7) (qadd m3 m5)
                (qadd m2 m4) (qadd (qadd (qsub m1 m2) m3) m6)
      | _, _ => QLeaf 0
      end
  end.

(** ** Shapes and counts

    Sums, differences and Strassen's product of matrices of size
    [2^k × 2^k] have this size, which has [4^k] entries and [qn k] internal
    nodes. [adds k], [subs k] and [unfs k] are the numbers of additions,
    subtractions and unfoldings of Strassen's product on such matrices,
    besides the first unfolding: the recurrences of the algorithm, whose
    closed forms follow. *)

Lemma qadd_full k a b : full k a -> full k b -> full k (qadd a b).
Proof.
  revert a b; induction k as [|k IH]; intros [x|a1 a2 a3 a4] [y|b1 b2 b3 b4]; cbn; try tauto.
  intros (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4). repeat split; apply IH; assumption.
Qed.

Lemma qsub_full k a b : full k a -> full k b -> full k (qsub a b).
Proof.
  revert a b; induction k as [|k IH]; intros [x|a1 a2 a3 a4] [y|b1 b2 b3 b4]; cbn; try tauto.
  intros (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4). repeat split; apply IH; assumption.
Qed.

Lemma strassen_full k d a b : length d = k -> full k a -> full k b -> full k (strassen d a b).
Proof.
  revert d a b; induction k as [|k IH];
    intros [|u d] [x|a11 a12 a21 a22] [y|b11 b12 b21 b22] Hd; cbn in Hd |- *;
    try discriminate; try tauto.
  injection Hd as Hd. intros (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4).
  repeat split; repeat (apply qadd_full || apply qsub_full || apply IH); assumption.
Qed.

Create HintDb full.
#[local] Hint Resolve qadd_full qsub_full strassen_full : full.

Fixpoint qn (k : nat) : nat := match k with O => 0 | S k => 1 + 4 * qn k end.

Lemma qleaves_full k a : full k a -> qleaves a = 4 ^ k.
Proof.
  revert a; induction k as [|k IH]; intros [x|a1 a2 a3 a4]; cbn; try tauto.
  intros (H1 & H2 & H3 & H4). rewrite !IH by assumption. lia.
Qed.

Lemma qnodes_full k a : full k a -> qnodes a = qn k.
Proof.
  revert a; induction k as [|k IH]; intros [x|a1 a2 a3 a4]; cbn; try tauto.
  intros (H1 & H2 & H3 & H4). rewrite !IH by assumption. lia.
Qed.

Fixpoint adds (k : nat) : nat := match k with O => 0 | S k => 7 * adds k + 12 * 4 ^ k end.
Fixpoint subs (k : nat) : nat := match k with O => 0 | S k => 7 * subs k + 6 * 4 ^ k end.
Fixpoint unfs (k : nat) : nat :=
  match k with O => 0 | S k => 7 * (1 + unfs k) + 18 * (1 + 4 * qn k) end.

Lemma qn_closed k : 3 * qn k + 1 = 4 ^ k.
Proof. induction k; cbn [qn Nat.pow]; lia. Qed.

Lemma adds_closed k : adds k = 4 * (7 ^ k - 4 ^ k).
Proof.
  enough (adds k + 4 * 4 ^ k = 4 * 7 ^ k) by lia.
  induction k; cbn [adds Nat.pow]; lia.
Qed.

Lemma subs_closed k : subs k = 2 * (7 ^ k - 4 ^ k).
Proof.
  enough (subs k + 2 * 4 ^ k = 2 * 7 ^ k) by lia.
  induction k; cbn [subs Nat.pow]; lia.
Qed.

(** With the first one, [(49 * 7^k - 48 * 4^k + 5) / 6] unfoldings. *)
Lemma unfs_closed k : 6 * (1 + unfs k) + 48 * 4 ^ k = 49 * 7 ^ k + 5.
Proof. induction k; cbn [unfs Nat.pow]; [lia | pose proof (qn_closed k); lia]. Qed.

(** ** The model *)

(** Quadtrees are ground data, with constructors and a case analysis. *)
Module Type QMatTimeCostModel
  (Import Time : CostModel) (Import BT : BasicTimeCostModel Time)
  (Import CB : CombinatorTimeCostModel Time BT) (Import ZD : ZData Time).

  #[global] Declare Instance Repr_qmat : Ground qmat.
  #[global] Declare Instance qmat_complexity : forall q : qmat, Time.ComplexityBound q tt.

  Parameter c_qmat c_case_qmat : nat.
  #[global] Hint Unfold c_qmat c_case_qmat : costs.

  #[global] Declare Instance QLeaf_complexity : Time.ComplexityBound QLeaf (fun _ => c_qmat ⋉ tt).
  #[global] Declare Instance QNode_complexity : Time.ComplexityBound QNode
    (fun _ => c_clo ⋉ fun _ => c_clo ⋉ fun _ => c_clo ⋉ fun _ => c_qmat ⋉ tt).

  #[global] Declare Instance qmat_case_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    Time.ComplexityBound (@qmat_case E A)
      (fun cl : ℂI (env E Z -> A) (ℂI (env E Z) (CE * unit) -> ℂO CA) => c_clo ⋉
       fun cn : ℂI (env (env (env (env E qmat) qmat) qmat) qmat -> A)
                   (ℂI (env (env (env (env E qmat) qmat) qmat) qmat)
                       ((((CE * unit) * unit) * unit) * unit) -> ℂO CA) => c_clo ⋉
       fun cq : ℂI (E -> qmat) (ℂI E CE -> ℂO unit) => c_clo ⋉
       fun ce : ℂI E CE => c_case_qmat ⊕ cost (pot cq ce) ⊕
         match val cq (val ce) with
         | QLeaf z => pot cl (ECons (val ce) z ⋊ (pot ce, tt))
         | QNode a b c d =>
             pot cn (ECons (ECons (ECons (ECons (val ce) a) b) c) d ⋊ ((((pot ce, tt), tt), tt), tt))
         end).
End QMatTimeCostModel.

(** The operations on integers, as primitives: an addition and a
    multiplication cost as on numbers ([c_add], [c_mul]), a subtraction
    [c_sub]. *)
Module Type ZOpsTimeCostModel
  (Import Time : CostModel) (Import BT : BasicTimeCostModel Time) (Import ZD : ZData Time)
  (Import ND : NatData Time) (Import NA : NatArithTimeCostModel Time ND).

  Parameter c_sub : nat.
  #[global] Hint Unfold c_sub : costs.

  #[global] Declare Instance Zadd_complexity : Time.ComplexityBound Z.add
    (fun _ => c_clo ⋉ fun _ => c_add ⋉ tt).
  #[global] Declare Instance Zsub_complexity : Time.ComplexityBound Z.sub
    (fun _ => c_clo ⋉ fun _ => c_sub ⋉ tt).
  #[global] Declare Instance Zmul_complexity : Time.ComplexityBound Z.mul
    (fun _ => c_clo ⋉ fun _ => c_mul ⋉ tt).
End ZOpsTimeCostModel.

Module Type ParamStrassenTimeCostModel := ArithOpsTimeCostModel <+ ZData <+ ZOpsTimeCostModel
  <+ QMatTimeCostModel.

Module Type StrassenTimeCostModel := ParamStrassenTimeCostModel
  with Definition c_qmat := 0 with Definition c_case_qmat := 0.

Module StrassenCount (Import Time : StrassenTimeCostModel).

  Section Counts.
  Hypothesis Hfix : 1 <= c_fix.

  (** The cost of a sum or a difference: one operation on each leaf, and
      one unfolding for each of the four recursive calls of each node. *)
  Definition qop_cost (c : nat) (a : qmat) : nat := qleaves a * c + 4 * qnodes a * c_fix.

  Instance qadd_complexity : Time.ComplexityBound qadd
    (fun ca => c_fix ⋉ fun cb => qop_cost c_add (val ca) ⋉ tt).
  Proof. unfold qop_cost. cbound. Qed.

  Instance qsub_complexity : Time.ComplexityBound qsub
    (fun ca => c_fix ⋉ fun cb => qop_cost c_sub (val ca) ⋉ tt).
  Proof. unfold qop_cost. cbound. Qed.

  (** The cost of a call to [qadd] or [qsub] whose first argument is `a`. *)
  Definition qcall (c : nat) (a : qmat) : nat := c_fix + qop_cost c a.

  (** The cost of `strassen d a b`, after its application to [d]: it
      follows the algorithm. *)
  Fixpoint strassen_cost (d : list unit) (a b : qmat) {struct d} : nat :=
    match d with
    | [] => match a, b with QLeaf _, QLeaf _ => c_mul | _, _ => 0 end
    | _ :: d =>
        match a, b with
        | QNode a11 a12 a21 a22, QNode b11 b12 b21 b22 =>
            let m1 := strassen d (qadd a11 a22) (qadd b11 b22) in
            let m2 := strassen d (qadd a21 a22) b11 in
            let m3 := strassen d a11 (qsub b12 b22) in
            let m4 := strassen d a22 (qsub b21 b11) in
            let m5 := strassen d (qadd a11 a12) b22 in
            let m6 := strassen d (qsub a21 a11) (qadd b11 b12) in
            let m7 := strassen d (qsub a12 a22) (qadd b21 b22) in
            (* the ten sums and differences of blocks of the inputs *)
            qcall c_add a11 + qcall c_add b11 + qcall c_add a21 + qcall c_sub b12
            + qcall c_sub b21 + qcall c_add a11 + qcall c_sub a21 + qcall c_add b11
            + qcall c_sub a12 + qcall c_add b21
            (* the seven products *)
            + 7 * c_fix
            + strassen_cost d (qadd a11 a22) (qadd b11 b22) + strassen_cost d (qadd a21 a22) b11
            + strassen_cost d a11 (qsub b12 b22) + strassen_cost d a22 (qsub b21 b11)
            + strassen_cost d (qadd a11 a12) b22
            + strassen_cost d (qsub a21 a11) (qadd b11 b12)
            + strassen_cost d (qsub a12 a22) (qadd b21 b22)
            (* the eight sums and differences of products *)
            + qcall c_add m1 + qcall c_sub (qadd m1 m4) + qcall c_add (qsub (qadd m1 m4) m5)
            + qcall c_add m3 + qcall c_add m2 + qcall c_sub m1 + qcall c_add (qsub m1 m2)
            + qcall c_add (qadd (qsub m1 m2) m3)
        | _, _ => 0
        end
    end.

  Instance strassen_complexity : Time.ComplexityBound strassen
    (fun cd => c_fix ⋉ fun ca => 0 ⋉ fun cb => strassen_cost (val cd) (val ca) (val cb) ⋉ tt).
  Proof. cbound. all: unfold qcall; lia. Qed.
  End Counts.

  (** The cost of `strassen d a b` on matrices of size [2^k × 2^k], where
      [d] has length [k]. *)
  Theorem strassen_cost_full k d a b : length d = k -> full k a -> full k b ->
    strassen_cost d a b = 7 ^ k * c_mul + adds k * c_add + subs k * c_sub + unfs k * c_fix.
  Proof.
    revert d a b; induction k as [|k IH];
      intros [|u d] [x|a11 a12 a21 a22] [y|b11 b12 b21 b22] Hd; cbn in Hd |- *;
      try discriminate; try tauto; [lia|].
    injection Hd as Hd. intros (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4).
    unfold qcall, qop_cost.
    repeat match goal with
    | |- context [strassen_cost d ?x ?y] => rewrite (IH d x y) by auto with full
    end.
    repeat match goal with
    | |- context [qleaves ?x] => rewrite (qleaves_full k x) by auto with full
    | |- context [qnodes ?x] => rewrite (qnodes_full k x) by auto with full
    end.
    lia.
  Qed.

  (** By [strassen_complexity], the cost of `strassen d a b` is
      `c_fix + strassen_cost d a b`. On matrices of size [2^k × 2^k], it
      takes [7^k] multiplications, [4 (7^k - 4^k)] additions,
      [2 (7^k - 4^k)] subtractions, and [1 + unfs k] unfoldings
      ([unfs_closed]). *)
  Corollary strassen_count k d a b : length d = k -> full k a -> full k b ->
    c_fix + strassen_cost d a b =
      7 ^ k * c_mul + 4 * (7 ^ k - 4 ^ k) * c_add + 2 * (7 ^ k - 4 ^ k) * c_sub
      + (1 + unfs k) * c_fix.
  Proof.
    intros Hd Ha Hb.
    rewrite (strassen_cost_full k d a b Hd Ha Hb), adds_closed, subs_closed. lia.
  Qed.

End StrassenCount.
