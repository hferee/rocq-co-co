(** * Cost analysis of the ETH algorithm ([ETHAlgorithm])

    The functions are analysed as they are written in [ETHAlgorithm]: [crec]
    states their unfolding equation ([FixCostModel]) and the compiler only
    replaces terms by convertible ones. The constants are the smallest ones
    for the shape of each bound (see [NatComplexity]). This file is the start
    of the analysis; the remarks at the end list what is covered. *)

From Complexity Require Import CostModel HOCostModel NatCostModel GroundListCostModel
  Combinators Compile CombinatorCostModel UnitCostModel BoolCostModel FixCostModel
  NatComplexity BoolComplexity ListComplexity ETHAlgorithm.
From Stdlib Require Import Program.Basics List Arith Lia.
Import ListNotations.

Module ETHCost (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import NT : NatTimeCostModel CM BT) (Import CB : CombinatorTimeCostModel CM BT)
  (Import UN : UnitTimeCostModel CM) (Import BO : BoolTimeCostModel CM BT)
  (Import LM : ListTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT).

  Module NC := NatComplexity CM BT NT CB UN BO FX.
  Module BC := BoolComplexity CM BT CB BO.
  Module LC := ListComplexity CM BT NT CB UN BO LM FX.
  Import NC BC LC.

  (** [memN x l]: recursive on its second argument. Each step compares with
      [Nat.eqb], whose cost is linear in [x] (unary numbers); [orb] evaluates
      both arguments. *)
  Lemma memN_complexity : ComplexityBound memN
    (fun cx : ℂI nat unit => 2 ⋉ fun cl : ℂI (list nat) unit =>
       (length (ival cl) * (5 * ival cx + 12) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cx; bo_split; destr_inputs; [cbn; lia |].
    destruct cl; cbn -[Nat.mul Nat.eqb]; unfold_comb; lia.
  Qed.
  Global Existing Instance memN_complexity.

  Lemma countN_complexity : ComplexityBound countN
    (fun cx : ℂI nat unit => 2 ⋉ fun cl : ℂI (list nat) unit =>
       (length (ival cl) * (5 * ival cx + 20) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cx; bo_split; destr_inputs; [cbn; lia |].
    destruct cl as [|y l]; cbn -[Nat.mul Nat.eqb]; unfold_comb; [lia |].
    destruct (Nat.eqb cx y); cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance countN_complexity.

  (** [eqbN a b]: recursive on its first argument, matches the second one. *)
  Lemma eqbN_complexity : ComplexityBound eqbN
    (fun ca : ℂI (list nat) unit => 2 ⋉ fun cb : ℂI (list nat) unit =>
       (5 * list_sum (ival ca) + 12 * length (ival ca) + 3) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro ca; bo_split; destr_inputs; [cbn; lia |].
    destruct ca, cb; cbn -[Nat.mul Nat.eqb]; unfold_comb; lia.
  Qed.
  Global Existing Instance eqbN_complexity.

  (** [insert_uniq x l]: the recursive call only happens in the last
      branch; its other branches return [l] itself. *)
  Lemma insert_uniq_complexity : ComplexityBound insert_uniq
    (fun cx : ℂI nat unit => 2 ⋉ fun cl : ℂI (list nat) unit =>
       (length (ival cl) * (10 * ival cx + 29) + 5) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cx; bo_split; destr_inputs; [cbn; lia |].
    destruct cl as [|y l]; cbn -[Nat.mul Nat.eqb Nat.ltb]; unfold_comb; [lia |].
    destruct (Nat.ltb cx y); cbn -[Nat.mul Nat.eqb Nat.ltb]; unfold_comb; [lia |].
    destruct (Nat.eqb cx y); cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance insert_uniq_complexity.

  (** [range n = seq 0 n]: not recursive, it follows from [seq]. *)
  Lemma range_complexity : ComplexityBound range
    (fun cn : ℂI nat unit => (8 * ival cn + 2) ⋉ tt).
  Proof.
    capply. unfold range. cbc.
    Unshelve. bo_split; destr_inputs; cbn -[Nat.mul]; lia.
  Qed.
  Global Existing Instance range_complexity.

  (** [fold_left Nat.add]: the cost of each addition is linear in the
      accumulator, so the bound depends on the values. *)
  Lemma fold_left_add_complexity : ComplexityBound (fold_left Nat.add)
    (fun cl : ℂI (list nat) unit => 2 ⋉ fun ca : ℂI nat unit =>
       (length (ival cl) * (5 * (ival ca + list_sum (ival cl)) + 8) + 2) ⋉ tt).
  Proof.
    crec; [cbc |].
    intro cl; bo_split; destr_inputs; [cbn; lia |].
    destruct cl; cbn -[Nat.mul]; unfold_comb; nia.
  Qed.
  Global Existing Instance fold_left_add_complexity.

  Lemma sumN_complexity : ComplexityBound sumN
    (fun cl : ℂI (list nat) unit =>
       (length (ival cl) * (5 * list_sum (ival cl) + 8) + 4) ⋉ tt).
  Proof.
    capply. unfold sumN. cbc.
    Unshelve. bo_split; destr_inputs; cbn -[Nat.mul list_sum]; lia.
  Qed.
  Global Existing Instance sumN_complexity.
End ETHCost.

(** * Coverage of [ETHAlgorithm] by the current models

    With the generic fixpoint axiom ([FixCostModel]), every structurally
    recursive function can be analysed as written, whatever its number of
    arguments, the position of its recursive argument, the matches of its
    body (also on other arguments), the depth of its recursive calls, and
    its type arguments; mutual recursion goes through an indexed function
    (see [Pos.add] in [PosComplexity]). This covers in particular the
    functions that were out of reach of the former recursors: polymorphic
    fixpoints ([fold_tuples], [find_tuple], [fold_sublists], [zipWith],
    [set_nth], ...), fixpoints with more than two arguments
    ([spar_M_search], [sparsify_fold], [rv_mul_aux], [Nat.div] through
    [divmod], ...), toplevel matches on other arguments ([nth],
    [combinations]), and deeper recursive calls ([Nat.even], [Nat.div2]).

    Still missing in the model:

    - Local fixpoints using variables of the enclosing function (the [go]
      of [lifted_factor]): [crec] only applies to a fixpoint at the head of
      the goal; a local one must be lambda-lifted first, or given a
      higher-order bound in terms of the complexities of its free variables.
    - Matches on user-defined inductive types and records ([params],
      [design], [literal], [pair_eig]): each needs its case combinator,
      constructors and an entry in [Compile.case_table]; a generic scheme
      over inductive types would avoid this.
    - [Z.div], [Z.modulo], [Z.ggcd] and [Z.pow] are not proved yet
      ([ZComplexity]): their bounds need invariants on the values computed
      ([Z.pos_div_eucl_bound], the fuel of [Pos.ggcdn]).

    Not a matter of expressiveness, but of proofs about the values computed
    (the paper's appendices): the bit sizes of the rationals manipulated by
    the counting routine, the size of the sparsification tree, and the
    parameter checks of [choose_params] for large inputs. *)
