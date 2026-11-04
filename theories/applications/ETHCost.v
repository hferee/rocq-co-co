(** * Cost analysis of the ETH algorithm ([ETHAlgorithm])

    The functions are analysed as they are written in [ETHAlgorithm], by
    [cbound] ([FixCostModel]): the compiler only replaces terms by
    convertible ones. The constants are the smallest ones
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
  (Import LM : ListTimeCostModel CM BT) (Import FX : FixTimeCostModel CM BT CB).

  Module NC := NatComplexity CM BT NT CB UN BO FX.
  Module BC := BoolComplexity CM BT CB BO.
  Module LC := ListComplexity CM BT NT CB UN BO LM FX.
  Import NC BC LC.

  (** [memN x l]: recursive on its second argument. Each step compares with
      [Nat.eqb], whose cost is linear in [x] (unary numbers); [orb] evaluates
      both arguments. *)
  Lemma memN_complexity : ComplexityBound memN
    (fun cx : ℂI nat unit => 38 ⋉ fun cl : ℂI (list nat) unit =>
       (length (val cl) * (54 * val cx + 105) + 2) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance memN_complexity.

  Lemma countN_complexity : ComplexityBound countN
    (fun cx : ℂI nat unit => 40 ⋉ fun cl : ℂI (list nat) unit =>
       (length (val cl) * (54 * val cx + 202) + 2) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance countN_complexity.

  (** [eqbN a b]: recursive on its first argument, matches the second one. *)
  Lemma eqbN_complexity : ComplexityBound eqbN
    (fun ca : ℂI (list nat) unit => 37 ⋉ fun cb : ℂI (list nat) unit =>
       (54 * list_sum (val ca) + 139 * length (val ca) + 9) ⋉ tt).
  Proof. cbound. all: unfold list_sum in *; lia. Qed.
  Global Existing Instance eqbN_complexity.

  (** [insert_uniq x l]: the recursive call only happens in the last
      branch; its other branches return [l] itself. *)
  Lemma insert_uniq_complexity : ComplexityBound insert_uniq
    (fun cx : ℂI nat unit => 59 ⋉ fun cl : ℂI (list nat) unit =>
       (length (val cl) * (95 * val cx + 311) + 11) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance insert_uniq_complexity.

  (** [range n = seq 0 n]: not recursive, it follows from [seq]. *)
  Lemma range_complexity : ComplexityBound range
    (fun cn : ℂI nat unit => (46 * val cn + 2) ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance range_complexity.

  (** [fold_left Nat.add]: the cost of each addition is linear in the
      accumulator, so the bound depends on the values. *)
  Lemma fold_left_add_complexity : ComplexityBound (fold_left Nat.add)
    (fun cl : ℂI (list nat) unit => 35 ⋉ fun ca : ℂI nat unit =>
       (length (val cl) * (55 * (val ca + list_sum (val cl)) + 96) + 7) ⋉ tt).
  Proof. cbound. all: unfold list_sum in *; nia. Qed.
  Global Existing Instance fold_left_add_complexity.

  Lemma sumN_complexity : ComplexityBound sumN
    (fun cl : ℂI (list nat) unit =>
       (length (val cl) * (55 * list_sum (val cl) + 96) + 43) ⋉ tt).
  Proof. cbound. Qed.
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
      of [lifted_factor]): [cbound] only applies to a fixpoint at the head of
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
