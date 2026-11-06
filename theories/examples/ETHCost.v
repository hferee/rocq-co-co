(** * Cost analysis of the ETH algorithm ([ETHAlgorithm])

    The functions are analysed as they are written in [ETHAlgorithm], by
    [cbound] ([TimeFix]): the compiler only replaces terms by
    convertible ones. The constants are the smallest ones
    for the shape of each bound (see [NatComplexity]). This file is the start
    of the analysis; the remarks at the end list what is covered. *)

From Complexity Require Export TimeStdlib ETHAlgorithm.
From Stdlib Require Import List.
Import ListNotations.

Module ETHCost (Import M : TimeStdlib).


  (** [memN x l]: recursive on its second argument. Each step compares with
      [Nat.eqb], whose cost is linear in [x] (unary numbers); [orb] evaluates
      both arguments. *)
  Global Instance memN_complexity : ComplexityBound memN
    (fun cx => 7 ⋉ fun cl =>
       (length (val cl) * (37 * val cx + 71) + 2) ⋉ tt) := _.

  Global Instance countN_complexity : ComplexityBound countN
    (fun cx => 7 ⋉ fun cl =>
       (length (val cl) * (37 * val cx + 115) + 2) ⋉ tt) := _.

  (** [eqbN a b]: recursive on its first argument, matches the second one. *)
  Global Instance eqbN_complexity : ComplexityBound eqbN
    (fun ca => 5 ⋉ fun cb =>
       (37 * list_sum (val ca) + 96 * length (val ca) + 15) ⋉ tt).
  Proof. cbound. all: unfold list_sum in *; lia. Qed.

  (** [insert_uniq x l]: the recursive call only happens in the last
      branch; its other branches return [l] itself. *)
  Global Instance insert_uniq_complexity : ComplexityBound insert_uniq
    (fun cx => 5 ⋉ fun cl =>
       (length (val cl) * (76 * val cx + 207) + 18) ⋉ tt) := _.

  (** [range n = seq 0 n]: not recursive, it follows from [seq]. *)
  Global Instance range_complexity : ComplexityBound range
    (fun cn => (29 * val cn + 2) ⋉ tt) := _.

  (** [fold_left Nat.add]: the cost of each addition is linear in the
      accumulator, so the bound depends on the values. *)
  Global Instance fold_left_add_complexity : ComplexityBound (fold_left Nat.add)
    (fun cl => 5 ⋉ fun ca =>
       (length (val cl) * (36 * (val ca + list_sum (val cl)) + 64) + 14) ⋉ tt).
  Proof. cbound. all: unfold list_sum in *; nia. Qed.

  Global Instance sumN_complexity : ComplexityBound sumN
    (fun cl =>
       (length (val cl) * (36 * list_sum (val cl) + 64) + 23) ⋉ tt) := _.
End ETHCost.

(** * Coverage of [ETHAlgorithm] by the current models

    With the generic fixpoint axiom ([TimeFix]), every structurally
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
