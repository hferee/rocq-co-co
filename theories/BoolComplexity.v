(** * Complexity of boolean functions from the standard library

    They are not recursive: compilation and typeclass search derive their
    complexity, and only the claimed bound remains to be checked. The
    constants are the smallest ones (see [NatComplexity]). *)

From Complexity Require Import CostModel HOCostModel Combinators Compile
  CombinatorCostModel BoolCostModel.
From Stdlib Require Import Program.Basics Bool Lia.

Module BoolComplexity (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import BO : BoolTimeCostModel CM BT).

  Lemma negb_complexity : ComplexityBound negb (fun cb : ℂI bool unit => 2 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance negb_complexity.

  Lemma andb_complexity : ComplexityBound andb
    (fun ca : ℂI bool unit => 1 ⋉ fun cb : ℂI bool unit => 8 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance andb_complexity.

  Lemma orb_complexity : ComplexityBound orb
    (fun ca : ℂI bool unit => 1 ⋉ fun cb : ℂI bool unit => 6 ⋉ tt).
  Proof. cbound. Qed.
  Global Existing Instance orb_complexity.
End BoolComplexity.
