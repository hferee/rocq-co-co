(** * Complexity of boolean functions from the standard library

    They are not recursive: compilation and typeclass search derive their
    complexity, and only the claimed bound remains to be checked. The
    constants are the smallest ones (see [NatComplexity]). *)

From Complexity Require Export TimeCostModel.
From Stdlib Require Import Bool.

Module BoolComplexity (Import M : TimeCostModel).

  Global Instance negb_complexity : ComplexityBound negb (fun cb => 2 ⋉ tt) := _.

  Global Instance andb_complexity : ComplexityBound andb
    (fun ca => 2 ⋉ fun cb => 14 ⋉ tt) := _.

  Global Instance orb_complexity : ComplexityBound orb
    (fun ca => 2 ⋉ fun cb => 12 ⋉ tt) := _.

  (** ** Bounds in the size of the arguments *)
  Global Instance negb_linear_bound : LinearBound negb := _.
  Global Instance andb_linear_bound : LinearBound andb := _.
  Global Instance orb_linear_bound : LinearBound orb := _.
End BoolComplexity.
