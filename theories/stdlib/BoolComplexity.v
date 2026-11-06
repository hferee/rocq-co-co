(** * Complexity of boolean functions from the standard library

    They are not recursive: compilation and typeclass search derive their
    complexity, and only the claimed bound remains to be checked. The
    constants are the smallest ones (see [NatComplexity]). *)

From Complexity Require Export TimeCostModel.

Module BoolComplexity (Import M : TimeCostModel).

  Global Instance negb_complexity : ComplexityBound negb (fun cb => 2 ⋉ tt) := _.

  Global Instance andb_complexity : ComplexityBound andb
    (fun ca => 2 ⋉ fun cb => 14 ⋉ tt) := _.

  Global Instance orb_complexity : ComplexityBound orb
    (fun ca => 2 ⋉ fun cb => 12 ⋉ tt) := _.

  (** ** Bounds in the size of the arguments: constant *)
  Global Instance negb_constant_bound : ConstantBound negb := _.
  Global Instance andb_constant_bound : ConstantBound andb := _.
  Global Instance orb_constant_bound : ConstantBound orb := _.
End BoolComplexity.
