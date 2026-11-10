(** * Complexity of boolean functions from the standard library

    They are not recursive: compilation and typeclass search derive their
    complexity, and only the claimed bound remains to be checked. The
    constants are the smallest ones (see [NatComplexity]). *)

From Complexity Require Export TimeCostModel.

Module BoolComplexity (Import Time : TimeCostModel).

  Global Instance negb_complexity : Time.ComplexityBound negb (fun cb => 2 ⋉ tt) := _.

  Global Instance andb_complexity : Time.ComplexityBound andb
    (fun ca => 2 ⋉ fun cb => 14 ⋉ tt) := _.

  Global Instance orb_complexity : Time.ComplexityBound orb
    (fun ca => 2 ⋉ fun cb => 12 ⋉ tt) := _.

  (** ** Bounds in the size of the arguments: constant *)
  Global Instance negb_constant_bound : Time.ConstantBound negb := _.
  Global Instance andb_constant_bound : Time.ConstantBound andb := _.
  Global Instance orb_constant_bound : Time.ConstantBound orb := _.
End BoolComplexity.
