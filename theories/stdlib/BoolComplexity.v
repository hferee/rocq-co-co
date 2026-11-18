(** * Complexity of boolean functions from the standard library

    They are not recursive: compilation and typeclass search derive their
    complexity, and only the claimed bound remains to be checked. The
    constants are the smallest ones (see [NatComplexity]). They do not use
    lists: they are proved over [TimeCostModelBase], the model without
    lists, options and pairs. *)

From Complexity Require Export TimeCostModel.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module BoolComplexity (Import Time : TimeCostModelBase).

  Global Instance negb_complexity : Time.ComplexityBound negb (fun cb => 3 >|) := _.

  Global Instance andb_complexity : Time.ComplexityBound andb
    (fun ca => 1 +> fun cb => 4 >|) := _.

  Global Instance orb_complexity : Time.ComplexityBound orb
    (fun ca => 1 +> fun cb => 4 >|) := _.

  Global Instance Bool_eqb_complexity : Time.ComplexityBound Bool.eqb
    (fun ca => 1 +> fun cb => 6 >|) := _.

  (** ** Bounds in the size of the arguments: constant *)
  Global Instance negb_constant_bound : Time.ConstantBound negb := _.
  Global Instance andb_constant_bound : Time.ConstantBound andb := _.
  Global Instance orb_constant_bound : Time.ConstantBound orb := _.
  Global Instance Bool_eqb_constant_bound : Time.ConstantBound Bool.eqb := _.
End BoolComplexity.
