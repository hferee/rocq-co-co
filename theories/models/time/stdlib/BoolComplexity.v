(** * Boolean functions

    Not recursive: compilation and typeclass search prove the bounds, with
    the smallest constants. Over the model without lists, options and pairs
    ([TimeCostModelBase]). *)

From Complexity Require Export TimeCostModel.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

Module BoolComplexity (Import Time : TimeCostModelBase).

  Global Instance negb_complexity : Time.ComplexityBound negb (fun cb => 3 >|) := _.

  Global Instance andb_complexity : Time.ComplexityBound andb
    (fun ca => 1 +> fun cb => 4 >|) := _.

  Global Instance orb_complexity : Time.ComplexityBound orb
    (fun ca => 1 +> fun cb => 4 >|) := _.

  Global Instance Bool_eqb_complexity : Time.ComplexityBound Bool.eqb
    (fun ca => 1 +> fun cb => 6 >|) := _.

  (** ** Bounds in the sizes: constant *)
  Global Instance negb_constant_bound : Time.ConstantBound negb := _.
  Global Instance andb_constant_bound : Time.ConstantBound andb := _.
  Global Instance orb_constant_bound : Time.ConstantBound orb := _.
  Global Instance Bool_eqb_constant_bound : Time.ConstantBound Bool.eqb := _.
End BoolComplexity.
