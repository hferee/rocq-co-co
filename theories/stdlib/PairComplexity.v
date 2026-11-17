(** * Complexity of the projections of pairs

    As in [BoolComplexity]: they are not recursive, compilation and
    typeclass search derive their complexity, and the constants are the
    smallest ones. Pairs are modelled for ground data, in both cost models
    ([TimeCostModelBase]). [Nat.div] and [Nat.modulo] project the pair
    computed by [Nat.divmod] ([NatComplexity]). *)

From Complexity Require Export TimeCostModel.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module PairComplexity (Import Time : TimeCostModelBase).
  Global Instance fst_complexity {A B} `{Ground A} `{Ground B} :
    Time.ComplexityBound (@fst A B) (fun cp => 5 >|) := _.
  Global Instance snd_complexity {A B} `{Ground A} `{Ground B} :
    Time.ComplexityBound (@snd A B) (fun cp => 3 >|) := _.

  Global Instance fst_constant_bound {A B} `{Ground A} `{Size A} `{Ground B} `{Size B} :
    Time.ConstantBound (@fst A B) := _.
  Global Instance snd_constant_bound {A B} `{Ground A} `{Size A} `{Ground B} `{Size B} :
    Time.ConstantBound (@snd A B) := _.

End PairComplexity.
