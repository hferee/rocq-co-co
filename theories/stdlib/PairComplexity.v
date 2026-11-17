(** * Complexity of the projections of pairs

    As in [BoolComplexity]: they are not recursive, compilation and
    typeclass search derive their complexity, and the constants are the
    smallest ones. Pairs of ground data are in both cost models
    ([TimeCostModelBase]): [Nat.div] and [Nat.modulo] project the pair
    computed by [Nat.divmod] ([NatComplexity]). Pairs of any data are in
    the model with lists and options of any data ([HOTimeCostModel],
    [HProdTimeCostModel]): the complexity of a projection is that of the
    element ([HPairComplexity]). *)

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

(** Pairs of any data: the elements may be functions, or other data with
    complexities. *)
Module HPairComplexity (Import Time : HOTimeCostModel).
  Global Instance fst_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fst A B) (fun cp => 5 +> fst (pot cp)) := _.
  Global Instance snd_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@snd A B) (fun cp => 3 +> snd (pot cp)) := _.
End HPairComplexity.
