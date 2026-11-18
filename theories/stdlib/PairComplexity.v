(** * Complexity of the projections of pairs

    As in [BoolComplexity]: they are not recursive, compilation and
    typeclass search derive their complexity, and the constants are the
    smallest ones. The elements are of any data: the complexity of a
    projection is that of the element. [Nat.div] and [Nat.modulo] project
    the pair computed by [Nat.divmod] ([NatComplexity]). *)

From Complexity Require Export TimeCostModel.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module PairComplexity (Import Time : TimeCostModel).
  (** The complexity of a projection is that of the element. *)
  Global Instance fst_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fst A B) (fun cp => 5 +> fst (pot cp)) := _.
  Global Instance snd_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@snd A B) (fun cp => 3 +> snd (pot cp)) := _.

  (** For pairs of ground data: constant in the sizes. *)
  Global Instance fst_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}
    {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.ConstantBound (@fst A B) := _.
  Global Instance snd_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}
    {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.ConstantBound (@snd A B) := _.
End PairComplexity.
