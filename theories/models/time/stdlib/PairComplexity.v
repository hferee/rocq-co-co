(** * Projections of pairs

    As in [BoolComplexity], by compilation and typeclass search. The
    elements are of any data: the complexity of a projection is that of the
    element. *)

From Complexity Require Export TimeCostModel.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

Module PairComplexity (Import Time : TimeCostModel).
  Global Instance fst_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fst A B) (fun cp => 5 +> fst (pot cp)) := _.
  Global Instance snd_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@snd A B) (fun cp => 3 +> snd (pot cp)) := _.

  (** ** Bounds in the sizes, for ground data: constant *)
  Global Instance fst_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}
    {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.ConstantBound (@fst A B) := _.
  Global Instance snd_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}
    {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.ConstantBound (@snd A B) := _.
End PairComplexity.
