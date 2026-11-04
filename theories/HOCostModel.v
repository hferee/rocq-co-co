From Complexity Require Import CostModel.

(** * A Cost model for higher order-order functions, heavily inspired by
  Forster & Künze's coq-library-complexity. *)

(** An example of specialization of the cost model to handle time complexity of
  higher-order functions. The complexities ([ℂI], [ℂO]) and the application
  [·] are defined in [CostModel]. *)
Module Type BasicTimeCostModel (Import CM : CostModel).

  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat,
  or make mistakes anymore *)

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  Parameter id_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (fun (x : A) => x) (fun (ca : ℂI A CA) => (1 ⋉ pot ca) : ℂO CA).
  Global Existing Instance id_complexity.

  (* Note : we are using the unfolding of [@id A] here so that typeclass
    resolution works *)

  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
    {v : A} {f : A -> B} {cv : CA} (cf : ℂI A CA -> ℂO CB),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound (f v: B) (res (cf (v ⋊ cv))).

  (* More convenient: the instantiation direct application of compose. *)
  Parameter compose_complexity : forall {A B C CA CB CC}
    `{Repr A CA} `{Repr B CB} `{Repr C CC}
    (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
    ComplexityBound f cf ->
    ComplexityBound g cg ->
    ComplexityBound (compose f g : A -> C)
                    (fun ca : ℂI A CA => 1 ⊕ pot <$> (f ⋊ cf) · ((g ⋊ cg) · ca)).
  Global Existing Instance compose_complexity.

  Parameter constant_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB} b {cb},
    ComplexityBound (b : B) (cb : CB) ->
    ComplexityBound (fun (_ : A) => b) (fun (_ : ℂI A CA) => 1 ⋉ cb).
  Global Existing Instance constant_complexity.

  (* Simple tactic that will be used to prove ComplexityBound goals.
    Maybe elaborated later. *)
  Ltac ctac := typeclasses eauto.
End BasicTimeCostModel.
