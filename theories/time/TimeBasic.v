(** * The time cost model: application and basic functions

    The first part of the time cost model ([TimeCostModel]), heavily
    inspired by Forster & Künze's coq-library-complexity: the costs of the
    identity, of application, of composition and of constant functions. The
    complexities ([ℂI], [ℂO]) and the application [·] are defined in
    [CostModel], independently of the resource. *)

From Complexity Require Export CostModel.
Module Type BasicTimeCostModel (Import CM : CostModel).

  (** ** Constants

      The costs of the primitives are constants, fixed by each cost model:
      [TimeCostModel] sets them all to [1]. [c_clo] is the cost of a partial
      application (building a closure). A full application of a combinator
      ([TimeCombinators]) has a cost of its own: the projections of an
      environment [c_ehd] and [c_etl], the call of a closure [c_Lam], the
      constants [c_Kc] (also for [fun _ => b]), the identity [c_Ic] (also for
      [fun x => x]), the composition [c_compose], and [c_Cc] and [c_Sc].
      They are equal in the models of L, and differ on a machine
      ([MachineCostModel]). The models of the datatypes and of fixpoints
      have their own constants. *)
  Parameter c_clo : nat.
  Parameter c_ehd c_etl c_Lam c_Kc c_Ic c_compose c_Cc c_Sc : nat.
  #[global] Hint Unfold c_clo c_ehd c_etl c_Lam c_Kc c_Ic c_compose c_Cc c_Sc : costs.

  (** [c_frame]: the cost of an evaluation that is not in tail position,
      whose value is used afterwards (a frame on the stack of a machine,
      pushed and popped). It is charged by the combinators that evaluate a
      subterm before using its value: the argument of [compose], the two
      subterms of [Sc], the function of [Cc], and the matched value of a
      case analysis. A call in tail position does not pay it. [0] in the
      models whose instance has no stack ([TimeCostModel]: L reduces terms). *)
  Parameter c_frame : nat.
  #[global] Hint Unfold c_frame : costs.

  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat,
  or make mistakes anymore *)

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  #[global] Declare Instance id_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (fun (x : A) => x) (fun ca => (c_Ic +> pot ca) : ℂO CA).

  (* Note : we are using the unfolding of [@id A] here so that typeclass
    resolution works *)

  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
    {v : A} {f : A -> B} {cv : CA} (cf : ℂI A CA -> ℂO CB),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound (f v: B) (res (cf (v ⋊ cv))).

  (* More convenient: the instantiation direct application of compose. *)
  #[global] Declare Instance compose_complexity : forall {A B C CA CB CC}
    `{Repr A CA} `{Repr B CB} `{Repr C CC}
    (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
    ComplexityBound f cf ->
    ComplexityBound g cg ->
    ComplexityBound (compose f g : A -> C)
                    (fun ca => c_compose ⊕ pot <$> (f ⋊ cf) · (c_frame ⊕ (g ⋊ cg) · ca)).

  #[global] Declare Instance constant_complexity :
    forall {A B CA CB} `{Repr A CA} `{Repr B CB} b {cb},
    ComplexityBound (b : B) (cb : CB) ->
    ComplexityBound (fun (_ : A) => b) (fun _ => c_Kc +> cb).

  (** [tt]: the empty environment of closures, to which closed code is
      applied (see [Combinators]). *)
  #[global] Declare Instance tt_complexity : ComplexityBound tt tt.

  (* Simple tactic that will be used to prove ComplexityBound goals.
    Maybe elaborated later. *)
  Ltac ctac := typeclasses eauto.
End BasicTimeCostModel.
