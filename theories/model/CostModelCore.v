From Stdlib Require Export Classes.Morphisms Classes.RelationClasses Program.Basics Arith Lia.
From Complexity Require Export BasicClasses.

(** * Complexity model

    The notions shared by all cost models, whatever the resource they measure:
    time ([TimeCostModel]), space ([SpaceCostModel]), or specific function
    calls ([StrassenCount] for instance).

    For function types, a complexity is a function taking as input an input
    of the function together with its complexity ([ℂI]), and returning a
    cost together with the complexity of the output ([ℂO]). This is Forster
    & Künze's [timeComplexity] (which also receives the input value), with
    records instead of curried arguments and pairs. The output value is not
    part of a complexity, as it is determined by the function.


  More precisely, if types `A` and `B` have respective complexity types `CA` and
  `CB`, then the type of complexity bounds for functions of type `A -> B` will
  be `(ℂI A CA -> ℂO CB)`.
*)

(** ** Complexity types and operations *)

(** A value with its complexity (potential). This will be the input type of
  complexity bounds for functions. *)
#[projections(primitive)]
Record ℂI (A CA : Type) := { val : A; pot : CA }.
Infix "⋊" := (Build_ℂI _ _) (at level 40).
Arguments val {_ _}.
Arguments pot {_ _}.

(** A cost with a result: the writer monad of costs. For now, costs are natural
  numbers, we can see if other types make sense.
  This can be read as the complexity of an arbitrary term (not necessarily a
  value): the cost of normalising together with the cost of the value. *)
#[projections(primitive)]
Record ℂO (C : Type) := { cost : nat; res : C }.
Arguments cost {_}.
Arguments res {_}.
Notation "c +> r" := (Build_ℂO _ c r) (at level 55, right associativity).

(** [c >|]: the cost [c] of a ground type. The [res] will be automatically
  instantiated using typeclass inference as ground types have no distinguishable complexity bounds. *)
#[warnings="-postfix-notation-not-level-1"]
Notation "c >|" := (Build_ℂO _ c inhabitant) (at level 55, format "c  >|").


(** Adds a cost. *)
Definition cost_add {C} (n : nat) (m : ℂO C) : ℂO C := (n + cost m) +> res m.
Infix "⊕" := cost_add (at level 60, right associativity).

(** [f <$> m]: the result of [m] transformed by [f], at the same cost; for
    example [pot <$> m] keeps the complexity of an annotated value. *)
Definition fmap {C D} (f : C -> D) (m : ℂO C) : ℂO D := cost m +> f (res m).
Infix "<$>" := fmap (at level 55, right associativity).

(** If `cf` is the complexity of an arbitrary  term `f` of function type,
  and `cx` is the complexity of an argument term `x`, then
  `(f ⋊ cf) · (x ⋊ cx)` the application term `f x` together with its
  complexity, in a call-by-value setting.*)

Definition app {A B CA CB} (f : ℂO (ℂI (A -> B) (ℂI A CA -> ℂO CB))) (x : ℂO (ℂI A CA))
  : ℂO (ℂI B CB) :=
  let r := pot (res f) (res x) in
  cost x ⊕ (* normalise the argument *)
  cost f ⊕ (* normalise the function *)
  cost r +> (* normalise the application *)
  (val (res f) (val (res x)) ⋊ (* the value of the result of the application *)
  res r). (* the complexity of the result *)
Infix "·" := app (at level 36, left associativity).

(* Coerce the complexity of a value into that of an arbitrary term. *)
Definition ret_I {A CA} (x : ℂI A CA) : ℂO (ℂI A CA) := 0 +> x.
Coercion ret_I : ℂI >-> ℂO.

(** * The cost model

    We axiomatize a notion of complexity and will import it via the module
    system: the axioms ([CostModelAxioms]), with the complexity bounds that
    they define ([Complexities]), form [CostModelCore]. [CostModel] extends
    it with the bounds in the size of the inputs ([Bounds]). *)
Module Type CostModelAxioms.

  (** ** Representable types

      [Repr A CA]: values of type [A] have complexities of type [CA]. *)
  Parameter Repr : Type -> Type -> Type.
  Existing Class Repr.

  (** Functions between representable types are representable (with
      complexities [ℂI A CA -> ℂO CB]): given a value for an input
      and a complexity bound for it, we can get a normalisation cost and 
      a complexity bound for the output. *)
  #[global] Declare Instance Repr_arr : forall {A CA B CB},
    Repr A CA -> Repr B CB -> Repr (A -> B) (ℂI A CA -> ℂO CB).

  (** ** Complexity bounds and their order

      [has_complexity f c] states that [c] is a complexity measure for [f]. *)
  Parameter has_complexity : forall {A CA} `{Repr A CA}, A -> CA -> Prop.

(* There is an ordering on complexity measures. *)
  Parameter bound_order : forall {A CA} `{Repr A CA}, CA -> CA -> Prop.
  #[global] Declare Instance bound_order_po :
    forall {A CA} `{Repr A CA}, PreOrder (@bound_order A CA _).

  (** ** Well-formedness of complexity bounds


      [wf x c]: the complexity [c] is well-formed with respect to the value [x].
      Mostly used for now for lists, where the complexity of a list is a list
      with the same complexity.

      This could be avoided by making CA dependent on the input of type A,
      but this approach is probably simpler.

      Ideally, `wf` could be `has_complexity` but this gets in the way when
      handling recursive functions.
      
      TODO: we may want to ensure that `ComplexityBound` entails `wf`? *)
  Parameter wf : forall {A CA} `{Repr A CA}, A -> CA -> Prop.

  (** The order on the complexities of functions is pointwise, at the inputs 
    whose complexity is well-formed, and hereditarily compares costs. *)
  Parameter bound_order_arr : forall {A CA B CB} `{Repr A CA} `{Repr B CB}
    (c c' : ℂI A CA -> ℂO CB),
    (forall ca, wf (val ca) (pot ca) ->
       cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.
    

  (** TODO: this might not belong here.
      The complexity type of a representable type is inhabited. *)
  Parameter cdefault : forall {A CA} `{Repr A CA}, CA.
End CostModelAxioms.

(** * Complexity bounds

    Defined and proved from the axioms, and included in the cost model
    ([CostModelCore]) and in its instances, which do not prove anything about
    them. *)
Module Complexities (Import CM : CostModelAxioms).

(** As Forster & Künze, we record complexity types and results using
  typeclasses. *)

  (** First, we record the type of complexity bounds of a given term type.
    This will allow us to compute (via typeclass search) `CA` from `A` and
    avoid heavy type annotations. *)
  Class CType (A : Type) := { ctype : Type; crepr : Repr A ctype }.
  Arguments ctype A {_}.
  Arguments crepr A {_}.
  Global Instance repr_ctype {A CA} {R : Repr A CA} : CType A := {| ctype := CA; crepr := R |}.
  (** ** Bounds *)

  
  (** [ComplexityBound f c] states that the complexity of the object (say, function) that `f` realises is bounded by `c`.
  
     It reads "[f] is computable within (time/space/...) [c]". 
     This is unavoidable: [f] is a Rocq value, so the predicate cannot inspect its syntax: it is invariant under conversion, and, under functional extensionality (which we do not want to contradict), pointwise-equal functions are equal and have the same bounds.

    Forster & Künze's approach is extensional in the same way:
    [computableTime f T] states that some L term computes [f] within [T],
    and their lemma [computableTimeExt] transports it along extensional
    equality. *)

  Class ComplexityBound {A} {I : CType A} (f : A) (c : ctype A) : Prop :=
    { bound_below : exists c0, @bound_order A (ctype A) (crepr A) c0 c /\
                               @has_complexity A (ctype A) (crepr A) f c0 }.

  Lemma has_complexity_bound {A CA} `{Repr A CA} (f : A) (c : CA) :
    has_complexity f c -> ComplexityBound f c.
  Proof. intro Hf. constructor. exists c. split; [reflexivity | exact Hf]. Qed.

  (** Bounds are closed upwards, by transitivity of the order: the proofs
      compare the complexity found for a function with the claimed one. *)
  Global Instance ComplexityBound_mono : forall {A CA} `{Repr A CA} (f : A),
    Proper (@bound_order A CA _ ==> impl) (ComplexityBound f).
  Proof.
    intros A CA R f c c' Hc [(c0 & H0 & H)]. constructor.
    exists c0. split; [etransitivity; eassumption | exact H].
  Qed.
End Complexities.

Module Type CostModelCore := CostModelAxioms <+ Complexities.
