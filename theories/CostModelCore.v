From Stdlib Require Export Classes.Morphisms Classes.RelationClasses Program.Basics.

(** * Complexities

    For function types, a complexity is a function taking as input an input
    of the function together with its complexity ([ℂI]), and returning a
    cost together with the complexity of the output ([ℂO]). This is Forster
    & Künze's [timeComplexity] (which also receives the input value), with
    records instead of curried arguments and pairs. The output value is not
    part of a complexity, as it is determined by the function.

    In the terms of recurrence extraction (Danner, Licata & Ramyaa,
    Denotational cost semantics for functional languages with inductive
    types, ICFP 2015), the complexity of a value is its potential, and [ℂO]
    is the writer monad of costs. *)

(** A value with its complexity (potential). *)
#[projections(primitive)]
Record ℂI (A CA : Type) := { val : A; pot : CA }.
Infix "⋊" := (Build_ℂI _ _) (at level 40).
Arguments val {_ _}.
Arguments pot {_ _}.

(** A cost with a result: the writer monad of costs. *)
#[projections(primitive)]
Record ℂO (C : Type) := { cost : nat; res : C }.
Infix "⋉" := (Build_ℂO _) (at level 40).
Arguments cost {_}.
Arguments res {_}.

Definition ret {C} (c : C) : ℂO C := 0 ⋉ c.

(** Adds a cost. *)
Definition cost_add {C} (n : nat) (m : ℂO C) : ℂO C := (n + cost m) ⋉ res m.
Infix "⊕" := cost_add (at level 60, right associativity).

Definition bind {C D} (m : ℂO C) (k : C -> ℂO D) : ℂO D := cost m ⊕ k (res m).
Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity).

Definition fmap {C D} (f : C -> D) (m : ℂO C) : ℂO D := cost m ⋉ f (res m).
Infix "<$>" := fmap (at level 55, right associativity).

(** [f · x] applies a function to an argument, both computed and annotated
    with their complexities: its cost is the sum of the costs of the
    argument, of the function and of the application, and its result keeps
    the value, to be passed to the next complexity. Annotated values are
    computations of cost [0] (coercion [ret_I]). The complexity of
    [compose f g] is thus [fun a => 1 ⊕ pot <$> (f ⋊ cf) · ((g ⋊ cg) · a)]:
    it reads as the term [f (g a)]. *)
Definition app {A B CA CB} (f : ℂO (ℂI (A -> B) (ℂI A CA -> ℂO CB))) (x : ℂO (ℂI A CA))
  : ℂO (ℂI B CB) :=
  let r := pot (res f) (res x) in
  cost x ⊕ cost f ⊕ cost r ⋉ (val (res f) (val (res x)) ⋊ res r).
Infix "·" := app (at level 36, left associativity).

Definition ret_I {A CA} (x : ℂI A CA) : ℂO (ℂI A CA) := ret x.
Coercion ret_I : ℂI >-> ℂO.

(** Destruct the complexities of the inputs of ground type: [c : ℂI A unit]
    becomes the value of the input, still named [c]. *)
Ltac destr_inputs :=
  repeat match goal with
  | c : ℂI _ unit |- _ => let v := fresh "v" in destruct c as [v []]; rename v into c
  end.

(** * Sizes

    [Size A]: the sizes of the values of [A], those of their representations
    in a machine model. The models of the datatypes give the sizes of ground
    data, with one axiom for each constructor: a value is larger than its
    arguments together. A size is a function of the value, as the
    representation of ground data is: a relation, as [has_complexity], would
    only be needed for values with several representations, such as
    functions. *)
Class Size (A : Type) := size : A -> nat.

(** * Complexity types

    [ctype A]: the type of the complexities of the values of [A], computed
    from their representation ([repr_ctype] in [CostModelCore]). A bound
    [ComplexityBound f c] has the type [ctype A]: Rocq resolves the
    representation of [A] when it checks [c] against it, so that the
    binders of [c] need no type annotation. A record, not a definitional
    class, so that [ctype A] is stuck until the instance is found. *)
Class CType (A : Type) := { ctype : Type }.
Arguments ctype A {_}.

(** * The cost model

    We axiomatize a notion of complexity and will import it via the module
    system. [CostModel] extends this core with the bounds in the size of the
    inputs ([Bounds]). *)
Module Type CostModelCore.

  (** ** Representable types

      [Repr A CA]: values of type [A] have complexities of type [CA]. The
      axioms only speak about representable types: in a machine model, a
      value is represented through its type (an encoding of ground data, a
      realiser of a function), which cannot be done for an arbitrary Rocq
      type. Functions between representable types are representable (with
      complexities [ℂI A CA -> ℂO CB]); the models of the datatypes declare
      their types representable, ground data having complexity [unit].
      Polymorphic results are proved for representable type parameters, as
      Forster & Künze do with sections. *)
  Parameter Repr : Type -> Type -> Type.
  Existing Class Repr.

  (** [Ground A]: [A] is a ground type, whose values have complexity [unit]
      (all the information is in the value). It is the class [Repr A unit]
      itself, so goals display it. *)
  Abbreviation Ground A := (Repr A unit).

  #[global] Declare Instance Repr_unit : Ground unit.

  #[global] Declare Instance Size_unit : Size unit.
  Parameter size_tt : 0 < size tt.

  #[global] Declare Instance Repr_arr : forall {A CA B CB}, Repr A CA -> Repr B CB ->
    Repr (A -> B) (ℂI A CA -> ℂO CB).

  (** ** Complexities and their order *)
  Parameter has_complexity : forall {A CA} `{Repr A CA}, A -> CA -> Prop.

  Parameter bound_order : forall {A CA} `{Repr A CA}, CA -> CA -> Prop.
  #[global] Declare Instance bound_order_po :
    forall {A CA} `{Repr A CA}, PreOrder (@bound_order A CA _).

  #[global] Declare Instance has_complexity_ext_eq : forall {A CA} `{Repr A CA} (f : A),
    Proper (bound_order ==> impl) (has_complexity f).

  (** The order on the complexities of functions is pointwise, and compares
      costs; complexities of ground data carry no information. *)
  Parameter bound_order_arr : forall {A CA B CB} `{Repr A CA} `{Repr B CB}
    (c c' : ℂI A CA -> ℂO CB),
    (forall ca, cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.

  Parameter bound_order_ground : forall {A} `{Ground A} (c c' : unit), bound_order c c'.

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  (** [ComplexityBound f c] is a property of the function [f], not of a
    program: it reads "[f] is computable within [c]". This is unavoidable.
    [f] is a Rocq value, so the predicate cannot inspect its syntax: it is
    invariant under conversion, and, under functional extensionality (which
    we do not want to contradict), pointwise-equal functions are equal and
    have the same bounds. For instance, [Nat.iter (2 ^ n) (fun x => x) n]
    has the bound of the identity (see [Examples]). [fix_complexity]
    ([FixCostModel]) makes this extensionality provable without assuming
    functional extensionality.

    Forster & Künze's approach is extensional in the same way:
    [computableTime f T] states that some L term computes [f] within [T],
    and their lemma [computableTimeExt] transports it along extensional
    equality. *)
  (** The complexity type of a representable type ([CType]). *)
  Global Instance repr_ctype {A CA} `{Repr A CA} : CType A := {| ctype := CA |}.

  Class ComplexityBound {A} {I : CType A} {R : Repr A (ctype A)} (f : A) (c : ctype A) :=
    {CB : has_complexity f c}.

  Global Instance ComplexityBound_ext_eq : forall {A CA} `{Repr A CA} (f : A),
    Proper (@bound_order A CA _ ==> impl) (ComplexityBound f).
  Proof. intros A CA R f c c' Hc [H]. constructor. eapply has_complexity_ext_eq; eauto. Qed.

  (** Replaces the complexity bound with an evar. The complexity bound goal
      will eventually need to be taken from the shelf. *)
  Ltac capply := eapply ComplexityBound_ext_eq; [shelve|].

  (** Decompose [bound_order] goals into inequalities between costs. The
      arguments of functions are named as in the right-hand side (usually
      the claimed bound). *)
  Ltac bo_split :=
    repeat match goal with
    | |- @bound_order _ (_ -> _) _ _ ?c =>
        let c := eval hnf in c in
        apply bound_order_arr;
        lazymatch c with
        | fun x => _ => let y := fresh x in intro y
        | _ => intro
        end;
        split
    | |- @bound_order _ unit _ _ _ => apply bound_order_ground
    end.
End CostModelCore.
