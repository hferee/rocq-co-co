(** The costs are numbers: the cost model exports the arithmetic of the
    standard library, with [lia] and [nia], which close the goals left by
    its tactics. *)
From Stdlib Require Export Classes.Morphisms Classes.RelationClasses Program.Basics Arith Lia.

(** * Complexity model

    Notions that should be common to all complexity notions.
    In particular, this could be instantiated with both space or time
    complexity.

    For function types, a complexity is a function taking as input an input
    of the function together with its complexity ([ℂI]), and returning a
    cost together with the complexity of the output ([ℂO]). This is Forster
    & Künze's [timeComplexity] (which also receives the input value), with
    records instead of curried arguments and pairs. The output value is not
    part of a complexity, as it is determined by the function.

*)

(** A value with its complexity (potential). *)
#[projections(primitive)]
Record ℂI (A CA : Type) := { val : A; pot : CA }.
Infix "⋊" := (Build_ℂI _ _) (at level 40).
Arguments val {_ _}.
Arguments pot {_ _}.

(** A cost with a result: the writer monad of costs. *)
#[projections(primitive)]
Record ℂO (C : Type) := { cost : nat; res : C }.
(** [c +> r]: the cost [c], then the result [r], whose costs come after
    [c] (they are added to it when [r] is used). Below [+] and [*], so that
    a cost needs no parentheses: [fun cn => 4 +> fun cm => 22 * val cn + 6 >|]. *)
Notation "c +> r" := (Build_ℂO _ c r) (at level 55, right associativity).
(** Inhabited types, with an element: the class [Inhabited] of stdpp (with
    the same names), on which [>|] relies. The search waits for the type
    ([Hint Mode]), so that [>|] finds the instance from the type of the
    result. The instances are declared with the types: [unit] below, lists
    in [TimeLists], options, pairs and sums in [TimeDatatypes]. *)
Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
#[global] Hint Mode Inhabited ! : typeclass_instances.
#[global] Arguments populate {_} _.

(** [unit], the complexity of numbers, booleans, ... *)
#[global] Instance unit_inhabited : Inhabited unit := populate tt.

(** An indiscrete (or chaotic) order: any two elements are related. The
    complexities of ground data have an indiscrete order ([IsGround]). *)
Class IndiscreteOrder {A} (R : A -> A -> Prop) : Prop := indiscrete : forall x y, R x y.

(** [c >|]: the cost [c], and nothing after it: [Build_ℂO _ c inhabitant],
    the end of a bound whose result is ground (a number, a boolean, a list
    of numbers, ...). Its complexity is any one ([inhabitant]: [tt] for
    [unit], the empty list for the lists of ground data, ...), any two
    complexities of ground data being related ([IsGround]). Like [+>], it
    takes the whole cost on its left: [22 * val cn + 6 >|]. Being declared
    after [+>], it is the one Rocq prints. It is at level 55, not at the
    usual level 1 of a postfix notation, so that it takes the whole
    cost. *)
#[warnings="-postfix-notation-not-level-1"]
Notation "c >|" := (Build_ℂO _ c inhabitant) (at level 55, format "c  >|").
Arguments cost {_}.
Arguments res {_}.

Definition ret {C} (c : C) : ℂO C := 0 +> c.

(** Adds a cost. *)
Definition cost_add {C} (n : nat) (m : ℂO C) : ℂO C := (n + cost m) +> res m.
Infix "⊕" := cost_add (at level 60, right associativity).

Definition bind {C D} (m : ℂO C) (k : C -> ℂO D) : ℂO D := cost m ⊕ k (res m).
Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity).

Definition fmap {C D} (f : C -> D) (m : ℂO C) : ℂO D := cost m +> f (res m).
Infix "<$>" := fmap (at level 55, right associativity).

(** [f · x] applies a function to an argument, both computed and annotated
    with their complexities: its cost is the sum of the costs of the
    argument, of the function and of the application, and its result keeps
    the value, to be passed to the next complexity. Annotated values are
    computations of cost [0] (coercion [ret_I]). The complexity of
    [compose f g] is thus [fun x => c ⊕ pot <$> (f ⋊ cf) · ((g ⋊ cg) · x)],
    where [c] is the cost of the composition itself: it reads as the term
    [f (g x)]. *)
Definition app {A B CA CB} (f : ℂO (ℂI (A -> B) (ℂI A CA -> ℂO CB))) (x : ℂO (ℂI A CA))
  : ℂO (ℂI B CB) :=
  let r := pot (res f) (res x) in
  cost x ⊕ cost f ⊕ cost r +> (val (res f) (val (res x)) ⋊ res r).
Infix "·" := app (at level 36, left associativity).

Definition ret_I {A CA} (x : ℂI A CA) : ℂO (ℂI A CA) := ret x.
Coercion ret_I : ℂI >-> ℂO.

(** * Constants

    The costs of the primitives of a cost model are constants, declared as
    parameters by the module types of the model and fixed by each model
    ([with Definition], see [TimeCostModel]). Each module type registers its
    constants in [costs], so that the tactics unfold them where they are
    fixed: [lia] treats an unfolded constant as an atom. *)
Create HintDb costs.

(** Destruct the complexities of the inputs of ground type: [c : ℂI A unit]
    becomes the value of the input, still named [c]. *)
(** The complexity types of ground data: [unit], and the lists, pairs,
    options and sums of them. *)
Ltac is_ground_ctype C :=
  lazymatch C with
  | unit => idtac
  | list ?C1 => is_ground_ctype C1
  | prod ?C1 ?C2 => is_ground_ctype C1; is_ground_ctype C2
  | option ?C1 => is_ground_ctype C1
  | sum ?C1 ?C2 => is_ground_ctype C1; is_ground_ctype C2
  end.

(** The inputs of ground data are replaced by their values (their
    complexities carry no information): the value keeps the name of the
    input. *)
Ltac destr_inputs :=
  repeat match goal with
  | c : ℂI _ unit |- _ => let v := fresh "v" in destruct c as [v []]; rename v into c
  | c : ℂI _ ?C |- _ =>
      is_ground_ctype C;
      let v := fresh "v" in let p := fresh "p" in destruct c as [v p]; rename v into c
  end.

(** * Sizes

    As complexity bounds are usually expressed in terms of the size of the
    inputs, we will record in a typeclass the size function of given types.
    For now, this is only relevant for ground types ; but we will later 
    define and used second or higher-order sizes.

    The size of a value of a datatype is the length of its binary
    encoding, its number of constructors: one bit per constructor for the
    types with two constructors ([bool], [nat], [option], [list], [sum]),
    the binary digits of a [positive] (with one more for the sign or the
    zero of [N] and [Z]), and one for each pair. The models of the
    datatypes state it as equations ([size_S], [size_cons], ...). *)
Class Size (A : Type) := size : A -> nat.
(** [#|x|]: the size of [x]. (The bar of [|x|] would also open a term:
    [#|] is a distinct token, as in mathcomp.) *)
Notation "#| x |" := (size x) (at level 0, x at level 99, format "#| x |").

(** * Complexity types

    [ctype A]: the type of the complexities of the values of [A], computed
    from their representation ([repr_ctype] in [Complexities]). A bound
    [ComplexityBound f c] has the type [ctype A]: Rocq resolves the
    representation of [A] when it checks [c] against it, so that the
    binders of [c] need no type annotation. A record, not a definitional
    class, so that [ctype A] is stuck until the instance is found. *)
Class CType (A : Type) := { ctype : Type }.
Arguments ctype A {_}.

(** * The cost model

    We axiomatize a notion of complexity and will import it via the module
    system: the axioms ([CostModelAxioms]), with the complexity bounds that
    they define ([Complexities]), form [CostModelCore]. [CostModel] extends
    it with the bounds in the size of the inputs ([Bounds]). *)
Module Type CostModelAxioms.

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
  Parameter size_tt : size tt = 1.

  #[global] Declare Instance Repr_arr : forall {A CA B CB}, Repr A CA -> Repr B CB ->
    Repr (A -> B) (ℂI A CA -> ℂO CB).

  (** ** Complexities and their order

      [has_complexity f c]: [c] is a complexity of [f]. It need not be
      monotone in [c]: the bounds ([ComplexityBound]) are closed upwards by
      definition. *)
  (* The relation between terms and complexity bounds. *)
  Parameter has_complexity : forall {A CA} `{Repr A CA}, A -> CA -> Prop.

(* The complexity relation can be closed downards by an ordering. *)
  Parameter bound_order : forall {A CA} `{Repr A CA}, CA -> CA -> Prop.
  #[global] Declare Instance bound_order_po :
    forall {A CA} `{Repr A CA}, PreOrder (@bound_order A CA _).

  (** A complexity of each representable type: the one that the
      representations of data use for a missing complexity (an element of a
      list longer than its complexities, ...). *)
  Parameter cdefault : forall {A CA} `{Repr A CA}, CA.

  (** The order on the complexities of functions is pointwise, and compares
      costs. *)
  Parameter bound_order_arr : forall {A CA B CB} `{Repr A CA} `{Repr B CB}
    (c c' : ℂI A CA -> ℂO CB),
    (forall ca, cost (c ca) <= cost (c' ca) /\ bound_order (res (c ca)) (res (c' ca))) ->
    bound_order c c'.
End CostModelAxioms.

(** * Complexity bounds

    Defined and proved from the axioms, and included in the cost model
    ([CostModelCore]) and in its instances, which do not prove anything about
    them. *)
Module Complexities (Import CM : CostModelAxioms).

  (** ** The order

      Complexities of ground data carry no information: any two are
      related, by reflexivity. The lemma applies to any terms of type
      [unit], such as [res (c ca)], which [reflexivity] does not relate to
      [tt] (there is no eta-rule for [unit]). *)
  Lemma bound_order_ground {A} `{Ground A} (c c' : unit) : bound_order c c'.
  Proof. destruct c, c'. reflexivity. Qed.

  (** Ground data, in general: their complexities carry no information. Their
      type is inhabited, and their order is indiscrete: any two are related.
      The data of complexity [unit] are ground; so are the lists, options,
      pairs and sums of ground data ([TimeLists], [TimeDatatypes]). The
      bounds whose result is ground end with [>|]: the complexity of the
      result is then any one ([inhabitant]). *)
  Class IsGround {A CA} (R : Repr A CA) : Type := {
    ground_inhabited :: Inhabited CA;
    ground_indiscrete :: IndiscreteOrder (@bound_order A CA R) }.

  Definition ground_order {A CA} {R : Repr A CA} {G : IsGround R} (c c' : CA) : bound_order c c' :=
    indiscrete c c'.

  Global Instance unit_ground {A} (R : Ground A) : IsGround R :=
    {| ground_inhabited := unit_inhabited; ground_indiscrete := @bound_order_ground A R |}.

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
    | |- @bound_order _ _ _ _ _ => solve [apply ground_order]
    end.

  (** ** Bounds *)

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  (** [ComplexityBound f c] is a property of the function [f], not of a
    program: it reads "[f] is computable within [c]". This is unavoidable.
    [f] is a Rocq value, so the predicate cannot inspect its syntax: it is
    invariant under conversion, and, under functional extensionality (which
    we do not want to contradict), pointwise-equal functions are equal and
    have the same bounds. For instance, [Nat.iter (2 ^ n) (fun x => x) n]
    has the bound of the identity (see [Examples]). [fix_complexity]
    ([TimeFix]) makes this extensionality provable without assuming
    functional extensionality.

    Forster & Künze's approach is extensional in the same way:
    [computableTime f T] states that some L term computes [f] within [T],
    and their lemma [computableTimeExt] transports it along extensional
    equality. *)

  (** The complexity type of a representable type ([CType]). *)
  Global Instance repr_ctype {A CA} `{Repr A CA} : CType A := {| ctype := CA |}.

  (** "Within [c]": [f] has a complexity below [c]. *)
  Class ComplexityBound {A} {I : CType A} {R : Repr A (ctype A)} (f : A) (c : ctype A)
    : Prop :=
    { bound_below : exists c0, bound_order c0 c /\ has_complexity f c0 }.

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

  (** Replaces the complexity bound with an evar. The complexity bound goal
      will eventually need to be taken from the shelf. *)
  Ltac capply := eapply ComplexityBound_mono; [shelve|].
End Complexities.

Module Type CostModelCore := CostModelAxioms <+ Complexities.
