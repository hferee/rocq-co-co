From Complexity Require Export SimpleTypes.
From Stdlib Require Import Classes.Morphisms Program.Basics.
From Equations Require Import Equations.

(* Type of the complexity bounds for elements of a simple type. *)
(* This is inspired by Forster & Künze with two main changed:
   - the cost of a term of ground type is the cost of normalizing it,
     while they only consider the cost of normal forms ;
   - Every element is packaged with a normalisation cost and the
     complexity of its normal form. *)

(* Monad(?) to annotate inputs (in normal form) with their complexity bounds *)
(* In theory, cost could be something else than nat. *)
Record ℂI (A : Type) (CA : Type) := { val : A; icomp : CA }.
(* TODO: find better names, especially icomp *)
(* TODO: Not sure that the use of a record improves things, especially for
  ground types. Maybe do something like ℂO *)

Infix "⋊" := (Build_ℂI _ _) (at level 40).

Global Arguments val {_} {_}.
Global Arguments icomp {_} {_}.

(* Type builder meant to group the normalisation cost of a term together
  with its complexity bound. *)
Definition ℂO (t : SimpleType) (CA : Type) : Type :=
match t with
| SGround A => nat
| _ => nat * CA
end.

(* Annotate a complexity bound with a cost *)
Definition ℂO_pair {t : SimpleType} {CA : Type} (n : nat) (c : CA) : ℂO t CA.
Proof. destruct t. 1: exact n. all: exact (n, c). Defined.
Infix "⋉" := ℂO_pair (at level 40).

(* (* The type of complexity bounds for normal forms of a given simple type *)
Fixpoint ℂT (t : SimpleType) : Type := match t with
| SGround A => unit
| SProd A B => ℂT A * ℂT B
| SFun A B => ℂI A (ℂT A) -> ℂO B (ℂT B)
| SPi F => forall (A : Type), ℂT (F A)
end. *)

(* Immediate/ normalisation cost of an output *)
Definition cost {t CA} (b : ℂO t CA) : nat.
Proof. destruct t. 1: exact b. all: exact (fst b). Defined.

(* (* Complexity of an output *)
Definition ocomp {t} (b : ℂO t (ℂT t)) : ℂT t.
Proof. destruct t. 1: exact tt. all: exact (snd b). Defined. *)


(* Global Arguments ℂT !t : simpl nomatch. (* TODO: this doesn't work, it's still unfolded *) *)

(* Ordering on complexity bounds *)
(* Equations ℂT_order t (b1 b2 : ℂT t) : Prop :=
ℂT_order (SGround A) _ _ => True;
ℂT_order (SProd A B) b1 b2 =>
  ℂT_order A (fst b1) (fst b2) /\ ℂT_order B (snd b1) (snd b2);
ℂT_order (SFun A B) b1 b2 => forall ca, let b1' := b1 ca in let b2' := b2 ca in
  cost b1' <= cost b2' /\ ℂT_order B (ocomp b1') (ocomp b2');
ℂT_order (SPi F) b1 b2 => forall A, ℂT_order (F A) (b1 A) (b2 A).

Global Arguments ℂT_order {t} b1 b2.
Global Transparent ℂT_order. *)

(* TODO: all this mess is to hopefully obtain nice complexity bounds
  - that are what we hope for first order functions ;
  - that handle multiple arguments ;
  - more generally handle higher-order functions ;
  - The complexity of polymorphic functions can be expressed polymorphically. *)


(* Global Instance ℂT_order_refl t : Reflexive (@ℂT_order t).
Proof. induction t; intro x; autorewrite with ℂT_order; auto with *. Qed.

Global Instance ℂT_order_trans t : Transitive (@ℂT_order t).
Proof.
induction t; intros x y z.
- trivial.
- split; auto with *.
- autorewrite with ℂT_order.
  fold ℂT. (* TODO: how do I prevent the unfolding of ℂT? *)
  split; auto with *.
  transitivity (cost (y ca)); auto with *.
- autorewrite with ℂT_order. eauto with *.
Qed. *)

(* Some execution models can be equipped with a notion of complexity *)
Module Type CostModel.

  (* An abstract notion of cost. This allows for multiple notions of cost
    (time, space, function calls, etc. *)

  (* I'm fixing the type of complexity measures to nat here for now. *)

  (* The complexity of an abstract term defined as a relation. *)
  (* We may require that it is monotone in the future *)
  Parameter complexity_type : Type -> Type -> Prop.
  Parameter has_complexity: forall {A B : Type}, A -> B -> Prop.

 (* Complexity is a monotone property *)
  Parameter has_complexity_ext_eq: forall {A},
    Proper ((ext_eq) ==> (ℂT_order) ==> impl) (@has_complexity A).
  Global Existing Instance has_complexity_ext_eq.

  Infix "has_complexity!" := has_complexity (at level 40).

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  Class ComplexityBound A (f : Type_of_SimpleType A) c := {CB : has_complexity f c}.

  Global Instance ComplexityBound_proper {A}:
    Proper ((ext_eq) ==> (ℂT_order) ==> (impl)) (ComplexityBound A).
  Proof. intros ??????[?]. constructor. eapply has_complexity_ext_eq; eauto. Qed.

  (* Useful functions to express complexity bounds *)
  (* Cost of applying a function of (input) complexity cg to an argument
    of (input) complexity ca. *)
  Definition cost_apply {A B} (cg : @ℂI (SFun A B) (ℂT (SFun A B)))
    (ca : @ℂI A (ℂT A)) : nat := cost (icomp cg ca).

  (* Input complexity of an application. *)
  (* TODO: find better name *)
  Definition ℂI_apply {A B} (cg : @ℂI (SFun A B) (ℂT (SFun A B))) (ca : @ℂI A (ℂT A))
    : ℂI B (ℂT B) :=
    val cg (val ca) ⋊ ocomp (icomp cg ca).

  (* Adds a normalisation cost to a complexity bound *)
  Definition cost_add {t} (n : nat) (b : ℂO t (ℂT t)) : ℂO t (ℂT t).
  Proof. destruct t. 1: exact (n + b). all: exact (n + fst b, snd b). Defined.

  Global Infix "⊕" := cost_add (at level 60, right associativity).

  (* Complexity of producing a value *)
  Definition ovalue {t} (v : ℂT t) : ℂO t (ℂT t).
  Proof. destruct t. 1: exact 1. all: exact (1, v). (* 1? could be 0 *) Defined.
End CostModel.

(* A basic example of a cost model for call-by-value time complexity *)
Module Type BasicTimeCostModel (Import CM : CostModel).

  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat, 
  or make mistakes anymore *)

  (* Identity on ground types *)
  (* TODO: compare with from coq-library-complexity. *)
  Parameter id0_complexity : forall {A} `{GroundType A},
    ComplexityBound $(A -> A) (@id A) (fun a => 1).
  Existing Instance id0_complexity.

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  Parameter id_complexity : forall {A B},
    ComplexityBound $(SFun (SFun A B) (SFun A B)) (@id (A -> B))
      (fun cf => (1, icomp cf)).
  Existing Instance id_complexity.

  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B : SimpleType} {v : A} {f cv cf},
    ComplexityBound A v cv ->
    ComplexityBound $(A -> B) f cf ->
    ComplexityBound B (f v) (ocomp (cf (v ⋊ cv))).

    (* TODO : notation for putting back v and cv together *)

  (* Unary composition *)
  (* It produces a value whose complexity is obtained by composing the complexity
     of the three inputs ; the normalisation cost is obtained by two successive
     applications. *)
  Parameter comp1_complexity : forall {A B C : SimpleType},
  ComplexityBound $((B -> C) -> (A -> B) -> (A -> C)) compose
    (fun cf => (1, fun cg => (1, fun ca =>
      1 + cost_apply cg ca + cost_apply cf (ℂI_apply cg ca)
      ⊕ icomp cf (ℂI_apply cg ca)))).
  Existing Instance comp1_complexity.

  (* More convenient: the instantiation direct application of compose.
    TODO: do we need both? *)
  Parameter compose_complexity : forall {A B C : SimpleType} f cf g cg,
  ComplexityBound $(B -> C) f cf ->
  ComplexityBound $(A -> B) g cg ->
  ComplexityBound $(A -> C) (compose f g)
    (fun ca =>
      cost (cg ca) ⊕ cf (ℂI_apply (g ⋊ cg) ca)).
  Existing Instance compose_complexity.

End BasicTimeCostModel.
