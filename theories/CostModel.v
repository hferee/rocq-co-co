From Complexity Require Export SimpleTypes.
From Stdlib Require Import Classes.Morphisms Program.Basics.
From Equations Require Import Equations.

(* Type of the complexity bounds for elements of a simple type. *)
(* This is inspired by Forster & Künze with two main changed:
   - the cost of a term of ground type is the cost of normalizing it,
     while they only consider the cost of normal forms ;
   - Every element is packaged with a normalisation cost and the
     complexity of its normal form. *)

  (* Types will extensively be interpreted as some simple types, typically
    using Scott Encodings. *)
  Class InterpretableType (t : Type) := {
    TI : SimpleType;
    enc : t -> TI;
    dec : TI -> t;
    }.

  Definition SimpleType_of t `{InterpretableType t} := TI.
  Coercion SimpleType_of : Sortclass >-> Funclass.
  Notation "§ A" := (SimpleType_of A) (at level 5).

   Global Instance InterpretableFun t1 t2
   `{InterpretableType t1} `{InterpretableType t2} : InterpretableType (t1 -> t2) := {
    TI := SFun §t1 §t2;
    enc := fun f x => enc (f (dec x));
    dec := fun f x => dec (f (enc x));
    }.

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

(* The type of complexity bounds for normal forms of a given simple type *)
Fixpoint ℂT (t : SimpleType) : Type := match t with
| SGround A => unit
| SProd A B => ℂT A * ℂT B
| SFun A B => ℂI A (ℂT A) -> ℂO B (ℂT B)
| SPi F => forall (A : SimpleType), ℂT (F A)
end.

(* Immediate/ normalisation cost of an output *)
Definition cost {t CA} (b : ℂO t CA) : nat.
Proof. destruct t. 1: exact b. all: exact (fst b). Defined.

(* Complexity of an output *)
Definition ocomp {t} (b : ℂO t (ℂT t)) : ℂT t.
Proof. destruct t. 1: exact tt. all: exact (snd b). Defined.


Global Arguments ℂT !t : simpl nomatch. (* TODO: this doesn't work, it's still unfolded *)

(* Ordering on complexity bounds *)
Equations ℂT_order t (b1 b2 : ℂT t) : Prop :=
ℂT_order (SGround A) _ _ => True;
ℂT_order (SProd A B) b1 b2 =>
  ℂT_order A (fst b1) (fst b2) /\ ℂT_order B (snd b1) (snd b2);
ℂT_order (SFun A B) b1 b2 => forall ca, let b1' := b1 ca in let b2' := b2 ca in
  cost b1' <= cost b2' /\ ℂT_order B (ocomp b1') (ocomp b2');
ℂT_order (SPi F) b1 b2 => forall (A : SimpleType), ℂT_order (F A) (b1 A) (b2 A).

Global Arguments ℂT_order {t} b1 b2.
Global Transparent ℂT_order.

(* TODO: all this mess is to hopefully obtain nice complexity bounds
  - that are what we hope for first order functions ;
  - that handle multiple arguments ;
  - more generally handle higher-order functions ;
  - The complexity of polymorphic functions can be expressed polymorphically. *)


Global Instance ℂT_order_refl t : Reflexive (@ℂT_order t).
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
Qed.

(* Some execution models can be equipped with a notion of complexity *)
Module Type CostModel.
  (* An abstract notion of cost. This allows for multiple notions of cost
    (time, space, function calls, etc. *)

  (* I'm fixing the type of complexity measures to nat here for now. *)

  (* The complexity of an abstract term defined as a relation. *)
  (* We may require that it is monotone in the future *)
  Parameter has_complexity: forall {t} `{InterpretableType t}, t -> ℂT (§ t) -> Prop.

  Definition ext_eq' {t} `{InterpretableType t} a b := ext_eq (enc a) (enc b).
Infix "=e" := ext_eq' (at level 50, no associativity).

 (* Complexity is a monotone property *)
  Parameter has_complexity_ext_eq: forall {A : Type} {IA: InterpretableType A},
    Proper ((ext_eq') ==> (ℂT_order) ==> impl) has_complexity.
  Global Existing Instance has_complexity_ext_eq.

  Infix "has_complexity!" := has_complexity (at level 40).

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  Class ComplexityBound {t} `{InterpretableType t} (f : t) c := {CB : has_complexity f c}.

  Global Instance ComplexityBound_proper {t} `{InterpretableType t}:
    Proper ((ext_eq') ==> (ℂT_order) ==> (impl)) ComplexityBound.
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

  (* Complexity of the Identity.
    Note that we can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)

  Parameter id_complexity : forall {A} `{InterpretableType A},
    ComplexityBound (@id A) (fun a => 1 ⋉ icomp a).
  Existing Instance id_complexity.

(*   (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B : SimpleType} {v : A} {f cv cf},
    ComplexityBound A v cv ->
    ComplexityBound $(A -> B) f cf ->
    ComplexityBound B (f v) (ocomp (cf (v ⋊ cv))).
 *)

  (* Unary composition *)
  (* It produces a value whose complexity is obtained by composing the complexity
     of the three inputs ; the normalisation cost is obtained by two successive
     applications. *)
  Parameter comp1_complexity : forall {A B C}
  `{InterpretableType A, InterpretableType B, InterpretableType C},
  ComplexityBound (@compose A B C)
    (fun cf => (1, fun cg => (1, fun ca =>
      1 + cost_apply cg ca + cost_apply cf (ℂI_apply cg ca)
      ⊕ icomp cf (ℂI_apply cg ca)))).
  Existing Instance comp1_complexity.

  (* More convenient: the instantiation direct application of compose.
    TODO: do we need both? *)
  Program Definition compose_complexity : forall {A B C}
  `{InterpretableType A, InterpretableType B, InterpretableType C}
  (f : B -> C) cf (g : A -> B) cg,
  let _ : InterpretableType (A -> B) := _ in
  let _ : InterpretableType (B -> C) := _ in
  let _ : InterpretableType (A -> C) := _ in
  ComplexityBound f cf ->
  ComplexityBound g cg ->
  ComplexityBound (@compose A B C f g : A -> C)
    (fun ca =>
      (* cost (cg ca) ⊕  *) cf (ℂI_apply _ ca)).
  Existing Instance compose_complexity.

End BasicTimeCostModel.
