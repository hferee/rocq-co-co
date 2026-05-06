From Stdlib Require Import Classes.Morphisms Basics.

(** ** Simple types built on top of an abstract set of ground types. *)

(* TODO: move this to a module? *)

(* There is an abstract notion of "ground type" *)
Parameter is_ground_type : Type -> Prop.

(* We will be able to register ground types in typeclasses. *)
Class GroundType (A : Type) := {GTGround := is_ground_type A}.


(* Reification of simple types over ground types. *)
(* I have extended SimpleType with products so that the ComplexityType of a
  SimpleType is still a SimpleType. *)
Inductive SimpleType : Type :=
(* Ground types *)
| SGround : forall (A : Type) `{GroundType A}, SimpleType
(* Product types *)
| SProd : SimpleType -> SimpleType -> SimpleType
(* Function types *)
| SFun : SimpleType -> SimpleType -> SimpleType
(* Dependent product types *)
| SPi : (Type -> SimpleType) -> SimpleType.

(* Interpret the reification as a type. *)
Fixpoint Type_of_SimpleType t := match t with
| SGround G => G
| SFun A B => (Type_of_SimpleType A) -> (Type_of_SimpleType B)
| SProd A B => ((Type_of_SimpleType A) * (Type_of_SimpleType B))%type
| SPi F => forall (A : Type), Type_of_SimpleType (F A)
end.

Coercion Type_of_SimpleType: SimpleType >-> Sortclass.

Coercion SGround: GroundType >-> SimpleType.

(* Conversely, a tactic to derive SimpleType from a type *)
Ltac simpletype A := match A with
| ?a -> ?b => exact (SFun ltac:(simpletype a) ltac:(simpletype b))
| (?a * ?b)%type => exact (SProd ltac:(simpletype a) ltac:(simpletype b))
| Type_of_SimpleType ?a => exact a
| ?a => exact (SGround a) (* This should succeed if ?a is registered in GroundType *)
| ?a => exact a
end.

Notation "'$' t" := (ltac:((simpletype t))) (at level 5).

Notation "A ⇝ B" := (SFun A B) (at level 80, right associativity).

(* Extensional equality over simple types *)
Definition ext_eq {T : SimpleType} : T -> T -> Prop.
Proof.
induction T as [G | X fX Y fY | A B P IHT1 | F HF]; intros x y.
- exact (x = y).
- destruct x as [x1 x2]; destruct y as [y1 y2].
  exact ((fX x1 y1) /\ fY x2 y2).
- exact (forall e, IHT1 (x e) (y e)).
- exact (forall A, HF A (x A) (y A)).
Defined.

Infix "=ext" := ext_eq (at level 50, no associativity).

Global Instance reflexive_ext_eq {A} : Reflexive (@ext_eq A).
Proof.
induction A; intros x; simpl; intuition (auto with *).
destruct x. intuition (auto with *).
Qed.

Global Instance symmetric_ext_eq {A} : Symmetric (@ext_eq A).
Proof.
induction A; intros x y; simpl; intuition.
destruct x; destruct y; intuition (auto with *).
now symmetry.
Qed.
