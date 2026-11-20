(** * Inhabited types and indiscrete orders

    The two properties of the complexities of ground data ([IsGround], in
    [GroundTypes]). *)

(** Inhabited types. *)
Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
#[global] Hint Mode Inhabited ! : typeclass_instances.
#[global] Arguments populate {_} _.

#[global] Instance unit_inhabited : Inhabited unit := populate tt.

(** An indiscrete (or chaotic) order: any two elements are related. *)
Class IndiscreteOrder {A} (R : A -> A -> Prop) : Prop := indiscrete : forall x y, R x y.
