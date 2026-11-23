(** * Arities and pointwise equality

    [Arity T] describes [T] as a type of functions with arbitrary arity. *)

Inductive Arity : Type -> Type :=
| ar_val : forall T, Arity T
| ar_fun : forall A B, Arity B -> Arity (A -> B).

(** [pw_eq] is the pointwise equality of such functions *)
Fixpoint pw_eq {T} (ar : Arity T) : T -> T -> Prop :=
  match ar in Arity T return T -> T -> Prop with
  | ar_val T => fun x y => x = y
  | ar_fun A B ar => fun f g => forall a : A, pw_eq ar (f a) (g a)
  end.

(** [f] is a fixpoint of [F]: [f a x1 .. xn = F f a x1 .. xn] for all
    arguments, where [ar] gives the number [n] of extra arguments. *)
Definition is_fixpoint {A B} (ar : Arity B) (F : (A -> B) -> A -> B) (f : A -> B) : Prop :=
  forall a : A, pw_eq ar (f a) (F f a).
