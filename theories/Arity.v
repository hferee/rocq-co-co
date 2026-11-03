(** * Fixpoints of functionals, pointwise in all arguments

    [Arity T] describes [T] as a type of functions with some arguments, and
    [ext_eq] is the pointwise equality of such functions. They are used to
    state the unfolding equations of recursive functions ([FixCostModel]). *)

Inductive Arity : Type -> Type :=
| ar_val : forall T, Arity T
| ar_fun : forall A B, Arity B -> Arity (A -> B).

Fixpoint ext_eq {T} (ar : Arity T) : T -> T -> Prop :=
  match ar in Arity T return T -> T -> Prop with
  | ar_val T => fun x y => x = y
  | ar_fun A B ar => fun f g => forall a : A, ext_eq ar (f a) (g a)
  end.

(** [f] is a fixpoint of [F]: [f a x1 .. xn = F f a x1 .. xn] for all
    arguments, where [ar] gives the number [n] of extra arguments. *)
Definition is_fixpoint {A B} (ar : Arity B) (F : (A -> B) -> A -> B) (f : A -> B) : Prop :=
  forall a : A, ext_eq ar (f a) (F f a).
