(** * Combinators for the analysis of lambda-terms

    This file only contains (transparent) definitions; their complexities are
    axiomatised in [CombinatorCostModel]. The tactics of [Compile] rewrite a term into a
    *convertible* term built from these combinators, whose complexity can then
    be found by plain first-order typeclass search. *)

From Stdlib Require Import Program.Basics.

(** ** Bracket abstraction

    [Kc], [Ic], [compose] (B), [Sc] and [Cc] are the usual combinators. *)
Definition Kc {A B : Type} (a : A) : B -> A := fun _ => a.
Definition Ic {A : Type} : A -> A := fun a => a.
Definition Sc {X A B : Type} (f : X -> A -> B) (g : X -> A) : X -> B := fun x => f x (g x).
Definition Cc {X A B : Type} (f : X -> A -> B) (a : A) : X -> B := fun x => f x a.

(** Under call-by-value, abstracting [x] out of a closure [fun a => e] must not
    evaluate [e] before [a] is given: [Lc g x] is a closure, [g x] is only
    evaluated once the next argument is supplied. [Lm] marks closures in
    compiled terms (where they are built). Both are convertible to their
    argument. *)
Definition Lc {X A B : Type} (g : X -> A -> B) : X -> A -> B := fun x a => g x a.
Definition Lm {A : Type} (a : A) : A := a.

(** The binders of the branches of a [match] (pattern variables, and the
    variables passed to the selected branch) are not function calls: [Lf]
    and [Lfc] are the versions of [Lm] and [Lc] for them. *)
Definition Lf {A : Type} (a : A) : A := a.
Definition Lfc {X A B : Type} (g : X -> A -> B) : X -> A -> B := fun x a => g x a.

(** ** Delayed computations

    A computation that does not use the bound variable [x] of a closure must
    still be evaluated only when [x] is given. It is abstracted over [tt]
    instead: [Dl h] discards [x] and evaluates [h tt]; [Rc] and [Rc2] apply
    a function to an argument, one of them not using [x]; [Su] is [Sc] on
    [unit]. Unlike [Sc], none of them duplicates [x]. *)
Definition Dl {X B : Type} (h : unit -> B) : X -> B := fun _ => h tt.
Definition Rc {X A B : Type} (h : unit -> A -> B) (g : X -> A) : X -> B :=
  fun x => h tt (g x).
Definition Rc2 {X A B : Type} (f : X -> A -> B) (h : unit -> A) : X -> B :=
  fun x => f x (h tt).
Definition Su {A B : Type} (f : unit -> A -> B) (g : unit -> A) : unit -> B :=
  fun u => f u (g u).

(** Typeclass search must follow the structure of compiled terms instead of
    unfolding the combinators. *)
#[global] Typeclasses Opaque Kc Ic Sc Cc Lc Lm compose Lf Lfc Dl Rc Rc2 Su.

(** ** Case analysis

    The case combinator of an inductive type [I] is named [I_case] and is
    defined with the cost model of [I] (e.g. [nat_case] in [NatCostModel]).
    Its arguments are the type parameters of [I] and the type of the result,
    the branches in the order of the constructors, and the matched value.
    Branches are closures (thunks, taking [tt], for constant constructors),
    so that only the selected branch is evaluated. [Compile] finds it by its
    name. Each case combinator must be declared opaque for typeclass search,
    and added to the hint database [comb] (used by [unfold_comb]). *)
Create HintDb comb.
#[global] Hint Unfold Kc Ic Sc Cc Lc Lm compose Lf Lfc Dl Rc Rc2 Su : comb.
