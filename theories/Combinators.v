(** * Combinators for the analysis of lambda-terms

    This file only contains (transparent) definitions; their complexities are
    axiomatised in [CombinatorCostModel]. The tactics of [Compile] rewrite a term into a
    *convertible* term built from these combinators, whose complexity can then
    be found by plain first-order typeclass search. *)

From Stdlib Require Import Program.Basics.

(** ** Bracket abstraction

    [Kc], [Ic], [Sc], [Cc] and [compose] are the combinators K, I, S, C and
    B of Turner's bracket abstraction (the suffix [c] avoids the [S] and [I]
    of the standard library; B is [compose] of [Program.Basics]).

    Under call-by-value, the abstraction of a variable [x] out of a term must
    not evaluate the computations of the term when the closure is built: K
    only abstracts values (variables, partial applications of combinators to
    values, closed terms), and the other terms are abstracted structurally,
    with S, B and C, even when they do not use [x]. This is the by-value
    abstraction of Gateley and Duba ([Compile.abs]).

    - D. A. Turner. A new implementation technique for applicative
      languages. Software: Practice and Experience 9(1):31-49, 1979.
    - J. Gateley, B. F. Duba. Call-by-value combinatory logic and the
      lambda-value calculus. MFPS 1991, LNCS 598:41-53, 1992. *)
Definition Kc {A B : Type} (a : A) : B -> A := fun _ => a.
Definition Ic {A : Type} : A -> A := fun a => a.
Definition Sc {X A B : Type} (f : X -> A -> B) (g : X -> A) : X -> B := fun x => f x (g x).
Definition Cc {X A B : Type} (f : X -> A -> B) (a : A) : X -> B := fun x => f x a.

(** Typeclass search must follow the structure of compiled terms instead of
    unfolding the combinators; [unfold_comb] ([Compile]) unfolds them, with
    the hint database [comb]. *)
#[global] Typeclasses Opaque Kc Ic Sc Cc compose.
Create HintDb comb.
#[global] Hint Unfold Kc Ic Sc Cc compose : comb.

(** ** Case analysis

    The case combinator of an inductive type [I] is named [I_case] and is
    defined with the cost model of [I] (e.g. [nat_case] in [NatCostModel]).
    Its arguments are the type parameters of [I] and the type of the result,
    the branches in the order of the constructors, and the matched value.
    Branches are closures (thunks, taking [tt], for constant constructors),
    so that only the selected branch is evaluated. [Compile] finds it by its
    name. Each case combinator must be declared opaque for typeclass search,
    and added to the hint database [comb]. *)
