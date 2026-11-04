(** * Combinators for the analysis of lambda-terms

    This file only contains (transparent) definitions; their complexities are
    axiomatised in [CombinatorCostModel]. The tactics of [Compile] rewrite a term into a
    *convertible* term built from these combinators, whose complexity can then
    be found by plain first-order typeclass search. *)

From Stdlib Require Import Program.Basics.

(** ** Closure conversion

    [Compile] turns every lambda into a closure: its code, a function of an
    environment, applied to the environment where the closure is built
    (linked environments, as in the CAM; flat closures, which copy their
    free variables when they are built, gave larger bounds). An environment
    is the list of the values of the variables in scope, the latest bound
    first: an [env] of an environment and a value, or the empty environment
    [tt]. The combinators are those of the categorical abstract machine:

    - [Lam c e a = c (ECons e a)]: the closure of code [c] and environment
      [e] (the currying Λ of the CAM);
    - [ehd] and [etl]: the projections of an environment, which give access
      to the variables;
    - [Sc f g e = f e (g e)]: an application, both parts computed in the
      environment [e] (S); [compose f g e = f (g e)] (B) and
      [Cc f a e = f e a] (C) when one part does not use [e];
    - [Kc a e = a]: a term that does not use the environment (K).

    The suffix [c] avoids the [S] and [I] of the standard library.

    G. Cousineau, P.-L. Curien, M. Mauny. The categorical abstract machine.
    Science of Computer Programming 8(2):173-202, 1987. *)

(** A dedicated type rather than [prod]: pairs are ground data
    ([DatatypesCostModel]), whereas environments contain closures, whose
    complexities they keep. *)
Record env (E A : Type) := ECons { etl : E; ehd : A }.
Arguments ECons {_ _}.
Arguments etl {_ _}.
Arguments ehd {_ _}.

Definition Lam {E A B : Type} (c : env E A -> B) (e : E) (a : A) : B := c (ECons e a).
Definition Kc {A B : Type} (a : A) : B -> A := fun _ => a.
Definition Sc {X A B : Type} (f : X -> A -> B) (g : X -> A) : X -> B := fun x => f x (g x).
Definition Cc {X A B : Type} (f : X -> A -> B) (a : A) : X -> B := fun x => f x a.

(** The identity (I) is only used by bracket abstraction ([BracketCompile]). *)
Definition Ic {A : Type} : A -> A := fun a => a.

(** Typeclass search must follow the structure of compiled terms instead of
    unfolding the combinators; [unfold_comb] ([Compile]) unfolds them, with
    the hint database [comb]. *)
#[global] Typeclasses Opaque Lam ehd etl Kc Ic Sc Cc compose.
Create HintDb comb.
#[global] Hint Unfold Lam ehd etl Kc Ic Sc Cc compose : comb.

(** ** Case analysis

    The case combinator of an inductive type [I] is named [I_case] and is
    defined with the cost model of [I] (e.g. [nat_case] in
    [DatatypesCostModel]). Its arguments are the type parameters of [I] and
    the type of the result, the branches in the order of the constructors,
    and the matched value. Branches are closures (thunks, taking [tt], for
    constant constructors), so that only the selected branch is evaluated.
    [Compile] finds it by its name. Each case combinator must be declared
    opaque for typeclass search, and added to the hint database [comb]. *)
