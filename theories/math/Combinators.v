(** * Combinators for the analysis of lambda-terms *)

From Stdlib Require Import Program.Basics.

(** ** Closures and environments

    The combinators of the categorical abstract machine. An environment
    holds the values of the variables in scope, latest first: [ECons e a],
    or [tt] when empty.

    - [Lam c e a = c (ECons e a)]: the closure of code [c] in [e] (Λ);
    - [ehd], [etl]: the projections of an environment;
    - [Sc f g e = f e (g e)] (S), [compose f g e = f (g e)] (B),
      [Cc f a e = f e a] (C);
    - [Kc a e = a] (K);
    - [etlc f e = f (etl e)]: [compose f etl] in one step, so that the
      variable at depth [p] is read in [p + 1] steps.

    The suffix [c] avoids the [S] of the standard library.

    G. Cousineau, P.-L. Curien, M. Mauny. The categorical abstract machine.
    Science of Computer Programming 8(2):173-202, 1987. *)

(** Not [prod]: environments are distinct from the pairs of the terms. *)
Record env (E A : Type) := ECons { etl : E; ehd : A }.
Arguments ECons {_ _}.
Arguments etl {_ _}.
Arguments ehd {_ _}.

Definition Lam {E A B : Type} (c : env E A -> B) (e : E) (a : A) : B := c (ECons e a).
Definition Kc {A B : Type} (a : A) : B -> A := fun _ => a.
Definition Sc {X A B : Type} (f : X -> A -> B) (g : X -> A) : X -> B := fun x => f x (g x).
Definition Cc {X A B : Type} (f : X -> A -> B) (a : A) : X -> B := fun x => f x a.
Definition etlc {E A B : Type} (f : E -> B) (e : env E A) : B := f (etl e).

(** [consume c e]: the case analysis [c] (a case combinator applied to its
    branches) of the top of [e], whose branches run in the rest of [e]. *)
Definition consume {E I A : Type} (c : (E -> I) -> E -> A) (e : env E I) : A :=
  c (fun _ => ehd e) (etl e).

(** Opaque for typeclass search; the hint database [comb] unfolds them. *)
#[global] Typeclasses Opaque Lam ehd etl Kc Sc Cc etlc compose consume.
Create HintDb comb.
#[global] Hint Unfold Lam ehd etl Kc Sc Cc etlc compose consume : comb.
