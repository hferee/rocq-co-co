(** * Polynomials

    Polynomials with natural coefficients in variables [pvar i], evaluated
    on the list of the values of the variables, [0] for those that are
    missing. They are the bounds of [Bounds] (in the sizes of the arguments
    of a function), and they are higher-order polynomials ([HOPoly]). *)

From Stdlib Require Import List PeanoNat.

Inductive poly : Type :=
| pconst (k : nat)
| pvar (i : nat)
| padd (p q : poly)
| pmul (p q : poly)
| ppow (p : poly) (d : nat).

Fixpoint peval (p : poly) (ss : list nat) : nat :=
  match p with
  | pconst k => k
  | pvar i => nth i ss 0
  | padd p q => peval p ss + peval q ss
  | pmul p q => peval p ss * peval q ss
  | ppow p d => peval p ss ^ d
  end.

Fixpoint pdeg (p : poly) : nat :=
  match p with
  | pconst _ => 0
  | pvar _ => 1
  | padd p q => Nat.max (pdeg p) (pdeg q)
  | pmul p q => pdeg p + pdeg q
  | ppow p d => pdeg p * d
  end.
