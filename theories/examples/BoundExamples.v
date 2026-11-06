(** * Examples of linear and polynomial bounds ([Bounds])

    The bounds of the standard library are instances ([stdlib]),
    and linear bounds are polynomial bounds. The other bounds are derived
    from the bounds of [ComplexityBound] by [clinear] and [cpolynomial],
    which choose the constants, explicitly or by typeclass search. *)

From Complexity Require Import ETHCost.
From Stdlib Require Import List PArith.

Module BoundExamples (Import M : TimeStdlib).

  Module EC := ETHCost M.
  Import EC.

  (** ** Instances of the standard library *)

  Example add_linear : LinearBound Nat.add := _.
  Example mul_polynomial : PolynomialBound Nat.mul := _.

  (** Three arguments. *)
  Example compare_cont_linear : LinearBound Pos.compare_cont := _.

  (** A linear bound is a polynomial bound; the elements of the lists need
      sizes. *)
  Example app_polynomial {A} `{Ground A} `{Size A} : PolynomialBound (@app A) := _.

  (** ** Derived bounds *)

  (** The cost [length l * x] is quadratic in the size. *)
  Lemma insert_uniq_polynomial : PolynomialBound insert_uniq.
  Proof. cpolynomial. Qed.

  (** By typeclass search alone, from the bounds of [ETHCost]. *)
  Example range_linear : LinearBound range := _.
  Example memN_polynomial : PolynomialBound memN := _.
End BoundExamples.
