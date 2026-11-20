(** * Examples of linear and polynomial bounds ([Bounds])

    The bounds of the standard library are instances ([stdlib]),
    and linear bounds are polynomial bounds. The other bounds are derived
    from the bounds of [ComplexityBound] by [clinear] and [cpolynomial],
    which choose the constants, explicitly or by typeclass search. *)

From Complexity Require Import ETHCost.
From Stdlib Require Import List PArith.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module BoundExamples (Import Time : TimeStdlib).

  Module EC := ETHCost Time.
  Import EC.

  (** ** Instances of the standard library *)

  Example add_linear : Time.LinearBound Nat.add := _.
  Example mul_polynomial : Time.PolynomialBound Nat.mul := _.

  (** Three arguments. *)
  Example compare_cont_linear : Time.LinearBound Pos.compare_cont := _.

  (** A linear bound is a polynomial bound; the elements of the lists need
      sizes. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Example app_polynomial {A} {CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.PolynomialBound (@app A) := _.
  *)

  (** ** Derived bounds *)

  (** The cost [length l * x] is quadratic in the size. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma insert_uniq_polynomial : Time.PolynomialBound insert_uniq.
  Proof. cpolynomial. Qed.
  *)

  (** By typeclass search alone, from the bounds of [ETHCost]. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Example range_linear : Time.LinearBound range := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Example memN_polynomial : Time.PolynomialBound memN := _.
  *)
End BoundExamples.
