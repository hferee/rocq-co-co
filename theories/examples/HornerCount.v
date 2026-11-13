(** * Counting arithmetic operations

    Analyses in [ArithOpsTimeCostModel] ([TimeArith]), where an addition
    costs [c_add], a multiplication [c_mul], an unfolding of a fixpoint
    [c_fix], and everything else is free. The three constants are abstract:
    the coefficient of each one in a bound is the number of operations of
    its kind. In [ArithCountTimeCostModel], where they are [1], the bounds
    are total numbers of operations. *)

From Complexity Require Import TimeArith.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** A polynomial, as written and in Horner's form. *)
Example poly_example (x : nat) : nat := x * x + 3 * x + 1.
Example poly_example_horner (x : nat) : nat := (x + 3) * x + 1.

(** Horner's evaluation of the polynomial of coefficients [l], from the
    constant one, at [x]. *)
Fixpoint horner (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | a :: t => a + x * horner x t end.

Module HornerCount (Import Time : ArithOpsTimeCostModel).

  (** Two multiplications and two additions as written; Horner's form
      saves a multiplication. *)
  Example poly_example_complexity : Time.ComplexityBound poly_example
    (fun cx => (2 * c_mul + 2 * c_add) >|) := _.

  Example poly_example_horner_complexity : Time.ComplexityBound poly_example_horner
    (fun cx => (c_mul + 2 * c_add) >|) := _.

  (** One addition, one multiplication and one unfolding for each
      coefficient, and one more unfolding at the end of the list. [x] is
      passed unchanged by the recursive calls: it is in the environment of
      the fixpoint ([fix_complexity]), and applying [horner] to it only
      builds a closure, which is free here. *)
  Lemma horner_complexity : 1 <= c_fix -> Time.ComplexityBound horner
    (fun cx => 0 +> fun cl => (length (val cl) * (c_add + c_mul + c_fix) + c_fix) >|).
  Proof. intro. cbound. Qed.

  (** Matches on numbers have no known cost. *)
  Fail Definition pred_complexity : Time.ComplexityBound Nat.pred (fun cn => 0 >|) := _.
End HornerCount.
