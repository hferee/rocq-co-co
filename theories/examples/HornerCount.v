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

(** A polynomial, as written and in Horner's form. *)
Example poly_example (x : nat) : nat := x * x + 3 * x + 1.
Example poly_example_horner (x : nat) : nat := (x + 3) * x + 1.

(** Horner's evaluation of the polynomial of coefficients [l], from the
    constant one, at [x]. *)
Fixpoint horner (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | a :: t => a + x * horner x t end.

Module HornerCount (Import M : ArithOpsTimeCostModel).

  (** Two multiplications and two additions as written; Horner's form
      saves a multiplication. *)
  Example poly_example_complexity : ComplexityBound poly_example
    (fun cx => (2 * c_mul + 2 * c_add) ⋉ tt) := _.

  Example poly_example_horner_complexity : ComplexityBound poly_example_horner
    (fun cx => (c_mul + 2 * c_add) ⋉ tt) := _.

  (** One addition, one multiplication and one unfolding for each
      coefficient, and one more unfolding, charged when [horner] is applied
      to [x]. *)
  Lemma horner_complexity : 1 <= c_fix -> ComplexityBound horner
    (fun cx => c_fix ⋉ fun cl => (length (val cl) * (c_add + c_mul + c_fix)) ⋉ tt).
  Proof. intro. cbound. Qed.

  (** Matches on numbers have no known cost. *)
  Fail Definition pred_complexity : ComplexityBound Nat.pred (fun cn => 0 ⋉ tt) := _.
End HornerCount.
