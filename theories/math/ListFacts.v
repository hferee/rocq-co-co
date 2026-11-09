(** * Facts on lists missing from the standard library *)

From Stdlib Require Import Arith List Lia.

(** An element of a list of numbers is at most their sum. *)
Lemma list_sum_In l n : In n l -> n <= list_sum l.
Proof.
  induction l as [|m l IH]; [contradiction|]. change (list_sum (m :: l)) with (m + list_sum l).
  intros [-> | H]; [lia | specialize (IH H); lia].
Qed.
