(** * Peak space of small functions ([SpaceCostModel])

    A profile [SP steps peak keep]: the unfoldings, the high point of the
    memory, and the memory kept by the result. [keep] counts the cells of
    the environments as kept, as a result that is a closure may reach them
    (linked environments): [double] keeps [6] cells per step, [2] of which
    are those of its result. *)

From Complexity Require Export SpaceCostModel.

Module PeakExamples (Import Space : SpaceCostModel).

  Definition succ2 (n : nat) : nat := S (S n).

  (** Two cells, kept by the result. *)
  Lemma succ2_space : ComplexityBound succ2 (fun cn => SP 0 2 2 >|).
  Proof. unfold succ2. cbound. Qed.

  Fixpoint double (n : nat) : nat := match n with O => O | S k => S (S (double k)) end.

  Lemma double_space : ComplexityBound double
    (fun cn => SP (val cn + 1) (6 * val cn + 5) (6 * val cn + 4) >|).
  Proof. cbound. Qed.
End PeakExamples.
