(** * Peak space of small functions ([SpaceCostModel])

    A profile [SP steps need ret]: the unfoldings, the high point of the
    memory, and the memory freed at the end, [need - ret] being still
    allocated. The cells of an environment are freed when its scope
    returns ground data ([PeakSpace]); the others stay allocated, as a
    result that is a closure may reach them (linked environments). *)

From Complexity Require Export SpaceCostModel.

(** A larger timeout than the library's ([ctimeout_lib]): with the
    releases of the scopes, the profiles of [double] have many truncated
    subtractions, and its analysis takes about 13 s. *)
#[local] Ltac2 Set ctimeout := 30.

Module PeakExamples (Import Space : SpaceCostModel).

  Definition succ2 (n : nat) : nat := S (S n).

  (** Two cells, kept by the result. *)
  Lemma succ2_space : Space.ComplexityBound succ2 (fun cn => SP 0 2 0 >|).
  Proof. unfold succ2. cbound. Qed.

  Fixpoint double (n : nat) : nat := match n with O => O | S k => S (S (double k)) end.

  Lemma double_space : Space.ComplexityBound double
    (fun cn => SP (val cn + 1) (6 * val cn + 5) (2 * val cn + 2) >|).
  Proof. cbound. Qed.

  (** A tail-recursive loop, constant in space with a garbage collector:
      the environments of a call are garbage once it calls itself. Each
      unfolding allocates [4] cells: the environment of the fixpoint
      ([c_fix]), the closure of its body ([c_clo]), and its environment
      extended with the argument ([c_Lam]) and with the predecessor
      ([c_case_nat]). The last two are freed when the call returns, after
      the recursive call: the peak is linear. *)
  Fixpoint loop (n : nat) : nat := match n with O => O | S k => loop k end.

  (** [cbound], step by step: the fixpoint rule ([crec]), the bound of the
      functional, compiled to
      [Lam (nat_case (Kc 0) (Sc (etlc (etlc ehd)) ehd) ehd)], from the
      rules of its combinators (which [cbc_found] finds), and the recurrence
      ([cfinish]). *)
  Lemma loop_space : Space.ComplexityBound loop
    (fun cn => SP (val cn + 1) (4 * val cn + 5) (2 * val cn + 2) >|).
  Proof.
    crec.
    - compile_goal.
      (* Frees the cell of [n] when the call returns ground data
         ([c_unLam]). *)
      eapply apply_complexity; [| exact Lam_ground_complexity].
      eapply apply_complexity; [exact ehd_complexity |].
      (* Frees the frame of the matched value ([c_pop]), and the cell of
         the predecessor when the branch returns ([c_uncase_nat]). *)
      eapply apply_complexity;
        [| eapply apply_complexity; [| exact nat_case_ground_complexity]].
      + (* branch [S k]: the call [loop k], in tail position. Frees the
           frames of its function and argument ([Sc]); the cells above are
           freed after it returns. *)
        eapply apply_complexity; [exact ehd_complexity |].
        eapply apply_complexity; [| exact Sc_complexity].
        eapply apply_complexity; [| exact etlc_complexity].
        eapply apply_complexity; [exact ehd_complexity | exact etlc_complexity].
      + (* branch [O] *)
        eapply apply_complexity; [exact (nat_complexity 0) | exact Kc_complexity].
    - (* the recurrence: the frees made after the recursive call are in the
         memory returned ([ret]), not in the peak *)
      csimpl. bo_split. destr_inputs. ccases. all: cbn -[Nat.mul Nat.sub]; lia.
  Qed.

  (** The same function, as a loop ([while_complexity]): an iteration is
      over, its cells freed, when the next one starts, and the peak is
      constant. The proof is by hand: the loop is given by its test, its
      result and its next value. *)
  Definition is_zero (n : nat) : bool := match n with O => true | S _ => false end.

  Lemma loop_while : forall n, loop n = while_unfold is_zero (fun _ => 0) pred loop n.
  Proof. intros []; reflexivity. Qed.

  Lemma loop_space_while : Space.ComplexityBound loop (fun cn => SP (val cn + 1) 3 3 >|).
  Proof.
    (* Frees the frames of the test and of the next value ([framed]). *)
    eapply (while_complexity is_zero (fun _ => 0) pred).
    - (* an iteration takes a step *)
      intros [s p q] H. cbv in H. lia.
    - exact loop_while.
    - (* [is_zero], compiled to [nat_case (Kc true) (Kc false) (fun x => x)] *)
      unfold is_zero. compile_goal.
      eapply apply_complexity; [exact id_complexity |].
      (* Frees the frame of the matched value, and the cell of the
         predecessor when the branch returns a boolean ([c_uncase_nat]). *)
      eapply apply_complexity;
        [| eapply apply_complexity; [| exact nat_case_ground_complexity]].
      + eapply apply_complexity; [exact (bool_complexity false) | exact Kc_complexity].
      + eapply apply_complexity; [exact (bool_complexity true) | exact Kc_complexity].
    - cbc_found.
    - (* [pred], compiled to [nat_case (fun x => x) ehd (fun x => x)] *)
      unfold pred. compile_goal.
      eapply apply_complexity; [exact id_complexity |].
      (* Frees as for [is_zero]: the predecessor, older than the cell, is
         returned. *)
      eapply apply_complexity;
        [| eapply apply_complexity; [| exact nat_case_ground_complexity]].
      + exact ehd_complexity.
      + exact id_complexity.
    - (* the recurrence: the iterations in sequence, each one balanced *)
      unfold is_zero. csimpl. bo_split. destr_inputs. ccases. all: cbn -[Nat.mul Nat.sub]; lia.
  Qed.

  (** [steps] counts the iterations; the space is the peak ([cnat]), [3]:
      a constant bound in the sizes. *)
  Existing Instance loop_space_while.
  Lemma loop_constant : Space.ConstantBound loop.
  Proof. cbound. Qed.
End PeakExamples.
