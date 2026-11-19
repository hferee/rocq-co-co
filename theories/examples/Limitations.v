(** * Limitations of the analysis

    Functions that [cbound] cannot analyse, with the error that it reports
    and the reason; each example ends with [Abort] (item C2 of
    [contributions_and_plan.md]). Local fixpoints, well-founded recursion
    ([Examples]) and user inductives, which come with their own axioms as
    the datatypes of the model do, are not limitations. *)

From Complexity Require Import TimeStdlib.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module Limitations (Import Time : TimeStdlib).

  (** ** Dependent matches

      The case combinators ([nat_case], [list_case], ...) are not
      dependent: the type of the branches does not depend on the matched
      value. The convoy pattern, which matches [n] with a return type that
      mentions [n] to keep the equation of the branch, is compiled to an
      ill-typed term. Moreover the equation is a proof, and proofs have no
      representation in the model ([Repr] is for data): even a dependent
      case combinator would need one for [n = m]. *)
  Definition pred_convoy (n : nat) : nat :=
    match n as m return n = m -> nat with O => fun _ => 0 | S k => fun _ => k end eq_refl.

  Lemma pred_convoy_complexity : Time.ComplexityBound pred_convoy (fun cn => 100 >|).
  Proof.
    Fail cbound.
    (* Illegal application: The term "@compose" of type
       "forall A B C : Type, (B -> C) -> (A -> B) -> A -> C"
       cannot be applied to the terms ... "@eq_refl nat" ... *)
  Abort.
End Limitations.
