(** * Bounds that use the well-formedness of the complexities

    The complexities of functions are compared at the well-formed inputs
    ([wf], [bound_order_arr]): the
    bounds may state the complexity of the result from those of the inputs,
    as [pot cl] for a list, as the bounds of the library do ([tl], [hd],
    [app], [rev], [firstn], [skipn], [nth], [HOListComplexity]). [cbound]
    computes it from the case analyses, which give the default complexity
    to a missing element and build the empty list: the two differ only at
    the inputs that are not well-formed, and each proof ends with a case on
    the well-formed complexity of the input. The examples below use it for a list, in a pair
    and in the environment of a recursive function. *)

From Complexity Require Export ListComplexity.
From Stdlib Require Import List Lia.
Import ListNotations.

#[local] Ltac2 Set ctimeout := 0.

Module WfExamples (Import Time : TimeNatLists).

  (** ** Lists *)

  (** A complexity read before the list is analysed: the case analyses
      disagree with the bound only at the inputs that are not well-formed,
      where the hypothesis [wf] is contradictory. *)
  Fixpoint hd_rep {A} (l : list A) (n : nat) : list A :=
    match n with 0 => [] | S n => match l with [] => [] | x :: _ => x :: hd_rep l n end end.
  Global Instance hd_rep_wf {A CA} `{Repr A CA} : Time.ComplexityBound (@hd_rep A)
    (fun cl => 2 +> fun cn => (33 * val cn + 13) +>
       match pot cl with [] => [] | h :: _ => repeat h (val cn) end).
  Proof.
    cbound; rewrite E, E0 in Hwf;
      first [apply wf_nil in Hwf | destruct (wf_cons _ _ _ Hwf) as (h & t & ? & _)]; discriminate.
  Qed.

  (** ** Pairs and environments

      A well-formed list in a pair ([wf_prod]). *)
  Definition tl_fst {A B} (p : list A * B) : list A :=
    match p with (l, _) => match l with [] => [] | _ :: t => t end end.
  Global Instance tl_fst_wf {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@tl_fst A B) (fun cp => 10 +> tl (fst (pot cp))).
  Proof.
    cbound. rewrite E, E0 in Hwf. apply wf_prod in Hwf as [Hl _]. cbn in Hl.
    apply wf_nil in Hl. rewrite Hl. reflexivity.
  Qed.

  (** A recursive function with arguments passed unchanged has them in the
      environment of its fixpoint ([crec_env]), where the list is
      well-formed ([wf_env]). *)
  Fixpoint hd_rep2 {A} (d : A) (l : list A) (n : nat) : list A :=
    match n with 0 => [] | S n => match l with [] => d | x :: _ => x end :: hd_rep2 d l n end.
  Global Instance hd_rep2_wf {A CA} `{Repr A CA} : Time.ComplexityBound (@hd_rep2 A)
    (fun cd => 1 +> fun cl => 2 +> fun cn =>
       (40 * val cn + 20) +> repeat (hd (pot cd) (pot cl)) (val cn)).
  Proof.
    cbound; apply wf_env in Hwf as [_ Hl]; cbn in Hl; rewrite E in Hl;
      first [apply wf_nil in Hl; rewrite Hl | destruct (wf_cons _ _ _ Hl) as (h & t & -> & _)];
      reflexivity.
  Qed.
End WfExamples.
