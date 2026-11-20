(** * Bounds that use the shapes of the complexities

    The complexities of functions are compared at the inputs whose
    complexity has the shape of the value ([wf], [bound_order_arr]). The
    bounds below state the complexity of the result from those of the
    inputs, as [pot cl] for a list: [cbound] computes it from the case
    analyses, which give the default complexity to a missing element and
    build the empty list, and the two differ only at the inputs of another
    shape. Each proof ends with a case on the shape of the input. *)

From Complexity Require Export ListComplexity.
From Stdlib Require Import List Lia.
Import ListNotations.

#[local] Ltac2 Set ctimeout := 0.

Module ShapeExamples (Import Time : TimeNatLists).

  (** ** Lists

      [hd d l] at [[]] is [d], with its complexity, whereas the head of a
      longer complexity is not; at [x :: l], the case analysis gives the
      head of [pot cl], or the default one if [pot cl] is empty. *)
  Global Instance hd_shape {A CA} `{Repr A CA} :
    Time.ComplexityBound (@hd A) (fun cd => 1 +> fun cl => 6 +> hd (pot cd) (pot cl)).
  Proof.
    cbound; rewrite E in Hwf0;
      first [apply wf_nil in Hwf0; rewrite Hwf0 | destruct (wf_cons _ _ _ Hwf0) as (h & t & -> & _)];
      reflexivity.
  Qed.

  (** [app_complexity] with [pot cl] for [map pot (czip cdefault cl)]. *)
  Global Instance app_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm => (21 * length (val cl) + 10) +> (pot cl ++ pot cm)).
  Proof.
    cbound; rewrite E in Hwf0;
      first [apply wf_nil in Hwf0; rewrite Hwf0 | destruct (wf_cons _ _ _ Hwf0) as (h & t & -> & _)];
      reflexivity.
  Qed.

  (** The bound of the lists of ground data ([rev_complexity],
      [ListComplexity]), for lists of any data: the complexities reversed.
      It uses [app_shape]. *)
  Global Instance rev_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (11 * length (val cl) + 23) + 6) +> rev (pot cl)).
  Proof.
    cbound.
    - rewrite length_rev. lia.
    - rewrite E in Hwf. apply wf_nil in Hwf. rewrite Hwf. reflexivity.
    - rewrite E in Hwf. destruct (wf_cons _ _ _ Hwf) as (h & t & -> & _). reflexivity.
  Qed.

  (** [skipn] builds [[]] when the list runs out, and [firstn] reads the
      heads of the complexity with the default one. *)
  Global Instance skipn_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@skipn A)
    (fun cn => 4 +> fun cl => (32 * val cn + 6) +> skipn (val cn) (pot cl)).
  Proof.
    cbound; rewrite E in Hwf0;
      first [apply wf_nil in Hwf0; rewrite Hwf0 | destruct (wf_cons _ _ _ Hwf0) as (h & t & -> & _)];
      reflexivity.
  Qed.

  Global Instance firstn_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@firstn A)
    (fun cn => 4 +> fun cl => (39 * val cn + 6) +> firstn (val cn) (pot cl)).
  Proof.
    cbound; rewrite E in Hwf0;
      first [apply wf_nil in Hwf0; rewrite Hwf0 | destruct (wf_cons _ _ _ Hwf0) as (h & t & -> & _)];
      reflexivity.
  Qed.

  Global Instance nth_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@nth A)
    (fun cn => 4 +> fun cl => 2 +> fun cd => (48 * val cn + 14) +> nth (val cn) (pot cl) (pot cd)).
  Proof.
    cbound; rewrite E in Hwf0;
      first [apply wf_nil in Hwf0; rewrite Hwf0 | destruct (wf_cons _ _ _ Hwf0) as (h & t & -> & _)];
      reflexivity.
  Qed.

  (** A complexity read before the list is analysed: the case analyses
      disagree with the bound only at the inputs of another shape, where
      the shape is contradictory. *)
  Fixpoint hd_rep {A} (l : list A) (n : nat) : list A :=
    match n with 0 => [] | S n => match l with [] => [] | x :: _ => x :: hd_rep l n end end.
  Global Instance hd_rep_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@hd_rep A)
    (fun cl => 2 +> fun cn => (33 * val cn + 13) +>
       match pot cl with [] => [] | h :: _ => repeat h (val cn) end).
  Proof.
    cbound; rewrite E, E0 in Hwf;
      first [apply wf_nil in Hwf | destruct (wf_cons _ _ _ Hwf) as (h & t & ? & _)]; discriminate.
  Qed.

  (** ** Pairs and environments

      The shape of a list in a pair ([wf_prod]). *)
  Definition tl_fst {A B} (p : list A * B) : list A :=
    match p with (l, _) => match l with [] => [] | _ :: t => t end end.
  Global Instance tl_fst_shape {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@tl_fst A B) (fun cp => 10 +> tl (fst (pot cp))).
  Proof.
    cbound. rewrite E, E0 in Hwf. apply wf_prod in Hwf as [Hl _]. cbn in Hl.
    apply wf_nil in Hl. rewrite Hl. reflexivity.
  Qed.

  (** A recursive function with arguments passed unchanged has them in the
      environment of its fixpoint ([crec_env]): the shape of the list in it
      ([wf_env]). *)
  Fixpoint hd_rep2 {A} (d : A) (l : list A) (n : nat) : list A :=
    match n with 0 => [] | S n => match l with [] => d | x :: _ => x end :: hd_rep2 d l n end.
  Global Instance hd_rep2_shape {A CA} `{Repr A CA} : Time.ComplexityBound (@hd_rep2 A)
    (fun cd => 1 +> fun cl => 2 +> fun cn =>
       (40 * val cn + 20) +> repeat (hd (pot cd) (pot cl)) (val cn)).
  Proof.
    cbound; apply wf_env in Hwf as [_ Hl]; cbn in Hl; rewrite E in Hl;
      first [apply wf_nil in Hl; rewrite Hl | destruct (wf_cons _ _ _ Hl) as (h & t & -> & _)];
      reflexivity.
  Qed.
End ShapeExamples.
