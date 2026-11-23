(** * Lists of ground data

    The sizes of lists, and the bounds in the sizes of the first-order
    functions, for elements of ground data ([IsGround]: numbers, pairs of
    numbers, ...). Their bounds in the values, for any data, are in
    [HOListComplexity]; [WfExamples] has more of them. *)

From Complexity Require Export NatComplexity ListFacts HOListComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout in the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** The lengths of [firstn] and [skipn] ([ValueFact]). *)
#[global] Instance firstn_value_fact {A} n (l : list A) :
  ValueFact (firstn n l) (fun y => length y = Nat.min n (length l)) := length_firstn n l.
#[global] Instance skipn_value_fact {A} n (l : list A) :
  ValueFact (skipn n l) (fun y => length y = length l - n) := length_skipn n l.

(** The model with the analyses of [nat] and of the lists of any data. *)
Module Type TimeNatLists := TimeNat <+ HOListComplexity.

Module ListComplexity (Import Time : TimeNatLists).

  (** ** Sizes *)
  Lemma length_lt_size {A} `{Size A} (l : list A) : length l < size l.
  Proof. induction l as [|a l]; cbn [length]; [rewrite size_nil | rewrite size_cons]; lia. Qed.

  Lemma list_sum_lt_size (l : list nat) : list_sum l + length l < size l.
  Proof.
    induction l as [|a l]; [rewrite size_nil; cbn; lia |].
    change (list_sum (a :: l)) with (a + list_sum l). cbn [length].
    pose proof (nat_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  (** Lists of lists: the total length of the elements (and their sums for
      lists of numbers). *)
  Lemma list_lengths_lt_size {A} `{Size A} (l : list (list A)) :
    list_sum (map (@length A) l) + length l < size l.
  Proof.
    induction l as [|a l IH]; [rewrite size_nil; cbn; lia|].
    cbn [map length]. change (list_sum (?x :: ?m)) with (x + list_sum m).
    pose proof (length_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Lemma list_sums_lt_size (l : list (list nat)) :
    list_sum (map list_sum l) + list_sum (map (@length nat) l) + length l < size l.
  Proof.
    induction l as [|a l IH]; [rewrite size_nil; cbn; lia|].
    cbn [map length]. change (list_sum (?x :: ?m)) with (x + list_sum m).
    pose proof (list_sum_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Global Instance length_size_fact {A} `{Size A} (l : list A) :
    SizeFact l (length l < size l) | 10 := length_lt_size l.
  Global Instance list_sum_size_fact (l : list nat) :
    SizeFact l (list_sum l + length l < size l) | 1 := list_sum_lt_size l.
  Global Instance list_lengths_size_fact {A} `{Size A} (l : list (list A)) :
    SizeFact l (list_sum (map (@length A) l) + length l < size l) | 2 := list_lengths_lt_size l.
  Global Instance list_sums_size_fact (l : list (list nat)) :
    SizeFact l (list_sum (map list_sum l) + list_sum (map (@length nat) l) + length l < size l)
    | 0 := list_sums_lt_size l.

  (** ** Bounds of the functions that build lists

      Their complexities of results are still to state, as for [rev]
      ([HOListComplexity]). *)

  (** [seq] is recursive on its second argument; the first one changes. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance seq_complexity : Time.ComplexityBound seq
    (fun cs => 4 +> fun cn => (33 * val cn + 4) >|) := _.
  *)

  (** [repeat] recurses on the number of copies. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance repeat_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@repeat A)
    (fun cx => 1 +> fun cn => (21 * val cn + 6) >|) := _.
  *)
  (** [concat] appends each list: linear in the length of the result. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance concat_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@concat A)
    (fun cl => (21 * length (concat (val cl)) + 30 * length (val cl) + 6) >|).
  Proof. cbound. rewrite length_app. lia. Qed.
  *)

  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance combine_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} {B CB} {RB : Repr B CB} {GB : IsGround RB} : Time.ComplexityBound (@combine A B)
    (fun cl => 4 +> fun cm => (54 * length (val cl) + 6) >|) := _.
  *)

  (** ** Bounds in the sizes

      From the bounds of [HOListComplexity]. *)
  Section Sizes.
    Context {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}.
    Global Instance length_linear_bound : Time.LinearBound (@length A) := _.
    Global Instance app_linear_bound : Time.LinearBound (@app A) := _.
    Global Instance tl_constant_bound : Time.ConstantBound (@tl A) := _.
    Global Instance hd_constant_bound : Time.ConstantBound (@hd A) := _.
    Global Instance firstn_linear_bound : Time.LinearBound (@firstn A) := _.
    Global Instance skipn_linear_bound : Time.LinearBound (@skipn A) := _.
    Global Instance nth_linear_bound : Time.LinearBound (@nth A) := _.
    Global Instance rev_polynomial_bound : Time.PolynomialBound (@rev A) := _.
  End Sizes.
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance seq_linear_bound : Time.LinearBound seq := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance repeat_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.LinearBound (@repeat A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance combine_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.LinearBound (@combine A B) := _.
  *)
  (** ** Bounds in the sizes, with their constants

      From the bounds above: a value or a length is at most the size
      ([SizeFact]). *)

  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma seq_size_complexity :
    Time.ComplexityBound seq
      (fun cs => 4 +> fun (cn : ℂI nat _) => (33 * #|val cn| + 0) >|).
  Proof. csize_using seq_complexity. Qed.
  *)

End ListComplexity.
