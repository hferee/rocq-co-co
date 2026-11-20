(** * Complexity of the first-order list functions of the standard library

    [cbound] proves the bounds, with the smallest constants. The elements
    are ground data ([IsGround]: numbers, pairs of numbers, ...), so that
    the complexity of a result of ground data is any one ([>|]); lists
    are not ground ([wf_list]). The functions on lists of any data
    ([length], [app], [tl]) and the higher-order functions are in
    [HOListComplexity]; [ShapeExamples] has bounds of more of them, by
    the shapes of the complexities. *)

From Complexity Require Export NatComplexity ListFacts HOListComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** The facts on the values of [firstn] and [skipn] ([ValueFact]): their
    lengths. *)
#[global] Instance firstn_value_fact {A} n (l : list A) :
  ValueFact (firstn n l) (fun y => length y = Nat.min n (length l)) := length_firstn n l.
#[global] Instance skipn_value_fact {A} n (l : list A) :
  ValueFact (skipn n l) (fun y => length y = length l - n) := length_skipn n l.

(** The model with the analyses of [nat] and the bounds of the functions on
    lists of any data ([app], used by [rev] and [concat]). *)
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
    SizeFact l (list_sum (map list_sum l) + list_sum (map (@length nat) l) + length l < size l) | 0 :=
    list_sums_lt_size l.

  (** ** Bounds

      These functions are defined in sections: their type parameters are
      fixed arguments of the fixpoint. A functional parameter that is fixed
      comes with a hypothesis on its complexity
      ([fold_left_const_complexity]). *)

  (** [seq] is recursive on its second argument; the first one changes. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance seq_complexity : Time.ComplexityBound seq
    (fun cs => 4 +> fun cn => (33 * val cn + 4) >|) := _.
  *)

  (** [firstn], [skipn] and [nth] recurse on the index, [repeat] on the
      number of copies. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance firstn_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@firstn A)
    (fun cn => 4 +> fun cl => (39 * val cn + 6) >|) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance skipn_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@skipn A)
    (fun cn => 4 +> fun cl => (32 * val cn + 6) >|) := _.
  *)
  Global Instance nth_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@nth A)
    (fun cn => 4 +> fun cl => 2 +> fun cd => (48 * val cn + 14) >|) := _.
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance repeat_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@repeat A)
    (fun cx => 1 +> fun cn => (21 * val cn + 6) >|) := _.
  *)
  Global Instance hd_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@hd A)
    (fun cd => 1 +> fun cl => 6 >|) := _.

  (** [rev] appends each element at the end of the reversed tail:
      quadratic. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance rev_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (11 * length (val cl) + 23) + 6) >|).
  Proof. cbound. rewrite length_rev. nia. Qed.
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

  (** [fold_left f], for a function [f] on ground data whose partial and
      full applications cost at most [c1] and [c2]. [f] is fixed: it is a
      parameter of the fixpoint, kept in the environment of its closure
      (for any function, see [HOListComplexity]). *)
  Lemma fold_left_const_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} {B CB} {RB : Repr B CB} {GB : IsGround RB} (f : A -> B -> A) (c1 c2 : nat) :
    Time.ComplexityBound f (fun _ : ℂI A CA => c1 +> fun _ : ℂI B CB => c2 >|) ->
    Time.ComplexityBound (fold_left f)
      (fun cl => 4 +> fun cx =>
         ((c1 + c2 + 31) * length (val cl) + 6) >|).
  Proof. intro Hf. cbound. Qed.

  (** ** Bounds in the size of the arguments

      Also for [length] and [app], whose bounds are those of
      [HOListComplexity]. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance length_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} :
    Time.LinearBound (@length A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance app_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} :
    Time.LinearBound (@app A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance tl_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.ConstantBound (@tl A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance seq_linear_bound : Time.LinearBound seq := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance firstn_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.LinearBound (@firstn A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance skipn_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.LinearBound (@skipn A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance nth_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.LinearBound (@nth A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance repeat_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.LinearBound (@repeat A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance hd_constant_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.ConstantBound (@hd A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance rev_polynomial_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} : Time.PolynomialBound (@rev A) := _.
  *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance combine_linear_bound {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A} {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B} :
    Time.LinearBound (@combine A B) := _.
  *)
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma seq_size_complexity :
    Time.ComplexityBound seq
      (fun cs => 4 +> fun (cn : ℂI nat _) => (33 * #|val cn| + 0) >|).
  Proof. csize_using seq_complexity. Qed.
  *)

End ListComplexity.
