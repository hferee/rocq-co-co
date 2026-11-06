(** * Complexity of list functions from the standard library

    As in [NatComplexity]: [cbound] proves the bounds, with the smallest
    constants. These functions are
    defined in sections: their type and function parameters are fixed
    arguments of the fixpoint. A functional parameter comes with a
    hypothesis on its complexity. *)

From Complexity Require Export NatComplexity.
From Stdlib Require Import List.
Import ListNotations.

Module ListComplexity (Import M : TimeNat).


  (** ** Sizes *)
  Lemma length_lt_size {A} `{Size A} (l : list A) : length l < size l.
  Proof. induction l as [|a l]; [apply size_nil | pose proof (size_cons a l); cbn [length]; lia]. Qed.

  Lemma list_sum_lt_size (l : list nat) : list_sum l + length l < size l.
  Proof.
    induction l as [|a l]; [apply size_nil|].
    change (list_sum (a :: l)) with (a + list_sum l). cbn [length].
    pose proof (nat_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Global Instance length_size_fact {A} `{Size A} (l : list A) :
    SizeFact l (length l < size l) | 10 := length_lt_size l.
  Global Instance list_sum_size_fact (l : list nat) :
    SizeFact l (list_sum l + length l < size l) | 1 := list_sum_lt_size l.

  (** ** List tail *)
  Instance complexity_tl {A} `{Ground A} :
    ComplexityBound (@tl A) (fun lc => 4 ⋉ tt) := _.

  Global Instance length_complexity {A} `{Ground A} : ComplexityBound (@length A)
    (fun cl => (17 * length (val cl) + 9) ⋉ tt) := _.

  Global Instance app_complexity {A} `{Ground A} : ComplexityBound (@app A)
    (fun cl => 5 ⋉ fun cm =>
       (47 * length (val cl) + 14) ⋉ tt) := _.

  (** [seq] is recursive on its second argument; the first one changes. *)
  Global Instance seq_complexity : ComplexityBound seq
    (fun cs => 7 ⋉ fun cn => (29 * val cn + 2) ⋉ tt) := _.

  (** [fold_left] with a function whose partial and full applications cost at
      most [c1] and [c2] (on ground data): a higher-order bound. *)
  Lemma fold_left_complexity {A B} `{Ground A} `{Ground B} (f : A -> B -> A) (c1 c2 : nat) :
    ComplexityBound f (fun _ => c1 ⋉ fun _ => c2 ⋉ tt) ->
    ComplexityBound (fold_left f)
      (fun cl => 5 ⋉ fun cx =>
         ((c1 + c2 + 45) * length (val cl) + 14) ⋉ tt).
  Proof. intro Hf. cbound. Qed.

  (** ** Bounds in the size of the arguments

      [fold_left] is higher-order: its bound depends on the one of its
      function. *)
  Global Instance tl_constant_bound {A} `{Ground A} `{Size A} : ConstantBound (@tl A) := _.
  Global Instance length_linear_bound {A} `{Ground A} `{Size A} : LinearBound (@length A) := _.
  Global Instance app_linear_bound {A} `{Ground A} `{Size A} : LinearBound (@app A) := _.
  Global Instance seq_linear_bound : LinearBound seq := _.
End ListComplexity.
