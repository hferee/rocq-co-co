(** * Facts on the values computed by the ETH algorithm

    The facts on the values of the functions of [ETHAlgorithm] that the
    cost analysis uses ([ETHCost]): the lengths of the sorted lists, and
    the codes of the literals. They do not depend on the cost model. *)

From Complexity Require Import ETHAlgorithm.
From Stdlib Require Import Arith List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(** ** Sorted lists

    An insertion adds at most one element: the sorted lists are at most as
    long as the original ones. *)

Lemma length_insert_uniq x l : length (insert_uniq x l) <= S (length l).
Proof.
  induction l as [|y l IH]; cbn [insert_uniq length]; [lia|].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [length] in *; lia.
Qed.

Lemma length_sort_uniq l : length (fold_right insert_uniq [] l) <= length l.
Proof.
  induction l as [|x l IH]; cbn [fold_right length]; [lia|].
  pose proof (length_insert_uniq x (fold_right insert_uniq [] l)). lia.
Qed.

Lemma length_insert_clause C F : length (insert_clause C F) <= S (length F).
Proof.
  induction F as [|D F IH]; cbn [insert_clause length]; [lia|].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [length] in *; lia.
Qed.

Lemma length_sort_clauses F : length (fold_right insert_clause [] F) <= length F.
Proof.
  induction F as [|C F IH]; cbn [fold_right length]; [lia|].
  pose proof (length_insert_clause C (fold_right insert_clause [] F)). lia.
Qed.

(** ** Codes of the literals *)

Lemma lit_code_le l : lit_code l <= 2 * lvar l + 1.
Proof. unfold lit_code. destruct (lpos l); lia. Qed.

Lemma code_var_le c : 2 * code_var c <= c.
Proof. unfold code_var. pose proof (Nat.div2_odd c). destruct (Nat.odd c); cbn in *; lia. Qed.

Lemma code_neg_le c : code_neg c <= S c.
Proof. unfold code_neg. destruct (Nat.odd c); lia. Qed.
