(** * Facts on lists missing from the standard library *)

From Stdlib Require Import Arith List Lia.

(** An element of a list of numbers is at most their sum. *)
Lemma list_sum_In l n : In n l -> n <= list_sum l.
Proof.
  induction l as [|m l IH]; [contradiction|]. change (list_sum (m :: l)) with (m + list_sum l).
  intros [-> | H]; [lia | specialize (IH H); lia].
Qed.

(** ** Sums of the images of the elements of a list *)
Section ListSumMap.
  Context {A : Type}.

  Lemma list_sum_map_const (c : nat) (l : list A) : list_sum (map (fun _ => c) l) = c * length l.
  Proof. induction l; cbn [map length]; [cbn; lia|]. change (list_sum (?a :: ?m)) with (a + list_sum m). lia. Qed.

  Lemma list_sum_map_S (f : A -> nat) l :
    list_sum (map (fun x => S (f x)) l) = length l + list_sum (map f l).
  Proof. induction l; cbn [map length]; [cbn; lia|]. change (list_sum (?a :: ?m)) with (a + list_sum m). lia. Qed.

  Lemma list_sum_map_add (f g : A -> nat) l :
    list_sum (map (fun x => f x + g x) l) = list_sum (map f l) + list_sum (map g l).
  Proof. induction l; cbn [map length]; [cbn; lia|]. change (list_sum (?a :: ?m)) with (a + list_sum m). lia. Qed.

  Lemma list_sum_map_mul_l (c : nat) (f : A -> nat) l :
    list_sum (map (fun x => c * f x) l) = c * list_sum (map f l).
  Proof. induction l; cbn [map length]; [cbn; lia|]. change (list_sum (?a :: ?m)) with (a + list_sum m). lia. Qed.

  Lemma list_sum_map_mul_r (c : nat) (f : A -> nat) l :
    list_sum (map (fun x => f x * c) l) = list_sum (map f l) * c.
  Proof. induction l; cbn [map length]; [cbn; lia|]. change (list_sum (?a :: ?m)) with (a + list_sum m). lia. Qed.

  Lemma list_sum_map_le (f g : A -> nat) l :
    (forall x, In x l -> f x <= g x) -> list_sum (map f l) <= list_sum (map g l).
  Proof.
    induction l as [|a l IH]; intro Hfg; cbn [map]; [reflexivity|].
    change (list_sum (?a :: ?m)) with (a + list_sum m).
    pose proof (Hfg a (or_introl eq_refl)). pose proof (IH (fun x Hx => Hfg x (or_intror Hx))). lia.
  Qed.

  Lemma list_sum_map_le_const (f : A -> nat) (c : nat) l :
    (forall x, In x l -> f x <= c) -> list_sum (map f l) <= c * length l.
  Proof. intro Hf. rewrite (list_sum_map_le f (fun _ => c) l Hf), list_sum_map_const. reflexivity. Qed.
End ListSumMap.

Lemma list_sum_map_id (l : list nat) : list_sum (map (fun x => x) l) = list_sum l.
Proof. rewrite map_id. reflexivity. Qed.

Lemma list_sum_map_le_affine (f : nat -> nat) (a b : nat) l :
  (forall x, In x l -> f x <= a * x + b) -> list_sum (map f l) <= a * list_sum l + b * length l.
Proof.
  intro Hf. rewrite (list_sum_map_le f (fun x => a * x + b) l Hf).
  rewrite list_sum_map_add, list_sum_map_mul_l, list_sum_map_id, list_sum_map_const. reflexivity.
Qed.

(** [simpl_list_sum] distributes the sums [list_sum (map f l)] of the goal
    and of the hypotheses over the constants, the successors, the sums and
    the products by factors that do not depend on the element, and computes
    the lengths of the [map]s. *)
Ltac simpl_list_sum :=
  repeat first
    [ rewrite length_map in *
    | rewrite list_sum_map_const in *
    | rewrite list_sum_map_id in *
    | rewrite list_sum_map_S in *
    | rewrite list_sum_map_add in *
    | rewrite list_sum_map_mul_l in *
    | rewrite list_sum_map_mul_r in * ].
