From Stdlib Require Export Classes.Morphisms Classes.RelationClasses
  Program.Equality Program.Basics.

(* Experiments to reason on functions of arbitrary arity. *)

(* Type with at least n arguments *)
Inductive Nary : nat -> Type -> Type :=
| Nary_O : forall T, Nary O T
| Nary_S : forall A B n, Nary n B -> Nary (S n) (A -> B).

Create HintDb nary.
Global Hint Constructors Nary : nary.

Lemma Nary_S_inv n T: Nary (S n) T -> Nary n T.
Proof.
intro Ht. dependent induction Ht.
destruct n as [|n]; constructor. now apply IHHt.
Qed.

(* Instance Nary_monotone :
  Proper ((ge) ==> (eq) ==> (impl)) Nary.
Proof.
  intros n m Hnm ? t ? Ht. subst. revert m Hnm t Ht.
  induction n; intros m Hnm t Ht.
  - inversion Hnm. constructor.
  - inversion Hnm; subst.
    + trivial.
    + apply IHn. trivial. now apply Nary_S_inv.
Qed.
 *)

(* Type whose k-th argument is T0 *)
Inductive Nary_with_arg : nat -> Type -> Type -> Type :=
| Nary_with_arg_0 : forall T T0, Nary_with_arg O T0 (T0 -> T)
| Nary_with_arg_S : forall A B T0 k,
    Nary_with_arg k T0 B -> Nary_with_arg (S k) T0 (A -> B).

Lemma Nary_with_arg_Nary n T0 T: Nary_with_arg n T0 T -> Nary (S n) T.
Proof.
intro Ht; dependent induction Ht; now repeat constructor.
Qed.

(* Idea : if a fixpoint is structural on the nth-argument, swap
  it with the first one *)


Fixpoint Nary_flip_aux n T0 T (H : Nary (S n) T) {struct H} : Type * Type :=
match H with
| Nary_S A B 0 HB => (A, T0 -> B) (* Should not happen *)
| Nary_S A B (S n) HB => let (T1, T2) := Nary_flip_aux n T0 B HB in
    (T1, A -> T2)
end.

(* (* TODO: cleaner definition with Equations? *)

Equations Nary_flip_aux (n : nat) (T0 T : Type) (H : Nary (S n) T) : Type * Type
 :=
Nary_flip_aux 0 T0 T (Nary_S A B n HB) := (A, T0 -> B);
Nary_flip_aux (S n) T0 _ (Nary_S A B n HB) :=
  let (T1, T2) := Nary_flip_aux n T0 B HB in
    (T1, A -> T2). *)

(* Definition Nary_flip_aux (n : nat) (T0 T : Type) (H : Nary (S n) T) : Type * Type.
Proof.
revert T0 T H. induction n as [|n]; intros T0 T H.
- inversion H. exact (A, T0 -> B).
- inversion H. destruct (IHn T0 B X) as [T1 T2].
  exact (T1, A -> T2).
Defined.
 *)
(* Swaps the argument type at position n with that at position 0. *)
(* Definition Nary_flip (n : nat) (T : Type) (H : Nary (S n) T) : Type.
Proof.
destruct n as [|n].
- exact T.
- inversion H. destruct (Nary_flip_aux n A B) as [T1 T2].
  + assumption.
  + exact (T1 -> T2).
Defined. *)

Definition Nary_flip n T (H : Nary (S n) T) : Type :=
match H with
| Nary_S A B 0 HB => T
| Nary_S A B (S n) HB => let (T1, T2) := Nary_flip_aux n A B HB in T1 -> T2
end.

(* Example *)

(* Eval compute in Nary_flip 2 (list bool -> bool -> list nat -> list (list nat)) (ltac:(repeat constructor)). *)


Lemma Nary_flip_aux_Nary n T0 T H: Nary (S n) (snd (Nary_flip_aux n T0 T H)).
Proof.
revert T H. induction n as [|n]; intros T H.
- dependent destruction H. simpl. now constructor.
- dependent destruction H. simpl. cbn.
  specialize (IHn B H).
  destruct (Nary_flip_aux n T0 B H) as [T1 T2]. simpl.
  constructor; assumption.
Qed.

Lemma Nary_flip_Nary n T (H : Nary (S n) T): Nary (S n) (Nary_flip n T H).
Proof.
destruct n as [|n]; dependent destruction H; simpl.
- now constructor.
- cbn. assert (H0 := Nary_flip_aux_Nary n A B H).
  destruct Nary_flip_aux as [T1 T2]. constructor. assumption.
Qed.

From Equations Require Import Equations.

(* The corresponding functor *)
Equations nary_flip_aux n T0 T (H : Nary (S n) T) (f : T0 -> T) :
  let (T1, T2) := Nary_flip_aux n T0 T H in T1 -> T2 :=
nary_flip_aux 0 T0 T (Nary_S A B _ HB) f => flip f;
nary_flip_aux (S n) T0 T (Nary_S A B _ HB) f =>
  let g := fun a => nary_flip_aux n T0 B HB (flip f a) in _
.
Next Obligation.
assert (g := fun a => nary_flip_aux n T0 B HB (flip f a)).
destruct Nary_flip_aux. exact (flip g).
Defined.


(* Definition nary_flip_aux n T0 T (H : Nary (S n) T) (f : T0 -> T) :
  let (T1, T2) := Nary_flip_aux n T0 T H in T1 -> T2.
Proof.
revert T H f. induction n as [|n]; intros T H f.
- dependent destruction H. simpl. exact (flip f).
- dependent destruction H. simpl. cbn.
  specialize (IHn _ H). destruct Nary_flip_aux as [T1 T2].
  intros t1 a. exact (IHn (flip f a) t1).
  fun t1 a => 
Defined.
 *)
Definition nary_flip n {T} (H : Nary (S n) T) (f : T) : Nary_flip n T H.
Proof.
destruct n; simpl.
- dependent destruction H. subst. simpl. exact f.
- dependent destruction H. simpl. cbn.
  assert (g := nary_flip_aux n A B H f).
  destruct Nary_flip_aux. exact g.
Defined.

Example flip_pow : nat -> nat -> nat := nary_flip 1 (ltac:(auto with nary)) Nat.pow.

(* Eval compute in flip_pow 3 5. *)

