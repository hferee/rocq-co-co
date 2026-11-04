(** * Examples: what [ComplexityBound] means

    [ComplexityBound f c] is a property of the function [f], not of a
    particular program computing it: it reads "[f] is computable within
    [c]" (see [CostModel]). The examples below show this, and how the cost
    model still accounts for the real running time of the programs it
    analyses.

    - Conversion: convertible terms have the same bounds.
    - Extensionality: pointwise-equal functions have the same bounds, up to
      a constant ([complexity_ext]). Hence [slow_id], which iterates the
      identity [2 ^ n] times, has a constant bound.
    - Every application is charged ([TimeCombinators]): [tower n] is
      the identity, as [2 ^ n] compositions of the identity built with [n]
      duplications, and its bound is exponential. With a free [compose],
      it used to get a constant bound, far below its running time. *)

From Complexity Require Import TimeCostModel CostModel TimeBasic TimeDatatypes Combinators
  Compile TimeCombinators TimeFix.
From Stdlib Require Import Program.Basics Arith Lia.

Definition slow_id (n : nat) : nat := Nat.iter (2 ^ n) (fun x => x) n.

Lemma slow_id_id n : slow_id n = n.
Proof. unfold slow_id. induction (2 ^ n); cbn; auto. Qed.

Fixpoint tower (n : nat) : nat -> nat :=
  match n with O => fun x => x | S k => let c := tower k in compose c c end.

Definition tower_eval (n : nat) : nat := tower n 0.

Module Examples (Import M : TimeCostModel).

  (** ** Conversion

      [ComplexityBound] is a predicate on Rocq values: it cannot distinguish
      convertible terms. A thousand iterations of the identity cost as much
      as the identity. *)
  Example iter_conv : ComplexityBound (fun n : nat => Nat.iter 1000 (fun x => x) n)
    (fun cn => 1 ⋉ pot cn).
  Proof. exact (@id_complexity nat unit _). Qed.

  (** ** Extensionality

      [fix_complexity] makes [ComplexityBound] extensional: a function is a
      fixpoint of the functional that ignores its recursive calls and
      returns any function pointwise equal to it. *)
  Lemma complexity_ext {A B CA CB} `{Repr A CA} `{Repr B CB} (ar : Arity B) (f g : A -> B) (cg : ℂI A CA -> ℂO CB) :
    (forall a, pw_eq ar (f a) (g a)) -> ComplexityBound g cg ->
    ComplexityBound f (fun ca => 2 ⊕ cg ca).
  Proof.
    intros Hfg Hg.
    eapply (fix_complexity ar f (fun _ => g) (fun _ => 1 ⋉ cg));
      [exact Hfg | apply constant_complexity, Hg |].
    apply bound_order_arr. intro ca. cbn. split; [lia | reflexivity].
  Qed.

  (** [slow_id n] takes [2 ^ n] steps, but it is the identity. *)
  Lemma slow_id_complexity : ComplexityBound slow_id (fun _ => 3 ⋉ tt).
  Proof.
    capply. apply (complexity_ext (ar_val nat) slow_id (fun n => n)).
    - exact slow_id_id.
    - exact (@id_complexity nat unit _).
    Unshelve. bo_split; destr_inputs; cbn; lia.
  Qed.

  (** ** Every application is charged

      [tower n x] performs [2 ^ n] compositions. Building [tower n] costs a
      linear number of steps, but applying it costs [3 * 2 ^ n - 1]. *)
  Global Instance tower_complexity : ComplexityBound tower
    (fun cn => (20 * val cn + 7) ⋉
     fun cx => (3 * 2 ^ val cn - 1) ⋉ tt).
  Proof. cbound. all: assert (2 ^ cn <> 0) by (apply Nat.pow_nonzero; lia); lia. Qed.

  Lemma tower_eval_complexity : ComplexityBound tower_eval
    (fun cn => (20 * val cn + 3 * 2 ^ val cn + 10) ⋉ tt).
  Proof. cbound. all: assert (2 ^ cn <> 0) by (apply Nat.pow_nonzero; lia); lia. Qed.
End Examples.
