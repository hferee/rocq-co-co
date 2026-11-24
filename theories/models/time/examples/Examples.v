(** * Examples: what [ComplexityBound] means

    [ComplexityBound f c] is a property of the function [f], not of a
    particular program computing it: it reads "[f] is computable within
    [c]" (see [CostModel]). The examples below show this, and how the cost
    model still accounts for the running time of the programs it
    analyses. *)

From Complexity Require Import TimeStdlib.
From Stdlib Require Import List Recdef Lia.
Import ListNotations.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

Definition slow_id (n : nat) : nat := Nat.iter (2 ^ n) (fun x => x) n.

Lemma slow_id_id n : slow_id n = n.
Proof. unfold slow_id. induction (2 ^ n); cbn; auto. Qed.

Fixpoint tower (n : nat) : nat -> nat :=
  match n with O => fun x => x | S k => let c := tower k in compose c c end.

Definition tower_eval (n : nat) : nat := tower n 0.

Module Examples (Import Time : TimeStdlib).

  (** ** Conversion

      [ComplexityBound] is a predicate on Rocq values: it cannot distinguish
      convertible terms. A thousand iterations of the identity cost as much
      as the identity. *)
  Example iter_conv : Time.ComplexityBound (fun n : nat => Nat.iter 1000 (fun x => x) n)
    (fun cn => 1 +> pot cn).
  Proof. exact (@id_complexity nat unit _). Qed.

  (** ** Extensionality

      [fix_complexity] makes [ComplexityBound] extensional: a function is a
      fixpoint of the functional that ignores its recursive calls and
      returns any function pointwise equal to it ([fix_closed_complexity],
      for a closed function). *)
  Lemma complexity_ext {A B CA CB} `{Repr A CA} {RB : Repr B CB} (ar : Arity B) `{!PwExt RB ar}
    (f g : A -> B) (cg : ℂI A CA -> ℂO CB) :
    (forall a, pw_eq ar (f a) (g a)) -> Time.ComplexityBound g cg ->
    Time.ComplexityBound f (fun ca => 2 ⊕ cg ca).
  Proof.
    intros Hfg Hg.
    eapply (fix_closed_complexity ar f (fun _ => g) (fun _ => 1 +> cg));
      [cfix_pos | exact Hfg | apply constant_complexity, Hg |].
    apply bound_order_arr. intros ca _. cbn. split; [autounfold with costs; lia | reflexivity].
  Qed.

  (** [slow_id n] takes [2 ^ n] steps, but it is the identity. *)
  Lemma slow_id_complexity : Time.ComplexityBound slow_id (fun _ => 3 >|).
  Proof.
    capply. apply (complexity_ext (ar_val nat) slow_id (fun n => n)).
    - exact slow_id_id.
    - exact (@id_complexity nat unit _).
    Unshelve. bo_split; destr_inputs; cbn; autounfold with costs; lia.
  Qed.

  (** ** Every application is charged

      [tower n x] performs [2 ^ n] compositions. Building [tower n] costs a
      linear number of steps, but applying it costs [3 * 2 ^ n - 1]. *)
  Global Instance tower_complexity : Time.ComplexityBound tower
    (fun cn => (17 * val cn + 6) +>
     fun cx => (2 * 2 ^ val cn - 1) >|).
  Proof. cbound. all: assert (2 ^ cn <> 0) by (apply Nat.pow_nonzero; lia); lia. Qed.

  Lemma tower_eval_complexity : Time.ComplexityBound tower_eval
    (fun cn => (17 * val cn + 2 * 2 ^ val cn + 8) >|).
  Proof. cbound. all: assert (2 ^ cn <> 0) by (apply Nat.pow_nonzero; lia); lia. Qed.

  (** ** Local fixpoints

      [cbound] analyses a fixpoint at the head of a definition, possibly
      under the lambdas of its parameters. A fixpoint elsewhere in the body
      (a [let fix], a worker applied to its initial arguments, a [fix]
      under a constructor) is closed: it is a constant of the compiled
      code, as any closed term. [cbound] does not analyse it, but asks for
      its bound, printing the fixpoint; once the bound is declared, as a
      hypothesis ([assert ... by cbound]) or as an instance, it is read
      from the context. A local fixpoint that uses variables of the
      function is lifted to a function of them, closed ([count_from]). *)

  (** The length of a list, by a worker with an accumulator, in a
      [let fix]: the bound of the worker is a hypothesis of the proof. *)
  Definition length_acc (l : list nat) : nat :=
    let fix go (l : list nat) (acc : nat) := match l with [] => acc | _ :: t => go t (S acc) end in
    go l 0.

  Lemma length_acc_complexity : Time.ComplexityBound length_acc
    (fun cl => (28 * length (val cl) + 13) >|).
  Proof.
    Fail cbound. (* cbound fails but tells us what to do: assert and prove
      the complexity bound of the local fixpoint first. *)
    assert (Hgo : Time.ComplexityBound
      (fix go (l : list nat) (acc : nat) := match l with [] => acc | _ :: t => go t (S acc) end)
      (fun cl => 4 +> fun ca => (28 * length (val cl) + 6) >|)) by cbound.
    cbound.
  Qed.

  (** The same worker, lifted to a top-level fixpoint whose bound is an
      instance: [length_acc] is convertible to the wrapper. *)
  Fixpoint length_go (l : list nat) (acc : nat) : nat :=
    match l with [] => acc | _ :: t => length_go t (S acc) end.

  Global Instance length_go_complexity : Time.ComplexityBound length_go
    (fun cl => 4 +> fun ca => (21 * length (val cl) + 5) >|).
  Proof. cbound. Qed.

  Lemma length_acc_lifted_complexity : Time.ComplexityBound length_acc
    (fun cl => (21 * length (val cl) + 12) >|).
  Proof. change length_acc with (fun l => length_go l 0). cbound. Qed.

  (** A worker applied to its initial arguments. *)
  Definition rev_acc (l : list nat) : list nat :=
    (fix go (l acc : list nat) := match l with [] => acc | x :: t => go t (x :: acc) end) l [].

  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma rev_acc_complexity : Time.ComplexityBound rev_acc
    (fun cl => (33 * length (val cl) + 13) >|).
  Proof.
    assert (Hgo : Time.ComplexityBound
      (fix go (l acc : list nat) := match l with [] => acc | x :: t => go t (x :: acc) end)
      (fun cl => 4 +> fun cacc => (33 * length (val cl) + 6) >|)) by cbound.
    cbound.
  Qed.
  *)

  (** A fixpoint under a constructor, with the bound of the fixpoint
      declared as an instance. *)
  Definition double_length (l : list nat) : nat :=
    S ((fix dbl (l : list nat) : nat := match l with [] => 0 | _ :: t => S (S (dbl t)) end) l).

  Global Instance dbl_complexity : Time.ComplexityBound
    (fix dbl (l : list nat) : nat := match l with [] => 0 | _ :: t => S (S (dbl t)) end)
    (fun cl => (15 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Lemma double_length_complexity : Time.ComplexityBound double_length
    (fun cl => (15 * length (val cl) + 10) >|).
  Proof. cbound. Qed.

  (** A local fixpoint that uses an argument of the function, [n]: it is
      lifted to the function [fun n => fix go ...] of [n], whose bound is
      declared ([cbound] prints this function when its bound is missing). *)
  Definition count_from (n : nat) (l : list nat) : nat :=
    let fix go (l : list nat) := match l with [] => n | _ :: t => S (go t) end in go l.

  Lemma count_from_complexity : Time.ComplexityBound count_from
    (fun cn => 1 +> fun cl => (16 * length (val cl) + 13) >|).
  Proof.
    assert (Hgo : Time.ComplexityBound
      (fun n : nat => fix go (l : list nat) : nat := match l with [] => n | _ :: t => S (go t) end)
      (fun cn => 1 +> fun cl => (16 * length (val cl) + 8) >|)) by cbound.
    cbound.
  Qed.

  (** ** Well-founded recursion

      A function defined by well-founded recursion ([Function], [Program
      Fixpoint], Equations) is not a [fix] on its arguments: its body is a
      fixpoint on a proof of accessibility, with its results in a subset
      type. The fixpoint rule only needs its unfolding equation, and does
      not need the termination argument: [cbound] uses the equation
      [div_equation] that [Function] proves ([crec_eq_auto]; [crec_eq e]
      for another equation [e]). The facts of the tests of [div], [m <> 0]
      and [m <= n], bound the cost of the recursive call on [n - m]. *)
  Function div (n m : nat) {measure id n} : nat :=
    if m =? 0 then 0 else if n <? m then 0 else S (div (n - m) m).
  Proof.
    intros n m Hm Hlt. unfold id. apply Nat.eqb_neq in Hm. apply Nat.ltb_ge in Hlt. lia.
  Defined.

  Lemma div_complexity : Time.ComplexityBound div
    (fun cn => 4 +> fun cm => ((val cn + 1) * (21 * val cm + 21 * val cn + 86)) >|).
  Proof. cbound. Qed.
End Examples.
