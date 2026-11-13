(** * Running times on the environment machine for L

    Bounds in the cost model of the environment machine ([MachineCostModel],
    whose instance is [LMachine]): in steps of the machine. The functions
    are compiled to the combinators, as in the time model, and each
    combinator costs at most [c_step = 16] steps of the machine: [Nat.add]
    costs [243 n + 173] steps, about [17] times its cost in combinator
    applications ([14 n + 10], [TimeCostModel]).

    Tail calls are cheaper on the machine (no frame), but this is a small
    part of the costs: [count_acc] and [rev_append], tail-recursive, cost
    more per element ([479], [550]) than [length] and [succ_all] ([290],
    [380]), because their accumulator is a second argument: each recursive
    call pays the partial application of the function ([54]). *)

From Complexity Require Import MachineCostModel.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** [map S], and [fold_left (fun a _ => S a)], as fixpoints. *)
Fixpoint succ_all (l : list nat) : list nat :=
  match l with [] => [] | x :: t => S x :: succ_all t end.
Fixpoint count_acc (l : list nat) (a : nat) : nat :=
  match l with [] => a | _ :: t => count_acc t (S a) end.

Module MachineExamples (Import Machine : MachineTimeCostModel).

  Global Instance Nat_add_machine : Machine.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (243 * val cn + 173) >|) := _.

  Global Instance length_machine {A} `{Ground A} : Machine.ComplexityBound (@length A)
    (fun cl => (290 * length (val cl) + 133) >|) := _.

  (** Tail-recursive, with an accumulator. *)
  Global Instance count_acc_machine : Machine.ComplexityBound count_acc
    (fun cl => 54 +> fun ca => (479 * length (val cl) + 130) >|) := _.

  Global Instance app_machine {A} `{Ground A} : Machine.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm => (361 * length (val cl) + 186) >|) := _.

  (** Tail-recursive, with an accumulator. *)
  Global Instance rev_append_machine {A} `{Ground A} : Machine.ComplexityBound (@rev_append A)
    (fun cl => 54 +> fun cm => (550 * length (val cl) + 130) >|) := _.

  Global Instance succ_all_machine : Machine.ComplexityBound succ_all
    (fun cl => (380 * length (val cl) + 133) >|) := _.
End MachineExamples.
