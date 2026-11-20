(** * Running times on the environment machine for L

    Bounds in steps of the environment machine ([MachineCostModel], whose
    instance is [LMachine]). [Nat.add] costs [199 n + 145] steps, about
    [14] times its cost in combinator applications ([14 n + 10],
    [TimeCostModel]): the case analyses ([c_case_nat = 33],
    [c_case_list = 46]) and the unfoldings ([c_fix = 36]) are the largest
    part. *)

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
    (fun cn => 1 +> fun cm => (199 * val cn + 145) >|) := _.

  Global Instance length_machine {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Machine.ComplexityBound (@length A)
    (fun cl => (238 * length (val cl) + 107) >|) := _.

  (** Tail-recursive, with an accumulator: tail calls are cheaper on the
      machine (no frame), but [count_acc] and [rev_append] cost more per
      element ([377], [433]) than [length] and [succ_all] ([238], [305]):
      their accumulator is a second argument, so that each recursive call
      pays the partial application of the function ([43]). *)
  Global Instance count_acc_machine : Machine.ComplexityBound count_acc
    (fun cl => 43 +> fun ca => (377 * length (val cl) + 109) >|) := _.

  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance app_machine {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Machine.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm => (294 * length (val cl) + 158) >|) := _.
  *)

  (** Tail-recursive, with an accumulator. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance rev_append_machine {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Machine.ComplexityBound (@rev_append A)
    (fun cl => 43 +> fun cm => (433 * length (val cl) + 109) >|) := _.
  *)

  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance succ_all_machine : Machine.ComplexityBound succ_all
    (fun cl => (305 * length (val cl) + 107) >|) := _.
  *)
End MachineExamples.
