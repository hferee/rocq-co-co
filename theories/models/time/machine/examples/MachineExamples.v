(** * Running times on the environment machine for L

    Bounds in steps of the environment machine ([MachineCostModel], whose
    instance is [LMachine]). [Nat.add] costs [189 n + 140] steps, about
    [16] times its cost in combinator applications ([12 n + 9],
    [TimeCostModel]): the case analyses ([c_case_nat = 33],
    [c_case_list = 46]) and the unfoldings ([c_fix = 36]) are the largest
    part. *)

From Complexity Require Import MachineCostModel HOListComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

(** [map S], and [fold_left (fun a _ => S a)], as fixpoints. *)
Fixpoint succ_all (l : list nat) : list nat :=
  match l with [] => [] | x :: t => S x :: succ_all t end.
Fixpoint count_acc (l : list nat) (a : nat) : nat :=
  match l with [] => a | _ :: t => count_acc t (S a) end.

Module MachineExamples (Import Machine : MachineTimeCostModel).

  Include CcombineTactics Machine.

  (** [cbound], with the case analysis of a list before the arithmetic,
      which is slow on the goals before it ([nia], with the large constants
      of the machine). *)
  Local Ltac cbound_list :=
    ltac2:(cbound_start ()); csimpl; bo_split; destr_inputs; ccases; cunit; cfold;
    try ccombine_case; first [reflexivity | carith].

  Global Instance Nat_add_machine : Machine.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (189 * val cn + 140) >|) := _.

  Global Instance length_machine {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Machine.ComplexityBound (@length A)
    (fun cl => (223 * length (val cl) + 107) >|) := _.

  (** Tail-recursive, with an accumulator: tail calls are cheaper on the
      machine (no frame), but [count_acc] costs more per element ([342])
      than [length] ([223]): its accumulator is a second argument, so that
      each recursive call pays the partial application of the function
      ([43]). *)
  Global Instance count_acc_machine : Machine.ComplexityBound count_acc
    (fun cl => 43 +> fun ca => (342 * length (val cl) + 104) >|) := _.

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

  (** ** Higher-order functions, as in [HOListComplexity] *)

  Global Instance map_machine {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Machine.ComplexityBound (@map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 338 * length (val cl) + 120)
         +> map (fun x => res (pot cf x)) (ccombine cl)).
  Proof. cbound_list. Qed.

  Global Instance filter_machine {A CA} `{Repr A CA} :
    Machine.ComplexityBound (@filter A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 401 * length (val cl) + 120)
         +> ListFacts.filter_map (fun x => if val cf (val x) then Some (pot x) else None) (ccombine cl)).
  Proof. cbound_list. Qed.
End MachineExamples.
