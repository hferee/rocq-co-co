(** The functions measured in assembly (tools/bounds/asm/measure.py), extracted
    to OCaml as they are defined in the standard library, and the examples of
    machine/MachineExamples.v. *)
From Stdlib Require Import List PArith ZArith.
From Corelib Require Extraction.
Extraction Language OCaml.
Definition map_S (l : list nat) := map S l.
Definition sum_left (l : list nat) := fold_left (fun a _ => S a) l 0.
Definition sum_right (l : list nat) := fold_right (fun _ a => S a) 0 l.
Definition keep_all (l : list nat) := filter (fun _ => true) l.
Definition all_true (l : list nat) := forallb (fun _ => true) l.
(** As in machine/MachineExamples.v. *)
Fixpoint succ_all (l : list nat) : list nat :=
  match l with nil => nil | x :: t => S x :: succ_all t end.
Fixpoint count_acc (l : list nat) (a : nat) : nat :=
  match l with nil => a | _ :: t => count_acc t (S a) end.
Extraction "fns" Nat.add Nat.mul Nat.sub Nat.eqb Nat.leb Nat.ltb length app seq
  rev_append map_S sum_left sum_right keep_all all_true succ_all count_acc
  Pos.succ Pos.add Pos.compare Pos.eqb Z.add.
