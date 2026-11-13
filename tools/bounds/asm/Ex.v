(** The functions measured in assembly (tools/bounds/asm/measure.py), extracted
    to OCaml as they are defined in the standard library. *)
From Stdlib Require Import List PArith.
From Corelib Require Extraction.
Extraction Language OCaml.
Definition succ_all (l : list nat) := map S l.
Definition sum_left (l : list nat) := fold_left (fun a _ => S a) l 0.
Extraction "fns" Nat.add Nat.mul length app succ_all sum_left Pos.add Pos.compare.
