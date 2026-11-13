(* Build an input of size n for a function, and call it [reps] times unless [mode] is
   "build" ("calls" otherwise: the two modes run the same code, but for the calls, so
   that the start-up of the program is the same). The calls are repeated so that the
   variations of the start-up, of a few instructions, are divided by [reps]. *)
open Fns

let rec mk_nat n = if n = 0 then O else S (mk_nat (n - 1))
let rec mk_list n = if n = 0 then Nil else Cons (O, mk_list (n - 1))
(* a positive of n bits, all ones; the functions of Pos named in Ex.v are in Coq_Pos
   (Z brings its own copy of Pos, of BinPosDef) *)
let rec mk_pos n = if n <= 1 then XH else XI (mk_pos (n - 1))

let sink = ref (Obj.repr 0)
let reps = 10

let () =
  let fn = Sys.argv.(1) and n = int_of_string Sys.argv.(2) and mode = Sys.argv.(3) in
  let call = mode <> "build" in
  let keep x = sink := Obj.repr (Sys.opaque_identity x) in
  match fn with
  | "add" -> let a = mk_nat n and b = mk_nat 3 in keep (a, b); for _ = 1 to reps do if call then keep (Nat.add a b) done
  | "mul" -> let a = mk_nat n and b = mk_nat 10 in keep (a, b); for _ = 1 to reps do if call then keep (Nat.mul a b) done
  | "mul20" -> let a = mk_nat n and b = mk_nat 20 in keep (a, b); for _ = 1 to reps do if call then keep (Nat.mul a b) done
  | "length" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (length l) done
  | "app" -> let l = mk_list n and m = mk_list 3 in keep (l, m); for _ = 1 to reps do if call then keep (app l m) done
  | "sub" -> let a = mk_nat n and b = mk_nat n in keep (a, b); for _ = 1 to reps do if call then keep (Nat.sub a b) done
  | "eqb" -> let a = mk_nat n and b = mk_nat n in keep (a, b); for _ = 1 to reps do if call then keep (Nat.eqb a b) done
  | "leb" -> let a = mk_nat n and b = mk_nat n in keep (a, b); for _ = 1 to reps do if call then keep (Nat.leb a b) done
  | "ltb" -> let a = mk_nat n and b = mk_nat n in keep (a, b); for _ = 1 to reps do if call then keep (Nat.ltb a b) done
  | "seq" -> let a = mk_nat n in keep a; for _ = 1 to reps do if call then keep (seq O a) done
  | "rev_append" -> let l = mk_list n and m = mk_list 3 in keep (l, m); for _ = 1 to reps do if call then keep (rev_append l m) done
  | "map" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (map_S l) done
  | "fold_left" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (sum_left l) done
  | "fold_right" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (sum_right l) done
  | "filter" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (keep_all l) done
  | "forallb" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (all_true l) done
  | "succ_all" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (succ_all l) done
  | "count_acc" -> let l = mk_list n in keep l; for _ = 1 to reps do if call then keep (count_acc l O) done
  | "pos_add" -> let a = mk_pos n and b = mk_pos n in keep (a, b); for _ = 1 to reps do if call then keep (Coq_Pos.add a b) done
  | "pos_compare" -> let a = mk_pos n and b = mk_pos n in keep (a, b); for _ = 1 to reps do if call then keep (Coq_Pos.compare a b) done
  | "pos_succ" -> let a = mk_pos n in keep a; for _ = 1 to reps do if call then keep (Coq_Pos.succ a) done
  | "pos_eqb" -> let a = mk_pos n and b = mk_pos n in keep (a, b); for _ = 1 to reps do if call then keep (Coq_Pos.eqb a b) done
  | "z_add" -> let a = Zpos (mk_pos n) and b = Zneg (mk_pos n) in keep (a, b); for _ = 1 to reps do if call then keep (Z.add a b) done
  | _ -> failwith "unknown function"
