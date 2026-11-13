(* Build an input of size n for a function, and call it unless [mode] is "build"
   ("calls" otherwise: the two modes have the same length, so that the start-up of
   the program is the same). *)
open Fns

let rec mk_nat n = if n = 0 then O else S (mk_nat (n - 1))
let rec mk_list n = if n = 0 then Nil else Cons (O, mk_list (n - 1))
(* a positive of n bits, all ones *)
let rec mk_pos n = if n <= 1 then XH else XI (mk_pos (n - 1))

let sink = ref (Obj.repr 0)

let () =
  let fn = Sys.argv.(1) and n = int_of_string Sys.argv.(2) and mode = Sys.argv.(3) in
  let call = mode <> "build" in
  let keep x = sink := Obj.repr (Sys.opaque_identity x) in
  match fn with
  | "add" -> let a = mk_nat n and b = mk_nat 3 in keep (a, b); if call then keep (add a b)
  | "mul" -> let a = mk_nat n and b = mk_nat 10 in keep (a, b); if call then keep (mul a b)
  | "mul20" -> let a = mk_nat n and b = mk_nat 20 in keep (a, b); if call then keep (mul a b)
  | "length" -> let l = mk_list n in keep l; if call then keep (length l)
  | "app" -> let l = mk_list n and m = mk_list 3 in keep (l, m); if call then keep (app l m)
  | "map" -> let l = mk_list n in keep l; if call then keep (succ_all l)
  | "fold_left" -> let l = mk_list n in keep l; if call then keep (sum_left l)
  | "pos_add" -> let a = mk_pos n and b = mk_pos n in keep (a, b); if call then keep (Pos.add a b)
  | "pos_compare" -> let a = mk_pos n and b = mk_pos n in keep (a, b); if call then keep (Pos.compare a b)
  | _ -> failwith "unknown function"
