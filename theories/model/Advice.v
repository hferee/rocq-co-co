(** * Advice on the inequalities left by the proofs of bounds

    The tactics that prove bounds ([cbound], [clinear], ...) reduce a claimed
    bound to inequalities `found <= claimed` between costs, and leave those
    that [lia] and [nia] do not prove. For each of them, [cadvice] looks for
    a counterexample: small values of its variables (natural numbers,
    booleans, binary numbers) that satisfy the hypotheses of its case, and
    for which it is false. A counterexample means that the claimed bound is
    too small; the message gives the cost found and the bound for these
    values. [cbound] calls [cadvice] on the inequalities it leaves.

    The inequalities without a small counterexample may hold, but need facts
    that [lia] and [nia] do not know. [cexplain] suggests some, from the
    shape of the inequality (sizes, powers, costs of functional arguments).

    [cadvice_level] is [0] for no advice, [1] (the default) for the
    counterexamples, and [2] for the suggestions of [cexplain] too. The
    proofs tried by typeclass search (the hints for [Instance .. := _]) use
    the tactics without advice. *)

From Ltac2 Require Import Ltac2 Message.
From Stdlib Require Import PArith NArith ZArith.
Import Constr.Unsafe.

Ltac2 mutable cadvice_level : int := 1.
(** ** Counterexamples *)

(** Small values of the types whose values can be enumerated. They are
    small: the inequalities are computed with unary numbers, and may have
    powers ([pow] makes them smaller still, [small_values_pow]). *)
Ltac2 small_values (ty : constr) : constr list option :=
  if Constr.equal ty constr:(nat) then
    Some [constr:(0); constr:(1); constr:(2); constr:(3)]
  else if Constr.equal ty constr:(bool) then Some [constr:(true); constr:(false)]
  else if Constr.equal ty constr:(positive) then
    Some [constr:(1%positive); constr:(2%positive); constr:(3%positive); constr:(4%positive)]
  else if Constr.equal ty constr:(N) then
    Some [constr:(0%N); constr:(1%N); constr:(2%N); constr:(3%N)]
  else if Constr.equal ty constr:(Z) then
    Some [constr:(0%Z); constr:(1%Z); constr:((-1)%Z); constr:(2%Z); constr:((-2)%Z)]
  else None.

(** A boolean test of a proposition, when it is a comparison of values. *)
Ltac2 test_of (p : constr) : constr option :=
  lazy_match! p with
  | ?a <= ?b => Some constr:(Nat.leb $a $b)
  | ?a < ?b => Some constr:(Nat.ltb $a $b)
  | ?a >= ?b => Some constr:(Nat.leb $b $a)
  | ?a > ?b => Some constr:(Nat.ltb $b $a)
  | @eq nat ?a ?b => Some constr:(Nat.eqb $a $b)
  | @eq bool ?a ?b => Some constr:(Bool.eqb $a $b)
  | @eq positive ?a ?b => Some constr:(Pos.eqb $a $b)
  | @eq N ?a ?b => Some constr:(N.eqb $a $b)
  | @eq Z ?a ?b => Some constr:(Z.eqb $a $b)
  | _ => None
  end.

Ltac2 occurs_var (id : ident) (t : constr) : bool :=
  Bool.neg (Constr.equal (closenl [id] 1 t) t).

(** [t] with the variables [vs] (with their types) replaced by [xs],
    computed. *)
Ltac2 eval_at (vs : (ident * constr) list) (xs : constr list) (t : constr) : constr :=
  let ids := List.map fst vs in
  let body := closenl (List.rev ids) 1 t in
  let f := List.fold_right
             (fun (id, ty) acc => make (Lambda (Constr.Binder.make (Some id) ty) acc)) vs body in
  (* an evaluation that fails (a parameter of the model, ...) gives [tt]:
     neither [true] nor [false] *)
  match Control.case (fun () => Std.eval_vm None (make (App f (Array.of_list xs)))) with
  | Val (r, _) => r
  | Err _ => constr:(tt)
  end.

Ltac2 is_true (t : constr) : bool := Constr.equal t constr:(true).
Ltac2 is_false (t : constr) : bool := Constr.equal t constr:(false).

(** The assignments of small values to [vs], at most [max] of them. *)
Ltac2 rec assignments (vs : (ident * constr list) list) : constr list list :=
  match vs with
  | [] => [[]]
  | (_, xs) :: vs =>
      let rest := assignments vs in
      List.flat_map (fun x => List.map (fun r => x :: r) rest) xs
  end.

Ltac2 rec occurs_const (name : string) (t : constr) : bool :=
  match kind t with
  | Constant c _ =>
      match List.last_opt (Env.path (Std.ConstRef c)) with
      | Some id => String.equal (Ident.to_string id) name
      | None => false
      end
  | App f args => Bool.or (occurs_const name f) (Array.exist (occurs_const name) args)
  | Lambda _ b => occurs_const name b
  | Prod _ b => occurs_const name b
  | Cast c _ _ => occurs_const name c
  | Case _ _ _ s bs => Bool.or (occurs_const name s) (Array.exist (occurs_const name) bs)
  | _ => false
  end.

(** A counterexample to the goal [a <= b]: the values of the variables, and
    those of [a] and [b]. *)
Ltac2 counterexample () : ((ident * constr) list * constr * constr) option :=
  let g := Control.goal () in
  match test_of g with
  | None => None
  | Some test =>
      let hyps := Control.hyps () in
      let vars := List.flat_map
        (fun (id, body, ty) =>
           match body with
           | Some _ => []
           | None =>
               match small_values ty with
               | Some xs =>
                   let xs := if occurs_const "pow" g then List.firstn 3 xs else xs in
                   if occurs_var id g then [(id, ty, xs)] else []
               | None => []
               end
           end) hyps in
      let n := List.length vars in
      if Int.lt 4 n then None else
      let vs := List.map (fun (id, ty, _) => (id, ty)) vars in
      let ids := List.map fst vs in
      (* the hypotheses on these variables: they must hold *)
      let conds := List.flat_map
        (fun (_, body, ty) =>
           match body with
           | Some _ => []
           | None =>
               if List.exist (fun id => occurs_var id ty) ids then [ty] else []
           end) hyps in
      let tests := List.map test_of conds in
      if List.exist (fun t => match t with None => true | Some _ => false end) tests then None
      else
      let tests := List.map (fun t => match t with Some t => t | None => test end) tests in
      let (a, b) := lazy_match! g with
                    | ?a <= ?b => (a, b) | ?a < ?b => (a, b)
                    | ?a >= ?b => (b, a) | ?a > ?b => (b, a) | ?a = ?b => (a, b) end in
      let found := List.find_opt
        (fun xs =>
           Bool.and (List.for_all (fun t => is_true (eval_at vs xs t)) tests)
                    (is_false (eval_at vs xs test)))
        (assignments (List.map (fun (id, _, xs) => (id, xs)) vars)) in
      match found with
      | None => None
      | Some xs =>
          Some (List.combine ids xs, eval_at vs xs a, eval_at vs xs b)
      end
  end.

(** ** Suggestions *)

Ltac2 suggestions (g : constr) : message list :=
  let s := fun str => of_string str in
  List.append
    (if List.exist (fun n => occurs_const n g) ["size_nat"; "size"; "zsize"] then
       [s "It mentions sizes: facts on them may be missing (size_facts for binary numbers, or lemmas such as Nat.lt_le_incl on the hypotheses n < size n)."]
     else [])
  (List.append
    (if occurs_const "pow" g then
       [s "It mentions powers: lia and nia treat them as unknowns; facts such as Nat.pow_le_mono_r or 1 <= 2 ^ n may help."]
     else [])
  (List.append
    (if occurs_const "mul" g then
       [s "It has products: nia may need facts on them, e.g. pose proof (Nat.mul_le_mono_l _ _ k H) for H : a <= b."]
     else [])
  (List.append
    (if occurs_const "cost" g then
       [s "It depends on the costs of a functional argument: it needs a hypothesis bounding them."]
     else [])
    [s "If it is false, the claimed bound is too small: compare the two sides, the left one is the cost found."])))
.

(** ** Messages *)

Ltac2 cat (ms : message list) : message :=
  List.fold_left (fun acc m => concat acc m) (of_string "") ms.

(** A new line, indented. *)
Ltac2 nl () : message := of_string (String.app (String.make 1 (Char.of_int 10)) "  ").

Ltac2 counterexample_message (g : constr) (asg : (ident * constr) list) (a : constr) (b : constr) :
  message :=
  let vals := match asg with
              | [] => of_string ""
              | _ => cat [of_string " for";
                          cat (List.map (fun (id, x) =>
                                 cat [of_string " "; of_ident id; of_string " = "; of_constr x]) asg)]
              end in
  cat [of_string "The inequality "; of_constr g; of_string " is false"; vals;
       of_string ":"; nl (); of_string "the cost found is "; of_constr a;
       of_string ", the claimed bound "; of_constr b; of_string ".";
       nl (); of_string "The claimed bound is too small: increase its constants, or change its shape."].

Ltac2 suggestion_message (g : constr) : message :=
  cat [of_string "The inequality "; of_constr g; of_string " has no small counterexample.";
       cat (List.map (fun m => cat [nl (); m]) (suggestions g))].

(** [cadvice_goal ()]: the advice on the inequality of the goal (all the
    focused goals). *)
Ltac2 cadvice_goal () : unit :=
  if Int.equal cadvice_level 0 then () else
  Control.enter (fun () =>
    let g := Control.goal () in
    match counterexample () with
    | Some (asg, a, b) => print (counterexample_message g asg a b)
    | None => if Int.le 2 cadvice_level then print (suggestion_message g) else ()
    end).

(** [cexplain_goal ()]: the counterexample, or the suggestions, whatever the
    level. *)
Ltac2 cexplain_goal () : unit :=
  Control.enter (fun () =>
    let g := Control.goal () in
    match counterexample () with
    | Some (asg, a, b) => print (counterexample_message g asg a b)
    | None => print (suggestion_message g)
    end).

Ltac cadvice := ltac2:(cadvice_goal ()).

(** ** Timeout

    The tactics used by hand ([cbound], [clinear], [csize], ...) stop after
    [ctimeout] seconds (2 by default; [0] for no timeout), with a message
    that suggests a larger timeout. Change it with
<<
      Ltac2 Set ctimeout := 10.
>>
    ([#[local] Ltac2 Set] for one file). The library turns it off in its
    files: their proofs are not interactive. *)
Ltac2 mutable ctimeout : int := 2.

Ltac2 is_timeout (e : exn) : bool :=
  let s := Message.to_string (Message.of_exn e) in
  let n := String.length s in
  let rec find i :=
    if Int.lt n (Int.add i 6) then false
    else if String.equal (String.sub s i 6) "imeout" then true else find (Int.add i 1) in
  find 0.

(** [ctimed name t]: the Ltac1 tactic [t] within [ctimeout] seconds. *)
Ltac2 ctimed (name : string) (t : Ltac1.t) : unit :=
  if Int.le ctimeout 0 then ltac1:(t |- t) t else
  match Control.case (fun () => ltac1:(n t |- timeout n t) (Ltac1.of_int ctimeout) t) with
  | Val _ => ()
  | Err e =>
      if is_timeout e then
        Control.zero (Tactic_failure (Some (cat
          [of_string name; of_string ": no result within "; of_int ctimeout;
           of_string " s (the timeout).";
           nl (); of_string "The analysis may need more time, or lia and nia may be searching in vain on an inequality.";
           nl (); of_string "Increase the timeout, for example to 10 seconds (0 for none):";
           nl (); of_string "  Ltac2 Set ctimeout := 10."])))
      else Control.zero e
  end.
Ltac cexplain := ltac2:(cexplain_goal ()).
