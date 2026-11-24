(** * Closure conversion

    [compile t]: a term convertible to the Rocq term [t], whose abstractions
    become closures (linked environments, as in the CAM; flat closures gave
    larger bounds) and whose matches become case combinators. Closed
    subterms are kept. A closed function needs no closure: its argument is
    its environment ([closed]). The default compiler of [cbound]
    ([Compile]). *)

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Program.Basics PArith NArith ZArith QArith.
From Complexity Require Export CompileCommon.
Import Constr.Unsafe.

(** The type of the bound variable of a lambda, if it is closed. *)
Ltac2 binder_type (b : binder) : constr :=
  let t := Constr.Binder.type b in if is_closed t then t else hole ().

(** Combinators and case combinators: number of type arguments and of
    other arguments. *)
Ltac2 comb_arity (f : constr) : (int * int) option :=
  if Bool.or (List.exist (fun c => Constr.equal f c)
                [constr:(@Lam); constr:(@ehd); constr:(@etl); constr:(@Kc); constr:(@Sc);
                 constr:(@Cc); constr:(@etlc); constr:(@compose); constr:(@consume)])
       (is_case_comb f)
  then
    let t := Constr.type f in
    let n := type_params t in
    Some (n, Int.sub (count_prods t) n)
  else None.

(** Values: variables, closed terms (which are evaluated once, see [conv]),
    lambdas, and partial applications of combinators to values. *)
Ltac2 rec is_value (t : constr) : bool :=
  if is_closed t then true
  else match kind t with
  | Rel _ => true
  | Lambda _ _ => true
  | App f args =>
      match comb_arity f with
      | Some (n, m) =>
          Bool.and (Int.lt (Int.sub (Array.length args) n) m)
            (Array.for_all is_value (Array.sub args n (Int.sub (Array.length args) n)))
      | None => false
      end
  | _ => false
  end.

(** A lambda that needs no closure: [fun x => v x] is [v] (eta) and
    [fun _ => v] is [Kc v], for a value [v] that does not use [x]. *)
Ltac2 simple_lambda (b : binder) (body : constr) : constr option :=
  if Bool.neg (occurs1 body) then
    (if is_value (lower body) then
       Some (mkapp constr:(@Kc) [| hole (); binder_type b; lower body |])
     else None)
  else match kind body with
  | App f args =>
      let n := Array.length args in
      let init := mkapp f (Array.sub args 0 (Int.sub n 1)) in
      if Bool.and (is_rel1 (Array.get args (Int.sub n 1)))
           (Bool.and (Bool.neg (occurs1 init)) (is_value (lower init)))
      then Some (lower init) else None
  | _ => None
  end.

(** ** Reads of the environment

    [env_path base t]: [t] reads the environment [e] of [conv base t] (see
    below) as [etl^q e] ([(q, false)]) or [ehd (etl^q e)] ([(q, true)]): a
    variable, or projections of the environment [Rel base]. Its code is
    [etlc^q] applied to [etl] or [ehd], built once ([path_code]). *)
Ltac2 rec env_path (base : int) (t : constr) : (int * bool) option :=
  match kind t with
  | Rel i => Some (Int.sub i 1, Bool.neg (Int.equal i base))
  | App h args =>
      if Int.equal (Array.length args) 3 then
        match env_path base (Array.get args 2) with
        | Some (q, false) =>
            if Constr.equal h constr:(@etl) then Some (Int.add q 1, false)
            else if Constr.equal h constr:(@ehd) then Some (q, true)
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** [etlc (.. (etlc f))], [q] times. *)
Ltac2 rec etlcs (q : int) (f : constr) : constr :=
  if Int.equal q 0 then f
  else mkapp constr:(@etlc) [| hole (); hole (); hole (); etlcs (Int.sub q 1) f |].

Ltac2 ehd_code () := mkapp constr:(@ehd) [| hole (); hole () |].
Ltac2 etl_code () := mkapp constr:(@etl) [| hole (); hole () |].

(** The code of a read: [etlc^q ehd], [etlc^(q-1) etl], or the identity. *)
Ltac2 path_code (p : int * bool) : constr :=
  let (q, h) := p in
  if h then etlcs q (ehd_code ())
  else if Int.equal q 0 then mklam (binder (hole ())) (mkrel 1)
  else etlcs (Int.sub q 1) (etl_code ()).

Ltac2 mk_compose (f : constr) (g : constr) : constr :=
  mkapp constr:(@compose) [| hole (); hole (); hole (); f; g |].

(** [compose f] of a read: [etlc^q (compose f ehd)], or [etlc^q f]: [f]
    itself for the environment, not [compose f (fun x => x)]. *)
Ltac2 compose_path (f : constr) (p : int * bool) : constr :=
  let (q, h) := p in
  if h then etlcs q (mk_compose f (ehd_code ())) else etlcs q f.

(** [base] shifted by [k] binders ([0]: no base). *)
Ltac2 shift (base : int) (k : int) : int :=
  if Int.equal base 0 then 0 else Int.add base k.

(** The number of reads, in [t], of the variables above [Rel k] (those
    bound outside [t] and deeper than [k]), on the path of [t] that reads
    the most: only one branch of a match runs. *)
Ltac2 rec count_above (k : int) (t : constr) : int :=
  match kind t with
  | Rel n => if Int.lt k n then 1 else 0
  | App f args => Array.fold_left (fun acc u => Int.add acc (count_above k u)) (count_above k f) args
  | Lambda _ body => count_above (Int.add k 1) body
  | LetIn _ v body => Int.add (count_above k v) (count_above (Int.add k 1) body)
  | Case _ _ _ scrut branches =>
      Int.add (count_above k scrut)
        (Array.fold_left (fun acc u => let n := count_above k u in if Int.lt acc n then n else acc) 0 branches)
  | Cast c _ _ => count_above k c
  | _ => 0
  end.

(** [conv base t]: a closed term [u] such that [u e] is convertible to [t]
    where each variable [Rel i] is the value at position [i - 1] of the
    environment [e] (the latest bound first), except [Rel base] (if
    [base > 0]), which is the environment at position [base - 1] itself
    (the argument of a closed function, [closed]). A read of [e] is
    [etlc^q] applied to [ehd] or [etl] ([env_path]). The terms that do not
    use [e] are closed, and evaluated once ([Kc]); an application is [Sc],
    or [compose] (B) and [Cc] when one of its parts is closed. A lambda becomes a closure [Lam c e]: the
    environment [e] extended with the argument is the one of its body [c]
    ([simple_lambda] needs no closure). A match becomes the application of
    its case combinator to the code of its branches and of its matched
    value ([case_code]): no closure. *)
Ltac2 rec conv (base : int) (t : constr) : constr :=
  if is_closed t then mkapp constr:(@Kc) [| hole (); hole (); closed t |]
  else match env_path base t with
  | Some p => path_code p
  | None =>
  match kind t with
  | App f args =>
      let n := Array.length args in
      let last := Array.get args (Int.sub n 1) in
      let init := mkapp f (Array.sub args 0 (Int.sub n 1)) in
      if is_closed init then
        match env_path base last with
        | Some p => compose_path (closed init) p
        | None => mk_compose (closed init) (conv base last)
        end
      else if is_closed last then
        mkapp constr:(@Cc) [| hole (); hole (); hole (); conv base init; closed last |]
      else mkapp constr:(@Sc) [| hole (); hole (); hole (); conv base init; conv base last |]
  | Lambda b body =>
      match simple_lambda b body with
      | Some u => conv base u
      | None => mkapp constr:(@Lam) [| hole (); binder_type b; hole (); conv (shift base 1) body |]
      end
  | Case ci _ _ scrut branches => case_code base ci scrut branches
  | Fix _ _ _ _ =>
      fail_msg "compile: a local fixpoint uses variables of the function: make it a function of them, closed, and declare its bound first"
  | _ => fail_msg "compile: unsupported term (dependent match, ...)"
  end
  end

(** The code of a match, for its environment [e]: the case combinator
    applied to the code of each branch, in [e] extended with the arguments
    of the constructor, and to the code of the matched value. *)
with case_code (base : int) (ci : case) (scrut : constr) (branches : constr array) : constr :=
  let data := Ind.data (Case.inductive ci) in
  let nargs := Array.to_list (Ind.constructor_nargs data) in
  let comb := mkapp_l (case_comb_of (Case.inductive ci)) (holes (Int.add (Ind.nparams data) 2)) in
  (* the matched variable, the top of the environment, unused in the
     branches: consumed ([consume]) *)
  let bodies := List.mapi (fun j a => (a, peel a (Array.get branches j))) nargs in
  (* consuming costs [c_consume + c_clo + c_Kc] instead of [c_ehd], and
     saves [c_etlc] on each read of a variable below the matched one: done
     when a run of a branch reads at least two of them *)
  let consumed :=
    Bool.and (Bool.and (is_rel1 scrut) (Bool.neg (Int.equal base 1)))
      (Bool.and (List.for_all (fun (a, b) => noccurn (Int.add a 1) b) bodies)
         (List.exist (fun (a, b) => Int.le 2 (count_above (Int.add a 1) b)) bodies)) in
  if consumed then
    mkapp constr:(@consume) [| hole (); hole (); hole ();
                                mkapp_l comb (consumed_branch_codes base ci branches) |]
  else mkapp_l comb (List.append (branch_codes base ci branches) [conv base scrut])

with branch_codes (base : int) (ci : case) (branches : constr array) : constr list :=
  List.mapi (fun j a => conv (shift base a) (peel a (Array.get branches j)))
    (Array.to_list (Ind.constructor_nargs (Ind.data (Case.inductive ci))))

(** The branches without the matched variable [Rel 1], which they do not use. *)
with consumed_branch_codes (base : int) (ci : case) (branches : constr array) : constr list :=
  let base' := if Int.equal base 0 then 0 else Int.sub base 1 in
  List.mapi (fun j a => conv (shift base' a) (substnl [dummy ()] a (peel a (Array.get branches j))))
    (Array.to_list (Ind.constructor_nargs (Ind.data (Case.inductive ci))))

(** [closed t], for a closed term [t]. A closed lambda needs no closure:
    its code, with its argument as the environment ([conv] with [base]
    [1]), is the function itself. A closed [fun x => match x with ... end]
    is thus the case combinator, with [x] as its environment, read by the
    identity;
    a closed [fun x y => b] is [Lam c], [c] being the code of [b] in the
    environment [ECons x y]. *)
with closed (t : constr) : constr :=
  match kind t with
  | Lambda b body =>
      (* a lifted local fixpoint is a constant, whose bound is given *)
      if is_lifted_fix t then t else
      match simple_lambda b body with
      | Some u => closed u
      | None => conv 1 body
      end
  | App f args => mkapp (closed f) (Array.map closed args)
  | Case ci _ _ scrut branches => mkapp (case_code 0 ci scrut branches) [| constr:(tt) |]
  | _ => t
  end.

(** [compile t]: a term convertible to [t], built from combinators. *)
Ltac2 compile (t : constr) : constr := closed (decase t).

(** The compiler, for [cbound] ([Compile]). *)
Ltac2 closure_compile_goal () := compile_goal_with compile.
