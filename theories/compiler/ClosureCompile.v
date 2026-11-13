(** * Closure conversion

    [compile t] rewrites the lambda-term [t] into a convertible term built
    from the combinators of [Combinators], by closure conversion: every
    lambda becomes a closure, i.e. its code applied to the environment where
    it is built. Matches become case combinators. A closed function needs no
    closure: its argument is its environment ([closed]). It only uses
    conversion: the goal before and after is the same proposition. This is
    the default compiler of [cbound] ([Compile]). *)

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Program.Basics PArith NArith ZArith QArith.
From Complexity Require Export CompileCommon.
Import Constr.Unsafe.

(** The variable at position [p] of an environment: [ehd (etl^p e)]. *)
Ltac2 rec access (p : int) : constr :=
  if Int.equal p 0 then mkapp constr:(@ehd) [| hole (); hole () |]
  else mkapp constr:(@compose)
         [| hole (); hole (); hole (); access (Int.sub p 1); mkapp constr:(@etl) [| hole (); hole () |] |].

(** The type of the bound variable of a lambda, if it is closed. *)
Ltac2 binder_type (b : binder) : constr :=
  let t := Constr.Binder.type b in if is_closed t then t else hole ().

(** Combinators and case combinators: number of type arguments and of
    other arguments. *)
Ltac2 comb_arity (f : constr) : (int * int) option :=
  if Bool.or (List.exist (fun c => Constr.equal f c)
                [constr:(@Lam); constr:(@ehd); constr:(@etl); constr:(@Kc); constr:(@Sc);
                 constr:(@Cc); constr:(@compose)])
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

(** The environment at position [p] of an environment: [etl^p e] ([Ic]
    for [p = 0]). *)
Ltac2 rec base_access (p : int) : constr :=
  if Int.equal p 0 then mkapp constr:(@Ic) [| hole () |]
  else if Int.equal p 1 then mkapp constr:(@etl) [| hole (); hole () |]
  else mkapp constr:(@compose)
         [| hole (); hole (); hole (); mkapp constr:(@etl) [| hole (); hole () |];
            base_access (Int.sub p 1) |].

(** [base] shifted by [k] binders ([0]: no base). *)
Ltac2 shift (base : int) (k : int) : int :=
  if Int.equal base 0 then 0 else Int.add base k.

(** [conv base t]: a closed term [u] such that [u e] is convertible to [t]
    where each variable [Rel i] is the value at position [i - 1] of the
    environment [e] (the latest bound first), except [Rel base] (if
    [base > 0]), which is the environment at position [base - 1] itself
    (the argument of a closed function, [closed]). The terms that do not use [e] are closed, and evaluated
    once ([Kc]); an application is [Sc], or [compose] (B) and [Cc] when one
    of its parts is closed. A lambda becomes a closure [Lam c e]: the
    environment [e] extended with the argument is the one of its body [c]
    ([simple_lambda] needs no closure). A match becomes the application of
    its case combinator to the code of its branches and of its matched
    value ([case_code]): no closure. *)
Ltac2 rec conv (base : int) (t : constr) : constr :=
  if is_closed t then mkapp constr:(@Kc) [| hole (); hole (); closed t |]
  else match kind t with
  | Rel i => if Int.equal i base then base_access (Int.sub i 1) else access (Int.sub i 1)
  | App f args =>
      let n := Array.length args in
      let last := Array.get args (Int.sub n 1) in
      let init := mkapp f (Array.sub args 0 (Int.sub n 1)) in
      if is_closed init then
        mkapp constr:(@compose) [| hole (); hole (); hole (); closed init; conv base last |]
      else if is_closed last then
        mkapp constr:(@Cc) [| hole (); hole (); hole (); conv base init; closed last |]
      else mkapp constr:(@Sc) [| hole (); hole (); hole (); conv base init; conv base last |]
  | Lambda b body =>
      match simple_lambda b body with
      | Some u => conv base u
      | None => mkapp constr:(@Lam) [| hole (); binder_type b; hole (); conv (shift base 1) body |]
      end
  | Case ci _ _ scrut branches => case_code base ci scrut branches
  | _ => fail_msg "compile: unsupported term (local fixpoint, dependent match, ...)"
  end

(** The code of a match, for its environment [e]: the case combinator
    applied to the code of each branch, in [e] extended with the arguments
    of the constructor, and to the code of the matched value. *)
with case_code (base : int) (ci : case) (scrut : constr) (branches : constr array) : constr :=
  let data := Ind.data (Case.inductive ci) in
  mkapp_l (case_comb_of (Case.inductive ci))
    (List.append (holes (Int.add (Ind.nparams data) 2))
       (List.append (branch_codes base ci branches) [conv base scrut]))

with branch_codes (base : int) (ci : case) (branches : constr array) : constr list :=
  List.mapi (fun j a => conv (shift base a) (peel a (Array.get branches j)))
    (Array.to_list (Ind.constructor_nargs (Ind.data (Case.inductive ci))))

(** [closed t], for a closed term [t]. A closed lambda needs no closure:
    its code, with its argument as the environment ([conv] with [base]
    [1]), is the function itself. A closed [fun x => match x with ... end]
    is thus the case combinator, with [x] as its environment, read by [Ic];
    a closed [fun x y => b] is [Lam c], [c] being the code of [b] in the
    environment [ECons x y]. *)
with closed (t : constr) : constr :=
  match kind t with
  | Lambda b body =>
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
