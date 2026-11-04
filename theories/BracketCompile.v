(** * Bracket abstraction (backup)

    The former compilation scheme, kept for comparison with closure
    conversion ([Compile]; see [BracketComparison]): every lambda is
    eliminated by Turner's bracket abstraction, by value, with the
    combinators [Kc], [Ic], [Sc], [Cc] and [compose] (K, I, S, C, B).

    Under call-by-value, the abstraction of a variable [x] out of a term must
    not evaluate the computations of the term when the closure is built: K
    only abstracts values (variables, partial applications of combinators to
    values, closed terms), and the other terms are abstracted structurally,
    with S, B and C, even when they do not use [x].

    - D. A. Turner. A new implementation technique for applicative
      languages. Software: Practice and Experience 9(1):31-49, 1979.
    - J. Gateley, B. F. Duba. Call-by-value combinatory logic and the
      lambda-value calculus. MFPS 1991, LNCS 598:41-53, 1992. *)

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Program.Basics.
From Complexity Require Import Combinators Compile.
Import Constr.Unsafe.

(** Combinators: number of type arguments and of other arguments. *)
Ltac2 comb_info (f : constr) : (int * int) option :=
  if Bool.or (List.exist (fun c => Constr.equal f c)
                [constr:(@Kc); constr:(@Ic); constr:(@Sc); constr:(@Cc); constr:(@compose)])
       (is_case_comb f)
  then
    let t := Constr.type f in
    let n := type_params t in
    Some (n, Int.sub (count_prods t) n)
  else None.

(** Under call-by-value, the body of a closure is only evaluated when the
    closure is applied. Bracket abstraction must not evaluate computations
    of the body when the closure is built: it only hoists out of a closure
    the terms that do not depend on its bound variables, and are values
    (variables, closures, i.e. partial applications of combinators to
    values, instantiations of type arguments) or closed terms. In particular, a
    recursive call is evaluated only when the closure containing it is
    applied. *)
Ltac2 rec hoistable (t : constr) : bool :=
  if is_closed t then true else
  match kind t with
  | Rel _ => true
  | App f args =>
      match comb_info f with
      | Some (n, m) =>
          Bool.and (Int.lt (Int.sub (Array.length args) n) m)
            (Array.for_all hoistable (Array.sub args n (Int.sub (Array.length args) n)))
      | None =>
          if is_closed f then Int.le (Array.length args) (type_params (Constr.type f))
          else false
      end
  | _ => false
  end.

(** [hoist t]: [t] does not use [Rel 1] and can be hoisted. *)
Ltac2 hoist (t : constr) : bool :=
  if occurs1 t then false else hoistable (lower t).

(** [abs t] is a combinator term [u] with no [Rel 1], such that [u x] is
    convertible to [t] where [Rel 1] is replaced by [x]: Turner's bracket
    abstraction, by value (see [Combinators]). [t] is a compiled term: it
    has no lambda. Evaluating [u] (building the closure) only evaluates
    values and closed terms: they are the only terms abstracted with [Kc];
    the other ones are abstracted structurally, even when they do not use
    [x], and are thus evaluated when [x] is given. *)
Ltac2 rec abs (t : constr) : constr :=
  if hoist t then mkapp constr:(@Kc) [| hole (); hole (); lower t |]
  else match kind t with
  | Rel _ => mkapp constr:(@Ic) [| hole () |]
  | App f args =>
      let n := Array.length args in
      let last := Array.get args (Int.sub n 1) in
      let init := mkapp f (Array.sub args 0 (Int.sub n 1)) in
      if hoist init then
        if is_rel1 last then lower init
        else mkapp constr:(@compose) [| hole (); hole (); hole (); lower init; abs last |]
      else if hoist last then
        mkapp constr:(@Cc) [| hole (); hole (); hole (); abs init; lower last |]
      else mkapp constr:(@Sc) [| hole (); hole (); hole (); abs init; abs last |]
  | _ => fail_msg "abs: unsupported term (local fixpoint, dependent match, ...)"
  end.

(** [bracket_compile t]: a term convertible to [t], built from combinators: every
    lambda is abstracted, and a [match] becomes an application of the case
    combinator, whose branches are closures. *)
Ltac2 rec bracket_compile (t : constr) : constr :=
  match kind t with
  | Lambda _ body => abs (bracket_compile body)
  | App f args => mkapp (bracket_compile f) (Array.map bracket_compile args)
  | LetIn b v body => bracket_compile (mkapp (mklam b body) [| v |])
  | Cast c _ _ => bracket_compile c
  | Case ci _ _ scrut branches =>
      let rec lams n body :=
        if Int.equal n 0 then bracket_compile body
        else abs (lams (Int.sub n 1) body) in
      let data := Ind.data (Case.inductive ci) in
      mkapp_l (case_comb_of (Case.inductive ci))
        (List.append (holes (Int.add (Ind.nparams data) 1))
           (List.append (List.map (fun (b, a) => lams a (peel a b)) (case_branches ci branches))
              [bracket_compile scrut]))
  | _ => t
  end.

(** In a goal [@ComplexityBound A CA R f c], replace [f] by its compiled
    form. *)
Ltac2 bracket_compile_goal () :=
  match kind (Control.goal ()) with
  | App _ args =>
      let i := Int.sub (Array.length args) 2 in
      replace_goal_arg i (bracket_compile (Array.get args i))
  | _ => fail_msg "bracket_compile_goal: unexpected goal"
  end.

Ltac bracket_compile_goal := ltac2:(bracket_compile_goal ()).

(** [cbc] with bracket abstraction. *)
Ltac bcbc := unshelve (bracket_compile_goal; typeclasses eauto); try exact unit.
