(** * Tools shared by the compilers

    The compilers ([ClosureCompile], [BracketCompile]; the selection is in
    [Compile]) rewrite the function of a goal [ComplexityBound f c] into a
    convertible term built from the combinators of [Combinators]. This file
    has what they share: the construction of terms, the case combinators of
    the inductive types, [compile_goal_with] (the replacement of [f] by its
    compiled form), and the unfolding equations of recursive functions
    ([fix_equation], [fix_equation_mutual] and [fix_equation_env]), as
    required by [fix_complexity] ([TimeFix]). *)

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Program.Basics PArith NArith ZArith QArith.
From Complexity Require Export Combinators Arity.
Import Constr.Unsafe.


Ltac2 fail_msg (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).

Ltac2 hole () := open_constr:(_ : Type).
Ltac2 holes (n : int) : constr list := List.init n (fun _ => hole ()).
Ltac2 dummy () := constr:(tt).
Ltac2 mkapp (f : constr) (args : constr array) : constr :=
  if Int.equal (Array.length args) 0 then f else make (App f args).
Ltac2 mkapp_l (f : constr) (args : constr list) : constr := mkapp f (Array.of_list args).
Ltac2 mklam (b : binder) (t : constr) : constr := make (Lambda b t).
Ltac2 mkprod (b : binder) (t : constr) : constr := make (Prod b t).
Ltac2 mkrel (n : int) : constr := make (Rel n).
Ltac2 binder (t : constr) : binder := Constr.Binder.make None t.

(** [lower t]: [t] does not use [Rel 1], which is removed. *)
Ltac2 lower (t : constr) : constr := substnl [dummy ()] 0 t.
Ltac2 occurs1 (t : constr) : bool := Bool.neg (noccurn 1 t).
Ltac2 is_rel1 (t : constr) : bool := match kind t with Rel n => Int.equal n 1 | _ => false end.

(** ** Case analysis *)

(** The name of a global reference. *)
Ltac2 ref_name (r : Std.reference) : string :=
  match List.last_opt (Env.path r) with
  | Some id => Ident.to_string id
  | None => ""
  end.

(** Case combinators are the constants named [I_case] (see [Combinators]). *)
Ltac2 is_case_comb (f : constr) : bool :=
  match kind f with
  | Constant c _ =>
      let s := ref_name (Std.ConstRef c) in
      let n := String.length s in
      if Int.lt n 5 then false else String.equal (String.sub s (Int.sub n 5) 5) "_case"
  | _ => false
  end.

Ltac2 rec count_prods (t : constr) : int :=
  match kind t with Prod _ b => Int.add 1 (count_prods b) | _ => 0 end.

(** Number of leading type arguments of a function type. *)
Ltac2 rec is_arity (t : constr) : bool :=
  match kind t with Sort _ => true | Prod _ b => is_arity b | _ => false end.
Ltac2 rec type_params (t : constr) : int :=
  match kind t with
  | Prod b body => if is_arity (Constr.Binder.type b) then Int.add 1 (type_params body) else 0
  | _ => 0
  end.

(** The case combinator [I_case] of the inductive type [I]. *)
Ltac2 case_comb_of (i : inductive) : constr :=
  let name := String.app (ref_name (Std.IndRef i)) "_case" in
  match Option.map (fun id => Env.expand [id]) (Ident.of_string name) with
  | Some (r :: _) => Env.instantiate r
  | _ => fail_msg (String.app "compile: no case combinator: " name)
  end.

(** The largest free [Rel] of [t]. *)
Ltac2 max_rel (t : constr) : int :=
  let rec go n := if closedn n t then n else go (Int.add n 1) in go 0.

(** The [n] binders of a branch, eta-expanded if needed, and its body. *)
Ltac2 rec peel_b (n : int) (t : constr) : binder list * constr :=
  if Int.equal n 0 then ([], t)
  else match kind t with
  | Lambda b body => let (bs, t) := peel_b (Int.sub n 1) body in (b :: bs, t)
  | _ =>
      let (bs, t) := peel_b (Int.sub n 1) (mkapp (liftn 1 1 t) [| mkrel 1 |]) in
      (binder (hole ()) :: bs, t)
  end.
Ltac2 peel (n : int) (t : constr) : constr := let (_, t) := peel_b n t in t.

(** ** Preprocessing *)

(** Let-ins become beta-redexes; matches are kept, and compiled by the compilers. *)
Ltac2 rec decase (t : constr) : constr :=
  match kind t with
  | Lambda b body => mklam b (decase body)
  | App f args => mkapp (decase f) (Array.map decase args)
  | LetIn b v body => decase (mkapp (mklam b body) [| v |])
  | Cast c _ _ => decase c
  | Case ci r iv scrut branches => make (Case ci r iv (decase scrut) (Array.map decase branches))
  | _ => t
  end.


(** [lift_cases t]: [t] without its let-ins' casts. The matches are kept:
    the case combinators work on environments, so that a variable used in
    several branches costs nothing ([case_code]). [fix_equation] proves the
    unfolding equation of the functional [lift_cases F] by case analysis. *)
Ltac2 rec lift_cases (t : constr) : constr :=
  match kind t with
  | Lambda b body => mklam b (lift_cases body)
  | App f args => mkapp (lift_cases f) (Array.map lift_cases args)
  | LetIn b v body => make (LetIn b (lift_cases v) (lift_cases body))
  | Cast c _ _ => lift_cases c
  | _ => t
  end.

(** Type-check a term built with holes, solving the holes. *)
Ltac2 typecheck (t : constr) : constr :=
  match Constr.Unsafe.check t with Val t => t | Err e => Control.throw e end.

(** Replace the argument number [i] of the head application of the goal by
    [y], which must be convertible to it (holes of [y] are solved). *)
(** Type arguments left undetermined by typing and unification can be any
    type: use [unit]. *)
Ltac2 rec close_holes (t : constr) : unit :=
  match kind t with
  | Evar _ _ => Std.unify t constr:(unit)
  | App f args => close_holes f; Array.iter close_holes args
  | Lambda b body => close_holes (Constr.Binder.type b); close_holes body
  | _ => ()
  end.

Ltac2 replace_goal_arg (i : int) (y : constr) :=
  let g := Control.goal () in
  match kind g with
  | App h args =>
      let y := typecheck y in
      (* unification solves the holes left by typing, if any; [change]
         checks the conversion *)
      Control.plus (fun () => Std.unify (Array.get args i) y) (fun _ => ());
      close_holes y;
      let args' := Array.copy args in
      Array.set args' i y;
      Std.change None (fun _ => make (App h args'))
        { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
  | _ => fail_msg "replace_goal_arg: the goal is not an application"
  end.

(** In a goal `@ComplexityBound A CA R f c`, replace [f] (the argument before
    last) by [compile f], convertible to it. *)
Ltac2 compile_goal_with (compile : constr -> constr) :=
  match kind (Control.goal ()) with
  | App _ args =>
      let i := Int.sub (Array.length args) 2 in
      replace_goal_arg i (compile (Array.get args i))
  | _ => fail_msg "compile_goal: unexpected goal"
  end.

(** ** Fixpoints

    [fix_equation], in a goal [ComplexityBound f c] where [f] is a recursive
    function, proves the unfolding equation `is_fixpoint ar F f` of [f], for
    its functional `F` (the body of the fixpoint, abstracted over the
    recursive calls, with its case analyses lifted by [lift_cases]), and
    adds it as a premise of the goal. It is proved by case analysis of the
    recursive argument and of the matched values. [f] may be a
    fixpoint applied to uniform leading arguments, such as the type arguments
    of a polymorphic fixpoint. For two mutually recursive functions [f1] and
    [f2], [fix_equation_mutual] does the same for
    [fun b => if b then f1 else f2]. *)

Ltac2 rec decompose_prod (n : int) (t : constr) : binder list * constr :=
  if Int.equal n 0 then ([], t)
  else match kind t with
  | Prod b body => let (bs, t) := decompose_prod (Int.sub n 1) body in (b :: bs, t)
  | _ => fail_msg "decompose_prod"
  end.

Ltac2 rec close_lams (bs : binder list) (t : constr) : constr :=
  match bs with [] => t | b :: bs => mklam b (close_lams bs t) end.

(** Beta-normalisation (no other reduction). *)
Ltac2 beta (t : constr) : constr :=
  Std.eval_cbv { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := false;
                 Std.rFix := false; Std.rCofix := false; Std.rZeta := false;
                 Std.rDelta := false; Std.rConst := [] } t.

Ltac2 rec count_lams (t : constr) : int :=
  match kind t with Lambda _ b => Int.add 1 (count_lams b) | _ => 0 end.

Ltac2 is_fix_app (t : constr) : bool :=
  match kind t with
  | Fix _ _ _ _ => true
  | App h _ => match kind h with Fix _ _ _ _ => true | _ => false end
  | _ => false
  end.

(** Unfold the head constant of [t] until a fixpoint, possibly applied, shows
    up. *)
Ltac2 head_is_constant (t : constr) : bool :=
  match kind t with
  | Constant _ _ => true
  | App h _ => match kind h with Constant _ _ => true | _ => false end
  | _ => false
  end.

Ltac2 rec unfold_to_fix (fuel : int) (t : constr) : constr :=
  if is_fix_app t then t
  else if Bool.or (Int.equal fuel 0) (Bool.neg (head_is_constant t)) then
    fail_msg "fix_equation: not a recursive function"
  else unfold_to_fix (Int.sub fuel 1) (Std.eval_red t).

Ltac2 split_app (t : constr) : constr * constr array :=
  match kind t with App h args => (h, args) | _ => (t, Array.of_list []) end.

(** The [Arity] of [t] with [n] (non-dependent) arrows. *)
Ltac2 rec mk_arity (n : int) (t : constr) : constr :=
  if Int.equal n 0 then mkapp constr:(@ar_val) [| t |]
  else match kind (Std.eval_hnf t) with
  | Prod b body =>
      if occurs1 body then fail_msg "fix_equation: dependent function type"
      else
        let body := lower body in
        mkapp constr:(@ar_fun) [| Constr.Binder.type b; body; mk_arity (Int.sub n 1) body |]
  | _ => fail_msg "fix_equation: not a function type"
  end.

(** The codomain of the function type [t]. *)
Ltac2 codomain (t : constr) : constr :=
  match kind (Std.eval_hnf t) with
  | Prod _ body => lower body
  | _ => fail_msg "fix_equation: not a function"
  end.

(** The leading lambdas of a term, and its body. *)
Ltac2 rec strip_lams (t : constr) : binder list * constr :=
  match kind t with
  | Lambda b body => let (bs, t) := strip_lams body in (b :: bs, t)
  | _ => ([], t)
  end.

(** Unfold the head constant of [t] until a fixpoint, possibly applied and
    under lambdas, shows up. *)
Ltac2 rec unfold_to_fix_lams (fuel : int) (t : constr) : constr :=
  let (_, inner) := strip_lams t in
  if is_fix_app inner then t
  else if Bool.or (Int.equal fuel 0) (Bool.neg (head_is_constant t)) then
    fail_msg "fix_equation: not a recursive function"
  else unfold_to_fix_lams (Int.sub fuel 1) (Std.eval_red t).

(** For [f] reducing to [fun x1 .. xL => (fix g y1 .. := body) a1 .. ap]
    (the lambdas are the parameters of a section, such as the function of
    [fold_left]; [L] may be [0]): the functional
    [fun rec x1 .. xL => body[g := fun _ .. _ => rec x1 .. xL] a1 .. ap],
    the number of its arguments (after [rec]), and the index of the
    recursive one among them. The recursive calls pass [x1 .. xL]
    unchanged. *)
Ltac2 fix_functional (f : constr) : constr * int * int :=
  let (xbs, inner) := strip_lams (unfold_to_fix_lams 10 f) in
  let l := List.length xbs in
  let (fx, args) := split_app inner in
  match kind fx with
  | Fix structs _ binders bodies =>
      if Bool.neg (Int.equal (Array.length bodies) 1) then
        fail_msg "fix_equation: mutual fixpoint (use fix_equation_mutual)"
      else
        let p := Array.length args in
        let body := Array.get bodies 0 in
        let (pbs, _) := decompose_prod p (Constr.Binder.type (Array.get binders 0)) in
        (* in the context [xL; ..; x1; rec], under the [p] binders: the
           recursive calls [g a1 .. ap] become [rec x1 .. xL] *)
        let xs := List.init l (fun i => mkrel (Int.add p (Int.sub l i))) in
        let s := close_lams (List.map (fun b => binder (Constr.Binder.type b)) pbs)
                   (mkapp_l (mkrel (Int.add (Int.add l p) 1)) xs) in
        let body' := substnl [s] 0 (liftn 1 (Int.add l 2) body) in
        let fbody := beta (mkapp body' (Array.map (liftn 1 (Int.add l 1)) args)) in
        let xbs' := List.mapi (fun i b =>
                      Constr.Binder.make (Constr.Binder.name b)
                        (liftn 1 (Int.add i 1) (Constr.Binder.type b))) xbs in
        (mklam (Constr.Binder.make (Some @rec) (Constr.type f)) (close_lams xbs' fbody),
         Int.add l (Int.sub (count_lams body) p), Int.add l (Int.sub (Array.get structs 0) p))
  | _ => fail_msg "fix_equation: not a fixpoint"
  end.

(** Prove `pw_eq ar (f a) (F' f a)` (for all `a`), where [F'] is
    `lift_cases F`, for [n] arguments, recursive on argument [k]: the
    equation `f a = F f a` holds by case analysis of the recursive argument
    and conversion, and `F f a = F' f a` by case analysis of the values
    matched by `F`. [pre] are the arguments given before (for mutual
    recursion). *)
Ltac2 prove_unfolding (ff : constr) (f : constr) (pre : constr list) (n : int) (k : int) :=
  ltac1:(intro; cbn [pw_eq]; intros);
  let hs := List.rev (List.firstn n (List.rev (Control.hyps ()))) in
  let (x, _, _) := List.nth hs k in
  let xs := List.map (fun (h, _, _) => make (Var h)) hs in
  let mid := mkapp_l ff (f :: List.append pre xs) in
  ltac1:(mid x |- transitivity mid;
    [ destruct x; reflexivity
    | cbv beta; autounfold with comb; cbv beta iota;
      repeat first
        [ reflexivity
        | match goal with |- context [match ?y with _ => _ end] =>
            destruct y; cbv beta iota end ] ])
    (Ltac1.of_constr mid) (Ltac1.of_ident x).

(** Prove [stmt] with [tac] and add it as a premise of the goal. *)
Ltac2 add_premise (stmt : constr) (tac : unit -> unit) :=
  (* typing adds the universe constraints of the arity *)
  let stmt := typecheck stmt in
  let h := Fresh.in_goal @Hunfold in
  Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier h))) stmt (Some tac));
  Std.revert [h].

Ltac2 fix_equation () :=
  match kind (Control.goal ()) with
  | App _ gargs =>
      let f := Array.get gargs (Int.sub (Array.length gargs) 2) in
      let (ff, n, k) := fix_functional f in
      let ff' := lift_cases ff in
      let ar := mk_arity (Int.sub n 1) (codomain (Constr.type f)) in
      add_premise constr:(is_fixpoint $ar $ff' $f)
        (fun () => ltac1:(unfold is_fixpoint); prove_unfolding ff f [] n k)
  | _ => fail_msg "fix_equation: unexpected goal"
  end.

(** Mutual recursion: [g := fun b => if b then f1 else f2], where [f1] and
    [f2] are the two functions of a mutual fixpoint, has the functional
    [fun rec b => if b then body1 else body2] where [f1] and [f2] become
    [rec true] and [rec false]. *)
Ltac2 mutual_functional (g : constr) : constr * int * int :=
  match kind g with
  | Lambda _ gbody =>
      match kind gbody with
      | Case _ _ _ _ brs =>
          let f1 := lower (Array.get brs 0) in
          match kind (unfold_to_fix 10 f1) with
          | Fix structs _ _ bodies =>
              if Bool.neg (Int.equal (Array.length bodies) 2) then
                fail_msg "fix_equation_mutual: expects two mutual functions"
              else
                (* bodies are in context [f1; f2]; branches are in context
                   [rec; b] *)
                let br i :=
                  substnl [mkapp (mkrel 2) [| constr:(false) |]; mkapp (mkrel 2) [| constr:(true) |]] 0
                    (liftn 2 3 (Array.get bodies i)) in
                let ty := codomain (Constr.type g) in
                let p := mklam (binder constr:(bool)) (liftn 1 1 ty) in
                (* [if b then br 0 else br 1], through [bool_rect] *)
                let gb := mkapp constr:(@bool_rect) [| liftn 2 1 p; br 0; br 1; mkrel 1 |] in
                let gg := mklam (Constr.Binder.make (Some @rec) (Constr.type g))
                            (mklam (binder constr:(bool)) gb) in
                (Std.eval_cbv { Std.rStrength := Std.Norm; Std.rBeta := true;
                    Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
                    Std.rZeta := false; Std.rDelta := false;
                    Std.rConst := [Std.ConstRef (match kind constr:(@bool_rect) with
                                                 | Constant c _ => c
                                                 | _ => fail_msg "bool_rect" end)] } gg,
                 count_lams (Array.get bodies 0), Array.get structs 0)
          | _ => fail_msg "fix_equation_mutual: not a mutual fixpoint"
          end
      | _ => fail_msg "fix_equation_mutual: expects fun b => if b then f1 else f2"
      end
  | _ => fail_msg "fix_equation_mutual: expects fun b => if b then f1 else f2"
  end.

Ltac2 fix_equation_mutual () :=
  match kind (Control.goal ()) with
  | App _ gargs =>
      let g := Array.get gargs (Int.sub (Array.length gargs) 2) in
      let (gg, n, k) := mutual_functional g in
      let gg' := lift_cases gg in
      let ar := mk_arity n (codomain (Constr.type g)) in
      add_premise constr:(is_fixpoint $ar $gg' $g)
        (fun () =>
           ltac1:(unfold is_fixpoint; let b := fresh "b" in intro b; destruct b);
           Control.dispatch [(fun () => prove_unfolding gg g [constr:(true)] n k);
                             (fun () => prove_unfolding gg g [constr:(false)] n k)])
  | _ => fail_msg "fix_equation_mutual: unexpected goal"
  end.

(** ** Arguments passed unchanged

    The arguments that every recursive call passes unchanged, such as the
    second argument of [app] or the function of [fold_left], can be the
    environment of the fixpoint ([fix_complexity]): the recursive calls
    then do not pass them again. *)

(** [uniform_args n ff], for the functional [ff = fun rec z1 .. zn => b]:
    for each argument, whether every occurrence of [rec] in [b] is a call
    that passes [zi] itself at its position. *)
Ltac2 uniform_args (n : int) (ff : constr) : bool array :=
  let rec peel k t :=
    if Int.equal k 0 then t
    else match kind t with
         | Lambda _ b => peel (Int.sub k 1) b
         | _ => fail_msg "uniform_args: not a functional"
         end in
  let b := peel (Int.add n 1) ff in
  let u := Array.make n true in
  let rec none i := if Int.lt i n then (Array.set u i false; none (Int.add i 1)) else () in
  let rec go d t :=
    let r := Int.add (Int.add n 1) d in
    match kind t with
    | Rel i => if Int.equal i r then none 0 else ()
    | App hd args =>
        (match kind hd with
         | Rel i =>
             if Int.equal i r then
               let na := Array.length args in
               let ok j :=
                 if Int.lt j na then
                   match kind (Array.get args j) with
                   | Rel x => Int.equal x (Int.add (Int.sub n j) d)
                   | _ => false
                   end
                 else false in
               let rec check j :=
                 if Int.lt j n then
                   ((if ok j then () else Array.set u j false); check (Int.add j 1))
                 else () in
               check 0
             else ()
         | _ => go d hd
         end);
        Array.iter (go d) args
    | _ => Constr.Unsafe.iter_with_binders (fun d _ => Int.add d 1) go d t
    end in
  go 0 b; u.

(** The environment of the types [T1; ..; Tk]: [T1], [env T1 T2],
    [env (env T1 T2) T3], ... *)
Ltac2 rec env_type (tys : constr list) : constr :=
  match List.rev tys with
  | [] => constr:(unit)
  | t :: [] => t
  | t :: rest => mkapp constr:(@env) [| env_type (List.rev rest); t |]
  end.

(** The values [x1; ..; xk] of an environment [e] of [env_type [T1; ..; Tk]]
    (built from [ECons]). *)
Ltac2 rec env_values (tys : constr list) (e : constr) : constr list :=
  match List.rev tys with
  | [] => []
  | _ :: [] => [e]
  | t :: rest =>
      let rest := List.rev rest in
      let et := env_type rest in
      List.append (env_values rest (mkapp constr:(@etl) [| et; t; e |]))
        [mkapp constr:(@ehd) [| et; t; e |]]
  end.

(** A recursive function [h] with arguments passed unchanged, as the
    function [ef_f : E -> A -> B] of an environment [E] of these arguments
    ([fix_complexity]): its functional [ef_F] ([lift_cases] applied), the
    arity of [B], the types of the arguments in [E], the number of the
    other arguments, and the index of the recursive one among them.
    - If the arguments passed unchanged come first ([ef_swap] false), [h]
      is [Lam (.. (Lam ef_f))] ([k - 1] times, for [k] of them, [ef_f] being
      [h] when [k] is [1]).
    - [h l m] where only [m] is passed unchanged ([ef_swap] true, as in
      [app], [Nat.add], [Nat.mul]) is [Cc ef_f]: [ef_f m l = h l m].
    Fails if there is no such argument. *)
Ltac2 Type env_fix := {
  ef_E : constr; ef_R : constr; ef_f : constr; ef_F : constr; ef_ar : constr;
  ef_tys : constr list; ef_m : int; ef_s : int; ef_swap : bool }.

Ltac2 env_fix (h : constr) : env_fix :=
  let (ff, n, s) := fix_functional h in
  let u := uniform_args n ff in
  let tys := match kind ff with
             | Lambda _ b =>
                 let (bs, _) := strip_lams b in
                 List.map Constr.Binder.type (List.firstn n bs)
             | _ => fail_msg "fix_equation_env: not a functional" end in
  if Bool.neg (List.for_all is_closed tys) then fail_msg "fix_equation_env: dependent arguments" else
  let (_, ret) := decompose_prod n (Std.eval_hnf (Constr.type h)) in
  if Bool.neg (is_closed ret) then fail_msg "fix_equation_env: dependent result" else
  (* [Bool.and] evaluates both arguments *)
  let rec prefix i := if Int.lt i n then (if Array.get u i then prefix (Int.add i 1) else i) else i in
  let k := prefix 0 in
  let (penv, prest, swap) :=
    if Int.lt 0 k then
      (List.init k (fun i => i), List.init (Int.sub n k) (fun i => Int.add i k), false)
    else if (if Int.equal n 2 then Bool.and (Array.get u 1) (Int.equal s 0) else false) then
      ([1], [0], true)
    else fail_msg "fix_equation_env: no argument passed unchanged" in
  let etys := List.map (fun i => List.nth tys i) penv in
  let rtys := List.map (fun i => List.nth tys i) prest in
  let m := List.length rtys in
  let ee := env_type etys in
  let rr := List.fold_right (fun t acc => mkprod (binder t) acc) rtys ret in
  let index_of (i : int) (l : int list) : int option :=
    let rec go j l := match l with
                      | [] => None
                      | x :: l => if Int.equal x i then Some j else go (Int.add j 1) l end in
    go 0 l in
  (* the functional, in [eg : env E R] and the other arguments *)
  let eg := mkrel (Int.add m 1) in
  let vals := env_values etys (mkapp constr:(@etl) [| ee; rr; eg |]) in
  let args := List.init n (fun i =>
    match index_of i penv with
    | Some j => List.nth vals j
    | None => match index_of i prest with
              | Some j => mkrel (Int.sub m j)
              | None => fail_msg "fix_equation_env" end
    end) in
  let rec' := close_lams (List.map binder tys)
                (mkapp_l (mkapp constr:(@ehd) [| ee; rr; mkrel (Int.add (Int.add m 1) n) |])
                   (List.map (fun q => mkrel (Int.sub n q)) prest)) in
  let fF := mklam (binder (mkapp constr:(@env) [| ee; rr |]))
              (close_lams (List.map binder rtys) (beta (mkapp_l ff (rec' :: args)))) in
  let fF := typecheck fF in
  let f :=
    if swap then mklam (binder ee) (mklam (binder (List.nth tys 0)) (mkapp h [| mkrel 1; mkrel 2 |]))
    else if Int.equal k 1 then h
    else mklam (binder ee) (mkapp_l h (env_values etys (mkrel 1))) in
  let f := typecheck f in
  let ar := match kind (Std.eval_hnf rr) with
            | Prod _ b => mk_arity (Int.sub m 1) (lower b)
            | _ => fail_msg "fix_equation_env: not a function" end in
  let s' := match index_of s prest with Some j => j | None => fail_msg "fix_equation_env" end in
  { ef_E := ee; ef_R := rr; ef_f := f; ef_F := fF; ef_ar := ar; ef_tys := etys;
    ef_m := m; ef_s := s'; ef_swap := swap }.

(** [fix_equation_env ef] proves the unfolding equation
    `forall e, is_fixpoint ar (fun g => F (ECons e g)) (f e)` of [ef]
    ([lift_cases] applied to [F]) and adds it as a premise of the goal. *)
Ltac2 fix_equation_env (ef : env_fix) :=
  let e_ty := ef.(ef_E) in
  let ar := ef.(ef_ar) in
  let f := ef.(ef_f) in
  let fF := ef.(ef_F) in
  let fF' := lift_cases fF in
  let m := ef.(ef_m) in
  let si := ef.(ef_s) in
  add_premise constr:(forall e : $e_ty, is_fixpoint $ar (fun g => $fF' (ECons e g)) ($f e))
    (fun () =>
       let e := Fresh.in_goal @e in
       Std.intro (Some e) None;
       let ev := Control.hyp e in
       ltac1:(unfold is_fixpoint);
       prove_unfolding constr:(fun g => $fF (ECons $ev g)) (beta (mkapp f [| ev |])) [] m si).

(** In a goal [ComplexityBound f c] where [f] is a definition (possibly
    applied to arguments), unfold it, so that [compile_goal] compiles its
    body. *)
Ltac2 unfold_fun () :=
  match kind (Control.goal ()) with
  | App _ args =>
      let i := Int.sub (Array.length args) 2 in
      let f := Array.get args i in
      let (h, _) := split_app f in
      match kind h with
      | Constant _ _ => replace_goal_arg i (Std.eval_red f)
      | _ => ()
      end
  | _ => fail_msg "unfold_fun: unexpected goal"
  end.

(** Ltac1 entry points. *)
Ltac fix_equation := ltac2:(fix_equation ()).
Ltac fix_equation_mutual := ltac2:(fix_equation_mutual ()).
Ltac unfold_fun := ltac2:(unfold_fun ()).

(** Values computed by compiled terms appear in cost expressions as
    applications of combinators: [unfold_comb] turns them back into ordinary
    terms (e.g. to destruct a test). *)
Ltac unfold_comb := autounfold with comb; cbv beta iota.
