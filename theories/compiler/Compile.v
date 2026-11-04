(** * Tactics for the analysis of terms

    - [compile t] rewrites the lambda-term [t] into a convertible term built
      from the combinators of [Combinators], by closure conversion: every
      lambda becomes a closure, i.e. its code applied to the environment
      where it is built. Matches become case combinators. It only uses
      conversion: the goal before and after is the same proposition. (The
      former compiler, by bracket abstraction, is in [BracketCompile].)
    - [fix_equation] and [fix_equation_mutual] state and prove the unfolding
      equation of a recursive function, as required by [fix_complexity]
      ([TimeFix]). *)

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Program.Basics PArith NArith ZArith QArith.
From Complexity Require Import Combinators Arity.
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

(** A branch for a constant constructor becomes a thunk. *)
Ltac2 thunk (b : constr) : constr := mklam (binder constr:(unit)) (liftn 1 1 b).

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

(** [body] is under [a] binders; the free variables [ks] (outside these
    binders) become [r] new binders, inside them. *)
Ltac2 lift_vars (a : int) (ks : int list) (body : constr) : constr :=
  let r := List.length ks in
  let rec index k l i := match l with
    | [] => None
    | k' :: l => if Int.equal k k' then Some i else index k l (Int.add i 1) end in
  let img i :=
    if Int.le i a then mkrel (Int.add i r)
    else match index (Int.sub i a) ks 1 with
      | Some m => mkrel (Int.add (Int.sub r m) 1)
      | None => mkrel (Int.add i r)
      end in
  substnl (List.init (max_rel body) (fun i => img (Int.add i 1))) 0 body.

(** The branches of a [match], with their arities (constant constructors
    get a thunk). *)
Ltac2 case_branches (ci : case) (branches : constr array) : (constr * int) list :=
  List.mapi (fun j a =>
      let b := Array.get branches j in
      if Int.equal a 0 then (thunk b, 1) else (b, a))
    (Array.to_list (Ind.constructor_nargs (Ind.data (Case.inductive ci)))).

(** ** Closure conversion *)

(** Matches become applications of the case combinators, whose branches are
    functions of the arguments of the constructors (thunks for constant
    constructors); let-ins become beta-redexes. *)
Ltac2 rec decase (t : constr) : constr :=
  match kind t with
  | Lambda b body => mklam b (decase body)
  | App f args => mkapp (decase f) (Array.map decase args)
  | LetIn b v body => decase (mkapp (mklam b body) [| v |])
  | Cast c _ _ => decase c
  | Case ci _ _ scrut branches =>
      let data := Ind.data (Case.inductive ci) in
      mkapp_l (case_comb_of (Case.inductive ci))
        (List.append (holes (Int.add (Ind.nparams data) 1))
           (List.append (List.map (fun (b, _) => decase b) (case_branches ci branches))
              [decase scrut]))
  | _ => t
  end.

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

(** [conv t]: a closed term [u] such that [u e] is convertible to [t] where
    each variable [Rel i] is the value at position [i - 1] of the
    environment [e] (the latest bound first). The terms that do not use [e]
    are closed, and evaluated once ([Kc]); an application is [Sc], or
    [compose] (B) and [Cc] when one of its parts is closed. A lambda becomes
    a closure [Lam c e]: the environment [e] extended with the argument is
    the one of its body [c] ([simple_lambda] needs no closure). *)
Ltac2 rec conv (t : constr) : constr :=
  if is_closed t then mkapp constr:(@Kc) [| hole (); hole (); closed t |]
  else match kind t with
  | Rel i => access (Int.sub i 1)
  | App f args =>
      let n := Array.length args in
      let last := Array.get args (Int.sub n 1) in
      let init := mkapp f (Array.sub args 0 (Int.sub n 1)) in
      if is_closed init then
        mkapp constr:(@compose) [| hole (); hole (); hole (); closed init; conv last |]
      else if is_closed last then
        mkapp constr:(@Cc) [| hole (); hole (); hole (); conv init; closed last |]
      else mkapp constr:(@Sc) [| hole (); hole (); hole (); conv init; conv last |]
  | Lambda b body =>
      match simple_lambda b body with
      | Some u => conv u
      | None => mkapp constr:(@Lam) [| hole (); binder_type b; hole (); conv body |]
      end
  | _ => fail_msg "compile: unsupported term (local fixpoint, dependent match, ...)"
  end

(** [closed t], for a closed term [t]: its closed lambdas are closures with
    the empty environment [tt]. *)
with closed (t : constr) : constr :=
  match kind t with
  | Lambda b body =>
      match simple_lambda b body with
      | Some u => closed u
      | None =>
          mkapp constr:(@Lam) [| constr:(unit); binder_type b; hole (); conv body; constr:(tt) |]
      end
  | App f args => mkapp (closed f) (Array.map closed args)
  | _ => t
  end.

(** [compile t]: a term convertible to [t], built from combinators. *)
Ltac2 compile (t : constr) : constr := closed (decase t).

(** [lift_cases t]: [t] where each [match] is replaced by an application of
    the case combinator, whose branches are closures, and the variables used
    in several branches are passed to the selected branch, after the case
    analysis. The result is equal to [t] for all
    values of its free variables, but not convertible to it: it is only
    used for functionals of fixpoints ([fix_equation]), whose unfolding
    equation is proved by case analysis. *)
Ltac2 rec lift_cases (t : constr) : constr :=
  match kind t with
  | Lambda b body => mklam b (lift_cases body)
  | App f args => mkapp (lift_cases f) (Array.map lift_cases args)
  | LetIn b v body => make (LetIn b (lift_cases v) (lift_cases body))
  | Cast c _ _ => lift_cases c
  | Case ci _ _ scrut branches =>
      let brs := case_branches ci branches in
      let m := List.fold_left (fun m (b, _) => if Int.lt m (max_rel b) then max_rel b else m) 0 brs in
      let ks := List.filter (fun k =>
                  Int.le 2 (List.length (List.filter (fun (b, _) => Bool.neg (noccurn k b)) brs)))
                  (List.init m (fun k => Int.add k 1)) in
      let r := List.length ks in
      let mk (b, a) :=
        let (bs, body) := peel_b a b in
        let body := lift_cases (lift_vars a ks body) in
        List.fold_right mklam (List.append bs (List.init r (fun _ => binder (hole ())))) body in
      let data := Ind.data (Case.inductive ci) in
      (* the result type takes the lifted variables *)
      let rec res n := if Int.equal n 0 then hole () else mkprod (binder (hole ())) (res (Int.sub n 1)) in
      let c := mkapp_l (case_comb_of (Case.inductive ci))
                 (List.append (holes (Ind.nparams data))
                    (res r :: List.append (List.map mk brs) [lift_cases scrut])) in
      mkapp_l c (List.map mkrel ks)
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

(** In a goal [@ComplexityBound A CA R f c], replace [f] (the argument before
    last) by its compiled form. *)
Ltac2 compile_goal () :=
  match kind (Control.goal ()) with
  | App _ args =>
      let i := Int.sub (Array.length args) 2 in
      replace_goal_arg i (compile (Array.get args i))
  | _ => fail_msg "compile_goal: unexpected goal"
  end.

(** ** Fixpoints

    [fix_equation], in a goal [ComplexityBound f c] where [f] is a recursive
    function, proves the unfolding equation [is_fixpoint ar F f] of [f], for
    its functional [F] (the body of the fixpoint, abstracted over the
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

(** For [f] reducing to [(fix g x1 .. := body) a1 .. ap]: the functional
    [fun rec => body[g := fun _ .. _ => rec] a1 .. ap], the number of
    remaining arguments, and the index of the recursive one among them. *)
Ltac2 fix_functional (f : constr) : constr * int * int :=
  let (fx, args) := split_app (unfold_to_fix 10 f) in
  match kind fx with
  | Fix structs _ binders bodies =>
      if Bool.neg (Int.equal (Array.length bodies) 1) then
        fail_msg "fix_equation: mutual fixpoint (use fix_equation_mutual)"
      else
        let p := Array.length args in
        let body := Array.get bodies 0 in
        let (pbs, _) := decompose_prod p (Constr.Binder.type (Array.get binders 0)) in
        (* the recursive calls [g a1 .. ap] become [rec] *)
        let s := close_lams (List.map (fun b => binder (Constr.Binder.type b)) pbs)
                   (mkrel (Int.add p 1)) in
        let body' := substnl [s] 0 (liftn 1 2 body) in
        let fbody := beta (mkapp body' (Array.map (liftn 1 1) args)) in
        (mklam (Constr.Binder.make (Some @rec) (Constr.type f)) fbody,
         Int.sub (count_lams body) p, Int.sub (Array.get structs 0) p)
  | _ => fail_msg "fix_equation: not a fixpoint"
  end.

(** Prove [pw_eq ar (f a) (F' f a)] (for all [a]), where [F'] is
    [lift_cases F], for [n] arguments, recursive on argument [k]: the
    equation [f a = F f a] holds by case analysis of the recursive argument
    and conversion, and [F f a = F' f a] by case analysis of the values
    matched by [F]. [pre] are the arguments given before (for mutual
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
Ltac compile_goal := ltac2:(compile_goal ()).
Ltac fix_equation := ltac2:(fix_equation ()).
Ltac fix_equation_mutual := ltac2:(fix_equation_mutual ()).
Ltac unfold_fun := ltac2:(unfold_fun ()).

(** Compile the function of a [ComplexityBound] goal and search for its
    complexity. Complexity types left undetermined (those of unused
    arguments) can be anything. *)
Ltac cbc := unshelve (compile_goal; typeclasses eauto); try exact unit.

(** Values computed by compiled terms appear in cost expressions as
    applications of combinators: [unfold_comb] turns them back into ordinary
    terms (e.g. to destruct a test). *)
Ltac unfold_comb := autounfold with comb; cbv beta iota.
