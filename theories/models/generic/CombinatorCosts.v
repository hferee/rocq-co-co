(** * Costs of application, basic functions and combinators

    The first part of the generic cost model ([Generic]), heavily inspired
    by Forster & Künze's coq-library-complexity. The complexities
    ([ℂI], [ℂO]) are defined in [CostModel], independently of the
    resource; the operations on costs and the application [·], here.

    - [BasicCostModel]: the operations on costs ([CostOperations],
      [CostOps]), and the costs of the identity, of application, of
      composition and of constant functions.
    - [CombinatorCostModel]: the costs of the combinators of
      [Combinators]. [Compile.compile] turns a Rocq term into a convertible
      term built from them, and from the case combinators of the datatype
      models.
      The combinators are higher-order
      constants: their complexities take the complexities of their
      (functional) arguments, so that typeclass search finds the complexity
      of a compiled term by following its structure ([cbc_found]). *)

From Complexity Require Export CostModel Compile.
From Stdlib Require Import PArith.
From Stdlib Require List.
From Complexity Require Poly.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** ** Operations on costs

    [a +c b]: the cost [a], then [b], with its unit [czero]: the cost
    monoids of calf (Niu, Sterling, Grodin and Harper, "A cost-aware
    logical framework", POPL 2022), without their laws, as the tactics
    compute the costs. Time: [0] and [+]; peak space: the resource monoid
    ([SpaceCostModel]), where a cost may free memory.

    [c_frame] and [c_pop]: the frame of an evaluation that is not in tail
    position, whose value is used afterwards, pushed before it and popped
    after it (on the stack of a machine; allocated, then freed, in space).
    It is charged by the combinators that evaluate a subterm before using
    its value: the argument of [compose], the two subterms of [Sc], the
    function of [Cc], and the matched value of a case analysis. A call in
    tail position does not pay it. [0] in the models whose instance has no
    stack ([TimeCostModel]: L reduces terms). Fixed by the model. *)
Module Type CostOperations (Import CM : CostModel).
  Parameter czero : Cost.
  Parameter cplus : Cost -> Cost -> Cost.
  Parameter c_frame c_pop : Cost.
End CostOperations.

(** Their uses on the costs of terms ([ℂO']), which [cost_ops] unfolds. *)
Create HintDb cost_ops.
Module CostOps (Import CM : CostModel) (Import CO : CostOperations CM).
  Infix "+c" := cplus (at level 50, left associativity).
  #[global] Hint Unfold czero cplus c_frame c_pop : costs.

  (** Adds a cost, before. *)
  Definition cost_add {C} (n : Cost) (m : ℂO C) : ℂO C := n +c cost m +> res m.
  Infix "⊕" := cost_add (at level 60, right associativity).

  (** Adds a cost, after. *)
  Definition cost_after {C} (m : ℂO C) (n : Cost) : ℂO C := cost m +c n +> res m.

  (** [framed m k]: [m] in a frame, then [k] of its result. The costs are
      nested to the right, as with [⊕]: in time, where frames cost [0],
      they compute to [cost m + cost (k (res m))]. *)
  Definition framed {C D} (m : ℂO C) (k : C -> ℂO D) : ℂO D :=
    c_frame ⊕ cost m ⊕ c_pop ⊕ k (res m).

  (** If [cf] is the complexity of an arbitrary term [f] of function type,
      and [cx] is the complexity of an argument term [x], then
      [(f ⋊ cf) · (x ⋊ cx)] is the application term [f x] together with
      its complexity, in a call-by-value setting. *)
  Definition capp {A B CA CB}
    (f : ℂO (ℂI (A -> B) (ℂI A CA -> ℂO CB))) (x : ℂO (ℂI A CA)) : ℂO (ℂI B CB) :=
    let r := pot (res f) (res x) in
    cost x ⊕ (* normalise the argument *)
    cost f ⊕ (* normalise the function *)
    cost r +> (* normalise the application *)
    (val (res f) (val (res x)) ⋊ (* the value of the result of the application *)
    res r). (* the complexity of the result *)
  Infix "·" := capp (at level 36, left associativity).

  (** The complexity of a value, as that of a term. *)
  Definition ret_I {A CA} (x : ℂI A CA) : ℂO (ℂI A CA) := czero +> x.
  #[warnings="-uniform-inheritance"]
  Coercion ret_I : ℂI >-> ℂO'.

  #[global] Hint Unfold czero cplus c_frame c_pop cost_add cost_after framed capp ret_I : cost_ops.
End CostOps.

(** ** Application and basic functions *)

Module Type BasicCostModel (Import CM : CostModel).
  Include CostOperations CM.
  Include CostOps CM.

  (** ** Constants

      The costs of the primitives are constants, fixed by each cost model:
      [TimeCostModel] sets them all to [1]. [c_clo] is the cost of a partial
      application (building a closure). A full application of a combinator
      ([CombinatorCostAxioms], below) has a cost of its own: the projections of an
      environment [c_ehd] and [c_etl], the call of a closure [c_Lam], the
      constants [c_Kc] (also for [fun _ => b]), the identity [c_Ic] ([fun x => x]), the composition [c_compose], [c_Cc] and [c_Sc], and [c_etlc].
      They are equal in the models of L, and differ on a machine
      ([MachineCostModel]). The models of the datatypes and of fixpoints
      have their own constants. *)
  Parameter c_clo : Cost.
  Parameter c_ehd c_etl c_Lam c_Kc c_Ic c_compose c_Cc c_Sc c_etlc c_consume : Cost.
  #[global] Hint Unfold c_clo c_ehd c_etl c_Lam c_Kc c_Ic c_compose c_Cc c_Sc c_etlc c_consume : costs.


  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat,
  or make mistakes anymore *)

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  #[global] Declare Instance id_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (fun (x : A) => x) (fun ca => (c_Ic +> pot ca) : ℂO CA).

  (* Note : we are using the unfolding of [@id A] here so that typeclass
    resolution works *)

  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
    {v : A} {f : A -> B} {cv : CA} (cf : ℂI A CA -> ℂO CB),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound (f v: B) (res (cf (v ⋊ cv))).

  (** [tt]: the empty environment of closures, to which closed code is
      applied (see [Combinators]). *)
  #[global] Declare Instance Repr_unit : Repr unit unit.
  #[global] Declare Instance tt_complexity : ComplexityBound tt tt.
End BasicCostModel.

(** ** Combinators *)

(** [cunit] destructs the closed subterms of type [unit] of the goal, other
    than [tt] (the complexities of ground values, given by potentials of
    functions as [res (..)]). The goal is traversed once for each destruct,
    without going into numerals: the goals of the costs are mostly
    inequalities between numerals ([S (S ..)]), and an Ltac1 [context]
    match, which types each subterm, took most of the time on large
    functions. *)
Ltac2 rec unit_subterms (acc : constr list ref) (t : constr) : unit :=
  match nat_value t with
  | Some _ => ()
  | None =>
      let found :=
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.Constructor _ _ => false
        | Constr.Unsafe.Sort _ => false
        | Constr.Unsafe.Prod _ _ => false
        | _ =>
            if Constr.Unsafe.is_closed t then
              match Control.case (fun () => Constr.type t) with
              | Val (ty, _) => Constr.equal ty constr:(unit)
              | Err _ => false
              end
            else false
        end in
      if found then Ref.set acc (t :: Ref.get acc)
      else Constr.Unsafe.iter (unit_subterms acc) t
  end.

Ltac2 rec cunit_goal () :=
  let acc := Ref.ref [] in
  unit_subterms acc (Control.goal ());
  let rec try_all l :=
    match l with
    | [] => ()
    | u :: l =>
        match Control.case (fun () => ltac1:(u |- destruct u) (Ltac1.of_constr u)) with
        | Val _ => cunit_goal ()
        | Err _ => try_all l
        end
    end in
  try_all (List.rev (Ref.get acc)).

Ltac2 cunit () := Control.enter cunit_goal.

(** The model of the combinators ([CombinatorCostModel], at the end) is
    made of its axioms ([CombinatorCostAxioms]) and of the tactics that
    they justify ([CombinatorTactics]). The tactics are in a functor, which
    the module type includes, rather than in the module type itself: Ltac2
    definitions should not be made in module types, since functor
    applications do not check them. *)
Module Type CombinatorCostAxioms
  (Import CM : CostModel) (Import BT : BasicCostModel CM).
  (** ** Costs

      Partial applications (building closures) cost [c_clo], a full
      application of a combinator its own constant ([c_ehd], [c_etl],
      [c_Lam], [c_Kc], [c_Ic], [c_compose], [c_Cc], [c_Sc], [c_etlc];
      [BasicCostModel]); the
      models of the datatypes and of fixpoints charge their case combinators,
      constructors and unfoldings with their own constants. In
      [TimeCostModel], every application costs one, as a beta-step of the
      call-by-value lambda-calculus L (Forster & Kunze). Each step of the
      evaluation of a compiled term does a constant amount of work, so that
      the real work is bounded by a constant times the cost.

      Free steps would break this bound, even when they are affine: with a
      free [compose], a closure duplicated once (and charged once) can be
      executed exponentially many times at no cost ([tower] in [Examples]).
      A model with free combinators (all these constants [0]) does not bound
      the running time: it counts the uses of the other primitives (see
      [TimeArith]). *)

  (** ** Environments

      An environment is represented by the representations of its values:
      its complexity is the list of their complexities. The empty
      environment is [tt]. *)
  #[global] Declare Instance Repr_env :
    forall {E CE A CA}, Repr E CE -> Repr A CA -> Repr (env E A) (CE * CA).

  (** A complexity of an environment is well-formed when those of its
      values are. *)
  Parameter wf_env : forall {E CE A CA} `{Repr E CE} `{Repr A CA} (e : env E A) (c : CE * CA),
    wf e c <-> wf (etl e) (fst c) /\ wf (ehd e) (snd c).

  #[global] Declare Instance ehd_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@ehd E A) (fun ce => c_ehd +> snd (pot ce)).

  #[global] Declare Instance etl_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@etl E A) (fun ce => c_etl +> fst (pot ce)).

  (** ** Closures *)

  (** [Lam c e] is the closure of code [c] and environment [e]; applying it
      to [a] runs [c] in the environment [e] extended with [a]. *)
  #[global] Declare Instance Lam_complexity :
    forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => c_clo +>
       fun ce : ℂI E CE => c_clo +>
       fun ca : ℂI A CA => c_Lam ⊕ pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))).

  (** ** Applications and constants *)

  #[global] Declare Instance Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Kc A B) (fun ca => c_clo +> (fun _ => c_Kc +> pot ca)).

  (** [compose] (B). *)
  #[global] Declare Instance compose_hcomplexity :
    forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => c_clo +>
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => c_clo +>
       fun ca : ℂI A CA => c_compose ⊕ pot <$> framed (cg · ca) (fun y => cf · y)).

  (** [Cc f a x = f x a]. *)
  #[global] Declare Instance Cc_complexity :
    forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => c_clo +>
       fun ca : ℂI A CA => c_clo +>
       fun cx : ℂI X CX => c_Cc ⊕ pot <$> framed (cf · cx) (fun h => h · ca)).

  (** [Sc f g x = f x (g x)]: the bound variable is used twice. *)
  #[global] Declare Instance Sc_complexity :
    forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => c_clo +>
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => c_clo +>
       fun cx : ℂI X CX => c_Sc ⊕ pot <$>
         framed (cg · cx) (fun y => framed (cf · cx) (fun h => h · y))).

  (** [etlc f e = f (etl e)]: [f] runs in the rest of [e], in tail
      position. *)
  #[global] Declare Instance etlc_complexity :
    forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@etlc E A B)
      (fun cf : ℂI (E -> B) (ℂI E CE -> ℂO CB) => c_clo +>
       fun ce : ℂI (env E A) (CE * CA) => c_etlc ⊕ pot <$> cf · (etl (val ce) ⋊ fst (pot ce))).

  (** [consume c e = c (fun _ => ehd e) (etl e)]: the matched value is the
      top of [e], whose code is a constant. *)
  #[global] Declare Instance consume_complexity :
    forall {E CE I CI A CA} `{Repr E CE} `{Repr I CI} `{Repr A CA},
    ComplexityBound (@consume E I A)
      (fun cc : ℂI ((E -> I) -> E -> A) (ℂI (E -> I) (ℂI E CE -> ℂO CI) -> ℂO (ℂI E CE -> ℂO CA)) =>
       c_clo +>
       fun ce : ℂI (env E I) (CE * CI) =>
         c_consume ⊕ pot <$>
           framed (cc · ((fun _ : E => ehd (val ce)) ⋊ (fun _ : ℂI E CE => c_Kc +> snd (pot ce))))
             (fun h => h · (etl (val ce) ⋊ fst (pot ce)))).
End CombinatorCostAxioms.

Module CombinatorTactics
  (Import CM : CostModel) (Import BT : BasicCostModel CM)
  (Import CB : CombinatorCostAxioms CM BT).

  (** ** Combinators applied to their arguments

      [compose f g] and [fun _ => b] ([Kc b]), from the bounds of [compose]
      and [Kc]. *)
  Lemma compose_complexity : forall {A B C CA CB CC}
    `{Repr A CA} `{Repr B CB} `{Repr C CC}
    (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
    ComplexityBound f cf ->
    ComplexityBound g cg ->
    ComplexityBound (compose f g : A -> C)
                    (fun ca => c_compose ⊕ pot <$> framed ((g ⋊ cg) · ca) (fun y => (f ⋊ cf) · y)).
  Proof.
    intros A B C CA CB CC RA RB RC f cf g cg Hf Hg.
    exact (apply_complexity _ Hg (apply_complexity _ Hf compose_hcomplexity)).
  Qed.

  Lemma constant_complexity :
    forall {A B CA CB} `{Repr A CA} `{Repr B CB} b {cb},
    ComplexityBound (b : B) (cb : CB) ->
    ComplexityBound (fun (_ : A) => b) (fun _ => c_Kc +> cb).
  Proof.
    intros A B CA CB RA RB b cb Hb. exact (apply_complexity _ Hb (@Kc_complexity B A CB CA RB RA)).
  Qed.
  (** ** Search of complexities

      [Found f]: a complexity [found f] of [f], with its bound. The typeclass
      search of the complexity of a compiled term ([cbc_found]) finds an
      instance of [Found], whose complexity is an output (a field), rather
      than a bound [ComplexityBound f ?c], whose complexity is an index:

      - the complexity of an application [f v] is the output complexity of
        [f] at [v] ([found_apply], from [apply_complexity]), of lowest
        priority, so that the search follows the structure of compiled
        terms;
      - [found_compose] does the same for [compose] ([compose_complexity]);
      - the other complexities are the bounds of the instances
        ([found_bound]), tried first.

      The types of the instances found only mention the terms, not their
      complexities: with bounds, the complexity of each subterm, unreduced
      ([res (cf (v ⋊ cv))]), appeared in the type of the bound of each
      enclosing application, and the kernel type-checked it again there (the
      check of the proof terms took most of the time of the proofs of the
      large functions). *)
  Class Found {A CA} `{Repr A CA} (f : A) := { found : CA ; found_ok : ComplexityBound f found }.
  Arguments found {_ _ _} _ {_}.
  Arguments found_ok {_ _ _} _ {_}.

  Definition found_bound {A CA} `{Repr A CA} (f : A) (c : CA) (H : ComplexityBound f c) : Found f :=
    {| found := c; found_ok := H |}.

  Definition found_apply {A B CA CB} `{Repr A CA} `{Repr B CB} (v : A) (f : A -> B)
    (Hv : Found v) (Hf : Found f) : Found (f v) :=
    {| found := res (found f (v ⋊ found v));
       found_ok := apply_complexity _ (found_ok v) (found_ok f) |}.

  Definition found_compose {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC}
    (f : B -> C) (g : A -> B) (Hf : Found f) (Hg : Found g) : Found (compose f g : A -> C) :=
    {| found := fun ca : ℂI A CA => c_compose ⊕ pot <$> framed ((g ⋊ found g) · ca) (fun y => (f ⋊ found f) · y);
       found_ok := compose_complexity f _ g _ (found_ok f) (found_ok g) |}.

  Global Existing Instance found_bound | 1.
  Global Existing Instance found_compose | 50.
  Global Existing Instance found_apply | 100.

  (** [csearch] searches for the complexity of the term of a goal
      [ComplexityBound f ?c], which instantiates [?c] with [found f].
      [cbc_found] compiles the function first ([compile_goal], [Compile]). *)
  Ltac csearch :=
    lazymatch goal with
    | |- ComplexityBound ?f _ => notypeclasses refine (@found_ok _ _ _ f _)
    end;
    typeclasses eauto.

  (** When the search fails, the constants of the compiled function whose
      complexity is not known ([missing_bounds]) are reported: their bounds
      must be proved first, as instances. *)
  Ltac2 is_combinator (f : constr) : bool :=
    Bool.or (is_case_comb f)
      (List.exist (fun c => Constr.equal f c)
         [constr:(@Lam); constr:(@ehd); constr:(@etl); constr:(@Kc); constr:(@Sc);
          constr:(@Cc); constr:(@etlc); constr:(@compose); constr:(@consume)]).

  (** The constants and constructors of [t], applied to their type
      arguments. *)
  Ltac2 rec consts_of (t : constr) (acc : constr list) : constr list :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let acc := Array.fold_left (fun acc a => consts_of a acc) acc args in
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Constant _ _ =>
            if is_combinator f then acc else
            let n := let p := type_params (Constr.type f) in let l := Array.length args in if Int.lt p l then p else l in
            mkapp f (Array.sub args 0 n) :: acc
        | Constr.Unsafe.Constructor _ _ =>
            let n := let p := type_params (Constr.type f) in let l := Array.length args in if Int.lt p l then p else l in
            mkapp f (Array.sub args 0 n) :: acc
        | _ => consts_of f acc
        end
    | Constr.Unsafe.Constant _ _ => if is_combinator t then acc else t :: acc
    | Constr.Unsafe.Constructor _ _ => t :: acc
    | Constr.Unsafe.Lambda _ b => consts_of b acc
    | _ => acc
    end.

  (** Whether the complexity of [c] is found by typeclass search. The
      search is run once: the failure that undoes it ([Not_found]) must not
      backtrack into the other solutions of the search. *)
  Ltac2 has_found (c : constr) : bool :=
    match Control.case (fun () =>
            Control.once (fun () =>
              ltac1:(c |- assert (Found c) by (typeclasses eauto)) (Ltac1.of_constr c));
            Control.zero Not_found) with
    | Err Not_found => true
    | _ => false
    end.

  Ltac2 missing_bounds (t : constr) : constr list :=
    let cs := consts_of t [] in
    let cs := List.fold_right (fun c acc =>
                if List.exist (Constr.equal c) acc then acc else c :: acc) cs [] in
    List.filter (fun c => Bool.and (Bool.neg (is_arity (Constr.type c)))
                                   (Bool.neg (has_found c))) cs.

  Ltac2 missing_message (ms : constr list) : message :=
    match ms with
    | [] =>
        Advice.cat [Message.of_string "cbound: the search for the complexity of the compiled function failed, although its constants have known bounds.";
                    Advice.nl (); Message.of_string "A type of its values may have no representation (Repr)."]
    | _ =>
        Advice.cat [Message.of_string "cbound: no complexity bound is known for:";
                    Advice.cat (List.map (fun c => Advice.cat [Message.of_string " "; Message.of_constr c]) ms);
                    Message.of_string ".";
                    Advice.nl (); Message.of_string "The function analysed uses it: prove a bound for it first, and declare it as an instance, e.g.";
                    Advice.nl (); Message.of_string "  Global Instance g_complexity : Time.ComplexityBound g (fun cx => ... >|).";
                    Advice.nl (); Message.of_string "  Proof. cbound. Qed.";
                    Advice.nl (); Message.of_string "(or Existing Instance after a Lemma)."]
    end.

  (** The local fixpoints of a compiled term: its [fix] subterms, which
      the compiler keeps as constants (they are closed). [cbound] does not
      analyse them: their bounds must be given, as hypotheses or
      instances. *)
  Ltac2 rec local_fixes (t : constr) (acc : constr list) : constr list :=
    let add t := if List.exist (Constr.equal t) acc then acc else t :: acc in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Fix _ _ _ _ => add t
    | Constr.Unsafe.App f args => Array.fold_left (fun acc a => local_fixes a acc) (local_fixes f acc) args
    | Constr.Unsafe.Lambda _ b => if is_lifted_fix t then add t else local_fixes b acc
    | _ => acc
    end.

  Ltac2 fixes_message (fs : constr list) : message :=
    Advice.cat
      (List.append
         (List.map (fun f => Advice.cat
            [Message.of_string "cbound: unknown complexity bound for the local fixpoint ";
             Message.of_constr f; Message.of_string "."; Advice.nl ()]) fs)
         [Message.of_string "Declare it first: the bound is then read from the context, e.g.";
          Advice.nl (); Message.of_string "  assert (H : Time.ComplexityBound (fix ...) (fun cx => ... >|)) by cbound.";
          Advice.nl (); Message.of_string "(For a fixpoint that uses variables of the function, the bound is that of the function of them printed.)"]).

  Ltac2 csearch_diag () : unit :=
    match Control.case (fun () => ltac1:(csearch)) with
    | Val _ => ()
    | Err _ =>
        match Constr.Unsafe.kind (Control.goal ()) with
        | Constr.Unsafe.App _ args =>
            let t := Array.get args (Int.sub (Array.length args) 2) in
            match List.filter (fun f => Bool.neg (has_found f)) (List.rev (local_fixes t [])) with
            | [] => Control.zero (Tactic_failure (Some (missing_message (missing_bounds t))))
            | fs => Control.zero (Tactic_failure (Some (fixes_message fs)))
            end
        | _ => Control.zero (Tactic_failure (Some (missing_message [])))
        end
    end.

  Ltac cbc_found := unshelve (compile_goal; ltac2:(csearch_diag ())); try exact unit.

  (** ** Proofs of bounds

      [cbound] proves a goal [ComplexityBound f c], where [c] is the claimed
      bound and [f] a definition (recursive functions: [FixCosts]). It
      compiles the body of [f], finds the complexity of the compiled term by
      typeclass search, and reduces its comparison with [c] to inequalities
      between costs ([cfinish]), one for each case of the values of the
      inputs, which are named as in [c]. It proves them with [lia] or [nia].

      The inequalities left are [found <= claimed], with both sides
      normalised: they show which costs the claimed bound must cover, or
      which facts on the values are missing. *)

  (** Compute the costs ([cbv], as the complexities found by typeclass
      search are large terms), unfolding the constants of the model
      ([costs]), and the values (combinators). The closure combinators are
      unfolded by the same [cbv]: the values that the complexities carry
      are compiled terms applied to environments, and an environment
      contains the values computed in the environment before it ([let]s):
      unevaluated, they copy it, and their size doubles with each [let];
      evaluated by value, each environment is computed once. *)
  Ltac csimpl :=
    cbv beta iota zeta delta [found found_bound found_apply found_compose
                              capp cost_add cost_after framed fmap ret_I cost res val pot fst snd
                              cplus czero cle cnat
                              Lam ehd etl Kc Sc Cc etlc compose consume];
    autounfold with costs;
    (* the costs of a model may unfold to its algebra ([costs]): computed *)
    cbv beta iota zeta delta [cplus czero cle cnat];
    unfold_comb.

  (** Compute the functions of the claimed bound on constructors, but
      neither multiplication nor the tests on values. The projections and
      the costs that this reveals (from cost functions of the claimed
      bound) are unfolded as in [csimpl], so that the same atoms compare
      equal. *)
  Ltac cnorm :=
    cbn -[Nat.mul Nat.max Nat.eqb Nat.leb Nat.ltb Pos.to_nat];
    autounfold with costs;
    cbv beta delta [cost res val pot cplus cost_after framed czero cle cnat].

  (** Case analysis of the values matched in the costs (those of the
      claimed bound are not unfolded: a recursive function of the bound,
      unfolded on a successor, would match again). *)
  Ltac ccases :=
    repeat (csimpl;
      (* a match on a variable first: a cost may match on a cost computed
         from it (profiles, [SpaceCostModel]) *)
      first [ match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end
            | lazymatch goal with
              | |- context [match ?x with _ => _ end] =>
                  let E := fresh "E" in destruct x eqn:E
              end ]);
    csimpl; cnorm;
    (* the same tests in the claimed bound, revealed by [cnorm] *)
    repeat match goal with
           | E : ?x = _ |- context [match ?x with _ => _ end] => rewrite E; cnorm
           end.

  (** The complexities of ground values, given by potentials of functions
      as [res (..)], are [tt]. *)
  Ltac cunit := ltac2:(cunit ()).

  (** From a goal [bound_order c_found c_claimed] to inequalities. The found
      complexity is computed first ([csimpl]): as built by typeclass search,
      it is a large term (closures, environments, typed binders), which
      makes every later tactic slow, even [split] and [destruct]. *)
  (** The records written out by the computation ([val x ⋊ pot x]) are
      folded back, so that they compare equal to [x], and [bound_order x x]
      holds. *)
  Ltac cfold :=
    repeat match goal with
    | |- context [val ?x ⋊ pot ?x] => progress change (val x ⋊ pot x) with x
    end;
    try match goal with |- bound_order ?x ?x => reflexivity end.

  (** *** Export of the inequalities

      With [cexport] set ([Ltac2 Set cexport := true]), the tactics that
      end with [lia] and [nia] ([cfinish], [csize]) print the inequalities
      left instead, with the arithmetic hypotheses, and admit them. The
      minimiser of the constants ([tools/bounds/minimise.py]) makes the
      constants of a bound variables, and solves these inequalities for
      them. Each one is printed as [#G (<= a b)] (or [<], [=]), after its
      hypotheses [#H ...], between [#CGOAL] and [#END]; the terms are
      s-expressions over [+], [*] and [-], numerals and atoms [{t}]. A goal
      of another form is printed as [#X t] ([Advice]). *)
  (** The tests of the case analyses ([ccases]) as facts on numbers: a
      comparison [Nat.eqb], [Nat.leb] or [Nat.ltb] that is [true] or
      [false] ([x =? 0] false: [0 < x]). [lia] and [nia] do not read them
      as booleans. *)
  Ltac cbool_facts :=
    repeat match goal with
    | H : Nat.eqb ?x 0 = false |- _ => apply Nat.eqb_neq in H; assert (0 < x) by lia; clear H
    | H : Nat.eqb 0 ?x = false |- _ => apply Nat.eqb_neq in H; assert (0 < x) by lia; clear H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
    | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
    | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
    | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
    | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
    end.

  (** [lia] and [nia] ([nia] alone if [clia] is false), with the facts of
      the tests if needed, or the
      export (with these facts). The facts on the values are added first
      ([add_value_facts]), then those of the file ([cfacts_hook]), and the
      type aliases unfolded ([cnorm_types]);
      [nia] has a timeout, and may run after the analysis ([cnia],
      [Advice]). *)
  Ltac carith := ltac2:(if Advice.cexport then
                          Control.enter (fun () => ltac1:(cbool_facts); cfacts_hook (); Advice.cexport_goal (); ltac1:(admit))
                        else (ltac1:(add_value_facts); cfacts_hook ();
                              if Advice.clia then ltac1:(first [solve [lia | progress cbool_facts; lia] | cbool_facts; cnia])
                              else ltac1:(cbool_facts; cnia))).

  Ltac cfinish :=
    csimpl; bo_split; destr_inputs; ccases; cunit; cfold; carith;
    ltac2:(if Advice.csimplify then ltac1:(try ring_simplify) else ()).

  (** From a goal [ComplexityBound f c] to [bound_order c_found c]. *)
  Ltac cstart := eapply ComplexityBound_mono; [idtac | unfold_fun; cbc_found].

  (** [cbound_start] reduces a goal [ComplexityBound f c] to the goals that
      [cfinish] reduces to inequalities. Here, it handles definitions that
      are not recursive ([cstart]). It is a mutable Ltac2 definition: the
      other parts of the generic cost model extend it with [Ltac2 Set
      cbound_start as previous := ..], falling back on [previous] for the
      goals they do not handle ([FixCosts] for recursive functions). An
      extension holds in the models that include its part, after those of
      the parts included before it, so that [cbound], and the hint below,
      use the most complete version for the model. *)
  Ltac2 mutable cbound_start : unit -> unit := fun () => ltac1:(cstart).

  (** [cbound] proves [ComplexityBound f c] ([cbound_start], then
      [cfinish]), and [ConstantBound f], [LinearBound f] and
      [PolynomialBound f] from the bound of [f] found by typeclass search
      ([cconstant], [clinear], [cpolynomial]). The inequalities that it
      leaves are explained ([cadvice], [Advice]): a counterexample shows
      that the claimed bound is too small; [cexplain] suggests facts for
      the others. [cbound_core] is [cbound] without advice, for the proofs
      tried by typeclass search. *)
  Ltac cbound_core :=
    lazymatch goal with
    | |- ConstantBound _ => cconstant
    | |- LinearBound _ => clinear
    | |- PolynomialBound _ => cpolynomial
    | |- _ => ltac2:(cbound_start ()); cfinish
    end.

  (** A bound in the sizes of [f] follows from a bound in the values of
      its arguments, its [ComplexityBound] instance: without one, [cbound]
      says so. *)
  Ltac2 size_bound_note (f : constr) : unit :=
    Message.print (Advice.cat
      [Message.of_string "cbound: "; Message.of_constr f; Message.of_string " has no ComplexityBound instance.";
       Advice.nl (); Message.of_string "Prove a bound in the values of its arguments first (Global Instance ... :";
       Advice.nl (); Message.of_string "Time.ComplexityBound ...): this bound in the sizes then follows from it (cbound, clinear, cpolynomial)."]).
  Ltac cbound_sizes f kind :=
    tryif assert_succeeds (eassert (ComplexityBound f _) by typeclasses eauto)
    then lazymatch kind with
         | 0 => cconstant | 1 => clinear | _ => cpolynomial end
    else (let note := ltac2:(f |- match Ltac1.to_constr f with
                                   | Some f => size_bound_note f
                                   | None => ()
                                   end) in
          note f; fail "cbound: no ComplexityBound instance").
  Ltac cbound_untimed :=
    lazymatch goal with
    | |- ConstantBound ?f => cbound_sizes f 0
    | |- LinearBound ?f => cbound_sizes f 1
    | |- PolynomialBound ?f => cbound_sizes f 2
    | |- _ => cbound_core; cadvice
    end.
  Ltac cbound := let f := ltac2:(t |- ctimed "cbound" t) in f ltac:(idtac; cbound_untimed).

  (** [csize] proves a bound in the sizes of the arguments ([#|x|], [Size])
      from the bound of the function found by typeclass search, which is in
      their values or lengths: each one is at most the size ([SizeFact],
      [add_size_facts]). *)
  Ltac csize_by tac :=
    eapply ComplexityBound_mono; [idtac | tac];
    csimpl; bo_split; destr_inputs; ccases; cunit; add_size_facts;
    carith; cadvice.
  Ltac csize := let f := ltac2:(t |- ctimed "csize" t) in f ltac:(idtac; csize_by ltac:(typeclasses eauto)).

  (** [csize_using H]: the same, from the bound [H]. *)
  Ltac csize_using H := let f := ltac2:(t |- ctimed "csize" t) in f ltac:(idtac; csize_by ltac:(exact H)).

  (** [cproject H v] proves [ComplexityBound f c] from the bound [H] of a
      function [g] such that [g v] is [f], for example the bound of
      [fun b => if b then f1 else f2] for mutually recursive functions [f1]
      and [f2] ([cbound], [FixCosts]): [cproject H true] proves the bounds of
      [f1], [cproject H false] those of [f2]. *)
  Ltac cproject_untimed H v :=
    eapply ComplexityBound_mono; [idtac | exact (apply_complexity (v := v) _ _ H)];
    cfinish; cadvice.
  Ltac cproject H v := let f := ltac2:(t |- ctimed "cproject" t) in f ltac:(idtac; cproject_untimed H v).

  (** [cweaken] proves [ComplexityBound f c] from the bound of [f] found by
      typeclass search (an instance), when [c] is larger. *)
  Ltac cweaken := eapply ComplexityBound_mono; [idtac | typeclasses eauto]; cfinish.

  (** A claimed bound that is not an instance is proved by weakening the
      bound of an instance ([cweaken]), or by [cbound], when they prove it
      completely: [Instance : ComplexityBound f c := _]. A bound that they
      do not prove needs a proof script, [Proof. cbound.], which shows the
      inequalities left. Only the first complexity found by [cbound] is
      tried ([once]): backtracking into the typeclass search of [cbc_found] would
      try the same inequalities many times. The hint only applies to bounds
      without evars: the bounds of the subterms that [cbc_found] searches are
      evars, so that the hint does not call [cbound] recursively.

      The proof is an auxiliary lemma ([abstract]), named after the
      function ([Pos_compare_cont_cbound] for [Pos.compare_cont]): the proof
      terms built by [cbound] are large, and the declaration of an
      [Instance] given by a term (as [_]) processes them several times more
      slowly than a [Qed]. The name must not depend on the file only: the
      analyses of several files are included in one module type
      ([TimeStdlib]). *)
  Ltac cbound_auto := cundeferred; first [solve [once cweaken] | solve [once cbound_core]].

  Ltac2 cbound_lemma_name () : ident option :=
    match Constr.Unsafe.kind (Control.goal ()) with
    | Constr.Unsafe.App _ args =>
        let (h, _) := split_app (Array.get args (Int.sub (Array.length args) 2)) in
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant c _ =>
            let p := List.map Ident.to_string (Env.path (Std.ConstRef c)) in
            let p := List.skipn (Int.sub (List.length p) 2) p in
            Ident.of_string (String.app (String.concat "_" p) "_cbound")
        | _ => None
        end
    | _ => None
    end.

  Ltac cbound_abstract :=
    ltac2:(if Constr.has_evar (Control.goal ()) then ltac1:(cbound_auto)
           else match cbound_lemma_name () with
                | Some id => Control.abstract (Some id) (fun () => ltac1:(cbound_auto))
                | None => ltac1:(cbound_auto)
                end).

  #[global] Hint Extern 150 (@ComplexityBound _ _ _ ?c) =>
    tryif has_evar c then fail else cbound_abstract : typeclass_instances.
End CombinatorTactics.

Module Type CombinatorCostModel (CM : CostModel) (BT : BasicCostModel CM) :=
  CombinatorCostAxioms CM BT <+ CombinatorTactics CM BT.
