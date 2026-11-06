(** * Cost model for the combinators of [Combinators]

    [Compile.compile] turns every lambda-term (and [match], through the case
    combinators of the datatype models) into a convertible term built from
    the closure combinators [Lam], [ehd], [etl], [Kc], [Sc], [Cc] and
    [compose] ([Ic] is only used by bracket abstraction, [BracketCompile]).
    The combinators are higher-order constants: their complexities take the
    complexities of their (functional) arguments, so that typeclass search
    finds the complexity of a compiled term by following its structure
    ([cbc]). *)

From Complexity Require Export TimeBasic Compile.
From Stdlib Require Import PArith.
From Stdlib Require List.
From Complexity Require Poly.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** ** Constant bounds

    [cst1 k], [cst2 k1 k2], ...: the complexity of a first-order function of
    [1], [2], ... arguments whose applications cost [k1], [k2], ... A bound
    [ComplexityBound f (cst2 _ _)] is proved by [cconst], which finds the
    constants ([CombinatorTactics]). The constants are arguments, not
    expressions under the binders of the complexity, so that they can be
    left to [cconst]. *)
    (* TODO: can we generalise this to an arbitrary arity? *)
Definition cst1 {A CA} (k1 : nat) : ℂI A CA -> ℂO unit := fun _ => k1 ⋉ tt.
Definition cst2 {A CA B CB} (k1 k2 : nat) : ℂI A CA -> ℂO (ℂI B CB -> ℂO unit) :=
  fun _ => k1 ⋉ fun _ => k2 ⋉ tt.
Definition cst3 {A CA B CB C CC} (k1 k2 k3 : nat)
  : ℂI A CA -> ℂO (ℂI B CB -> ℂO (ℂI C CC -> ℂO unit)) :=
  fun _ => k1 ⋉ fun _ => k2 ⋉ fun _ => k3 ⋉ tt.
Definition cst4 {A CA B CB C CC D CD} (k1 k2 k3 k4 : nat)
  : ℂI A CA -> ℂO (ℂI B CB -> ℂO (ℂI C CC -> ℂO (ℂI D CD -> ℂO unit))) :=
  fun _ => k1 ⋉ fun _ => k2 ⋉ fun _ => k3 ⋉ fun _ => k4 ⋉ tt.
Definition cst5 {A CA B CB C CC D CD E CE} (k1 k2 k3 k4 k5 : nat)
  : ℂI A CA -> ℂO (ℂI B CB -> ℂO (ℂI C CC -> ℂO (ℂI D CD -> ℂO (ℂI E CE -> ℂO unit)))) :=
  fun _ => k1 ⋉ fun _ => k2 ⋉ fun _ => k3 ⋉ fun _ => k4 ⋉ fun _ => k5 ⋉ tt.
Definition cst6 {A CA B CB C CC D CD E CE F CF} (k1 k2 k3 k4 k5 k6 : nat)
  : ℂI A CA -> ℂO (ℂI B CB -> ℂO (ℂI C CC -> ℂO (ℂI D CD -> ℂO (ℂI E CE -> ℂO
    (ℂI F CF -> ℂO unit))))) :=
  fun _ => k1 ⋉ fun _ => k2 ⋉ fun _ => k3 ⋉ fun _ => k4 ⋉ fun _ => k5 ⋉ fun _ => k6 ⋉ tt.
#[global] Hint Unfold cst1 cst2 cst3 cst4 cst5 cst6 : costs.

Ltac2 rec cst_update (r : constr) (k : int) (l : (constr * int) list) : (constr * int) list :=
  match l with
  | [] => [(r, k)]
  | (r', k') :: l' =>
      if Constr.equal r r' then (r, imax k k') :: l' else (r', k') :: cst_update r k l'
  end.

(** [cunit] destructs the closed subterms of type [unit] of the goal, other
    than [tt] (the complexities of ground values, given by potentials of
    functions as [res (..)]). The goal is traversed once for each destruct,
    without going into numerals: the goals of the costs are mostly
    inequalities between numerals ([S (S ..)]), and an Ltac1 [context]
    match, which types each subterm, took most of the time of [cconst] on
    large functions. *)
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

(** In the goals [cost <= ?k], instantiates each [?k] with the largest
    cost, which must be a numeral expression. *)
Ltac2 cst_instantiate () :=
  let tbl := Ref.ref [] in
  Control.enter (fun () =>
    lazy_match! goal with
    | [ |- ?l <= ?r ] =>
        if Constr.is_evar r then
          let (k, d) := poly_of l in
          if Int.lt 0 d then
            Control.zero (Tactic_failure (Some (Message.concat
              (Message.of_string "cconst: the cost is not constant: ") (Message.of_constr l))))
          else Ref.set tbl (cst_update r k (Ref.get tbl))
        else ()
    | [ |- _ ] => ()
    end);
  Control.focus 1 1 (fun () =>
    List.iter (fun (r, k) => Std.unify r (nat_constr k)) (Ref.get tbl)).

(** The model of the combinators ([CombinatorTimeCostModel], at the end) is
    made of its axioms ([CombinatorTimeCostAxioms]) and of the tactics that
    they justify ([CombinatorTactics]). The tactics are in a functor, which
    the module type includes, rather than in the module type itself: Ltac2
    definitions should not be made in module types, since functor
    applications do not check them. *)
Module Type CombinatorTimeCostAxioms
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** The complexity of an application [f v] is the output complexity of [f]
      at [v] ([apply_complexity]). As an instance of lowest priority, it lets
      typeclass search follow the structure of compiled terms. *)
  Global Existing Instance apply_complexity | 100.

  (** ** Costs

      Partial applications (building closures) cost [c_clo], full
      applications of the combinators [c_step] ([BasicTimeCostModel]); the
      models of the datatypes and of fixpoints charge their case combinators,
      constructors and unfoldings with their own constants. In
      [TimeCostModel], every application costs one, as a beta-step of the
      call-by-value lambda-calculus L (Forster & Kunze). Each step of the
      evaluation of a compiled term does a constant amount of work, so that
      the real work is bounded by a constant times the cost.

      Free steps would break this bound, even when they are affine: with a
      free [compose], a closure duplicated once (and charged once) can be
      executed exponentially many times at no cost ([tower] in [Examples]).
      A model with free combinators ([c_clo = c_step = 0]) does not bound
      the running time: it counts the uses of the other primitives (see
      [TimeArith]). *)

  (** ** Environments

      An environment is represented by the representations of its values:
      its complexity is the list of their complexities. The empty
      environment is [tt]. *)
  #[global] Declare Instance Repr_env :
    forall {E CE A CA}, Repr E CE -> Repr A CA -> Repr (env E A) (CE * CA).

  #[global] Declare Instance ehd_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@ehd E A) (fun ce => c_step ⋉ snd (pot ce)).

  #[global] Declare Instance etl_complexity : forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@etl E A) (fun ce => c_step ⋉ fst (pot ce)).

  (** ** Closures *)

  (** [Lam c e] is the closure of code [c] and environment [e]; applying it
      to [a] runs [c] in the environment [e] extended with [a]. *)
  #[global] Declare Instance Lam_complexity :
    forall {E CE A CA B CB} `{Repr E CE} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Lam E A B)
      (fun cc : ℂI (env E A -> B) (ℂI (env E A) (CE * CA) -> ℂO CB) => c_clo ⋉
       fun ce : ℂI E CE => c_clo ⋉
       fun ca : ℂI A CA => c_step ⊕ pot <$> cc · (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))).

  (** ** Applications and constants *)

  #[global] Declare Instance Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Kc A B) (fun ca => c_clo ⋉ (fun _ => c_step ⋉ pot ca)).

  (** Only used by bracket abstraction. *)
  #[global] Declare Instance Ic_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Ic A) (fun ca => c_step ⋉ pot ca).

  (** [compose] (B) as a constant, whereas [compose_complexity] requires fixed
      arguments. *)
  #[global] Declare Instance compose_hcomplexity :
    forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => c_clo ⋉
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => c_clo ⋉
       fun ca : ℂI A CA => c_step ⊕ pot <$> cf · (cg · ca)).

  (** [Cc f a x = f x a]. *)
  #[global] Declare Instance Cc_complexity :
    forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => c_clo ⋉
       fun ca : ℂI A CA => c_clo ⋉
       fun cx : ℂI X CX => c_step ⊕ pot <$> cf · cx · ca).

  (** [Sc f g x = f x (g x)]: the bound variable is used twice. *)
  #[global] Declare Instance Sc_complexity :
    forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => c_clo ⋉
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => c_clo ⋉
       fun cx : ℂI X CX => c_step ⊕ pot <$> cf · cx · (cg · cx)).
End CombinatorTimeCostAxioms.

Module CombinatorTactics
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostAxioms CM BT).

  (** ** Proofs of bounds

      [cbound] proves a goal [ComplexityBound f c], where [c] is the claimed
      bound and [f] a definition (recursive functions: [TimeFix]). It
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
    cbv beta iota zeta delta [app cost_add fmap ret_I ret bind cost res val pot fst snd
                              Lam ehd etl Kc Ic Sc Cc compose];
    autounfold with costs; unfold_comb.

  (** Compute the functions of the claimed bound on constructors, but
      neither multiplication nor the tests on values. The projections that
      this reveals (from cost functions of the claimed bound) are unfolded
      as in [csimpl], so that the same atoms compare equal. *)
  Ltac cnorm :=
    cbn -[Nat.mul Nat.eqb Nat.leb Nat.ltb Pos.to_nat];
    cbv beta delta [cost res val pot].

  (** Case analysis of the values matched in the costs (those of the
      claimed bound are not unfolded: a recursive function of the bound,
      unfolded on a successor, would match again). *)
  Ltac ccases :=
    repeat (csimpl;
      lazymatch goal with
      | |- context [match ?x with _ => _ end] =>
          tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
      end);
    csimpl; cnorm.

  (** The complexities of ground values, given by potentials of functions
      as [res (..)], are [tt]. *)
  Ltac cunit := ltac2:(cunit ()).

  (** From a goal [bound_order c_found c_claimed] to inequalities. The found
      complexity is computed first ([csimpl]): as built by typeclass search,
      it is a large term (closures, environments, typed binders), which
      makes every later tactic slow, even [split] and [destruct]. *)
  Ltac cfinish :=
    csimpl; bo_split; destr_inputs; ccases; cunit; try solve [lia | nia]; try ring_simplify.

  (** From a goal [ComplexityBound f c] to [bound_order c_found c]. *)
  Ltac cstart := eapply ComplexityBound_mono; [idtac | unfold_fun; cbc].

  (** [cbound_start] reduces a goal [ComplexityBound f c] to the goals that
      [cfinish] reduces to inequalities. Here, it handles definitions that
      are not recursive ([cstart]). It is a mutable Ltac2 definition: the
      other layers of a cost model extend it with [Ltac2 Set cbound_start as
      previous := ..], falling back on [previous] for the goals they do not
      handle ([TimeFix] for recursive functions). An extension holds in the
      models that include its layer, after those of the layers included
      before it, so that [cbound], and the hint below, use the most complete
      version for the model. *)
  Ltac2 mutable cbound_start : unit -> unit := fun () => ltac1:(cstart).

  (** [cconst] proves [ComplexityBound f (cst2 _ _)] (or [cst1], ...), and
      finds the constants: the largest costs of the applications of [f]. *)
  Ltac cconst :=
    ltac2:(cbound_start ()); csimpl; bo_split; destr_inputs; ccases; cunit;
    ltac2:(cst_instantiate ()); cbn; lia.

  (** [cbound_constant], [cbound_linear] and [cbound_polynomial] prove
      [ConstantBound f], [LinearBound f] and [PolynomialBound f] by analysing
      [f] as [cbound] does, without a [ComplexityBound] instance for [f]
      (unlike [cconstant], [clinear] and [cpolynomial]): [cbound_split]
      reduces [FirstOrderBound f (peval ?p)] to inequalities [cost <= peval
      ?p ss], and the polynomial [?p] is chosen from the costs as in
      [Bounds]. The inequalities that [lia] and [nia] do not prove are left,
      for example when they need facts on the sizes of the arguments. *)
  Ltac cbound_split :=
    unfold FirstOrderBound; cbn [fo_repr size_bound];
    ltac2:(cbound_start ()); csimpl; bo_split; destr_inputs; ccases; cunit;
    add_size_facts.

  Ltac cbound_constant :=
    unfold ConstantBound; eexists; split; cycle 1;
    [ cbound_split; ltac2:(constant_constants ()); cbn [Poly.peval List.nth];
      try solve [lia | nia]
    | reflexivity ].

  Ltac cbound_linear :=
    unfold LinearBound; eexists; split; cycle 1;
    [ cbound_split; ltac2:(linear_constants ()); cbn [Poly.peval List.nth];
      try solve [lia | nia]
    | cbn; lia ].

  Ltac cbound_polynomial :=
    unfold PolynomialBound; eexists;
    cbound_split; ltac2:(polynomial_constants ()); cbn [Poly.peval List.nth Nat.pow];
    try solve [lia | nia].

  (** [cbound] proves [ComplexityBound f c] ([cbound_start], then
      [cfinish]), and [ConstantBound f], [LinearBound f] and
      [PolynomialBound f] with the tactics above. *)
  Ltac cbound :=
    lazymatch goal with
    | |- ConstantBound _ => cbound_constant
    | |- LinearBound _ => cbound_linear
    | |- PolynomialBound _ => cbound_polynomial
    | |- _ => ltac2:(cbound_start ()); cfinish
    end.

  (** [cweaken] proves [ComplexityBound f c] from the bound of [f] found by
      typeclass search (an instance), when [c] is larger. *)
  Ltac cweaken := eapply ComplexityBound_mono; [idtac | typeclasses eauto]; cfinish.

  (** A claimed bound that is not an instance is proved by weakening the
      bound of an instance ([cweaken]), or by [cbound], when they prove it
      completely: [Instance : ComplexityBound f c := _]. A bound that they
      do not prove needs a proof script, [Proof. cbound.], which shows the
      inequalities left. Only the first complexity found by [cbound] is
      tried ([once]): backtracking into the typeclass search of [cbc] would
      try the same inequalities many times. The hint only applies to bounds
      without evars: the bounds of the subterms that [cbc] searches are
      evars, so that the hint does not call [cbound] recursively.

      The proof is an auxiliary lemma ([abstract]), named after the
      function ([Pos_compare_cont_cbound] for [Pos.compare_cont]): the proof
      terms built by [cbound] are large, and the declaration of an
      [Instance] given by a term (as [_]) processes them several times more
      slowly than a [Qed]. The name must not depend on the file only: the
      analyses of several files are included in one module type
      ([TimeStdlib]). *)
  Ltac cbound_auto := first [solve [once cweaken] | solve [once cbound]].

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

  #[global] Hint Extern 150 (@ComplexityBound _ _ _ _ ?c) =>
    tryif has_evar c then fail else cbound_abstract : typeclass_instances.
End CombinatorTactics.

Module Type CombinatorTimeCostModel (CM : CostModel) (BT : BasicTimeCostModel CM) :=
  CombinatorTimeCostAxioms CM BT <+ CombinatorTactics CM BT.
