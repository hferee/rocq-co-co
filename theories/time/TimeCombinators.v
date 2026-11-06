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

Module Type CombinatorTimeCostModel
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
      ([costs]), and the values (combinators). *)
  Ltac csimpl :=
    cbv beta iota zeta delta [app cost_add fmap ret_I ret bind cost res val pot fst snd];
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
  Ltac cunit :=
    repeat match goal with
    | |- context [?u] =>
        lazymatch type of u with
        | unit => lazymatch u with tt => fail | _ => destruct u end
        end
    end.

  (** From a goal [bound_order c_found c_claimed] to inequalities. *)
  Ltac cfinish :=
    bo_split; destr_inputs; ccases; cunit; try solve [lia | nia]; try ring_simplify.

  (** From a goal [ComplexityBound f c] to [bound_order c_found c]. *)
  Ltac cstart := eapply ComplexityBound_mono; [idtac | unfold_fun; cbc].

  (** [cbound_start] reduces a goal [ComplexityBound f c] to the goals that
      [cfinish] reduces to inequalities. Here, it handles definitions that
      are not recursive ([cstart]). The other layers of a cost model extend
      it ([Ltac cbound_start ::= ..]): [TimeFix] with recursive functions.
      The extension holds in the models that include the layer, so that
      [cbound], and the hint below, use the most complete version for the
      model. *)
  Ltac cbound_start := cstart.
  Ltac cbound := cbound_start; cfinish.

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
      evars, so that the hint does not call [cbound] recursively. *)
  #[global] Hint Extern 150 (@ComplexityBound _ _ _ _ ?c) =>
    tryif has_evar c then fail
    else first [solve [once cweaken] | solve [once cbound]] : typeclass_instances.
End CombinatorTimeCostModel.
