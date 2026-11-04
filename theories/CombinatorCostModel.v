(** * Cost model for the combinators of [Combinators]

    [Compile.compile] turns every lambda-term (and [match], through the case
    combinators of the datatype models) into a convertible term built from
    [Kc], [Ic], [compose], [Cc] and [Sc]. The combinators are higher-order
    constants: their complexities take the complexities of their
    (functional) arguments, so that typeclass search finds the complexity of
    a compiled term by following its structure ([cbc]). *)

From Complexity Require Import CostModel HOCostModel Combinators Compile.
From Stdlib Require Import Program.Basics PArith Arith Lia.

Module Type CombinatorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** The complexity of an application [f v] is the output complexity of [f]
      at [v] ([apply_complexity]). As an instance of lowest priority, it lets
      typeclass search follow the structure of compiled terms. *)
  Global Existing Instance apply_complexity | 100.

  (** ** Costs

      Every application costs at least one, as a beta-step of the
      call-by-value lambda-calculus L (Forster & Kunze): partial applications
      (building closures), and full applications of the combinators and, in
      the models of the datatypes, of the case combinators, of the
      constructors and of the unfoldings of fixpoints. Each step of the
      evaluation of a compiled term does a constant amount of work, so that
      the real work is bounded by a constant times the cost.

      Free steps would break this bound, even when they are affine: with a
      free [compose], a closure duplicated once (and charged once) can be
      executed exponentially many times at no cost ([tower] in [Examples]). *)

  Parameter Kc_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Kc A B) (fun ca : ℂI A CA => 1 ⋉ (fun _ : ℂI B CB => 1 ⋉ pot ca)).
  Global Existing Instance Kc_complexity.

  Parameter Ic_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@Ic A) (fun ca : ℂI A CA => 1 ⋉ pot ca).
  Global Existing Instance Ic_complexity.

  (** [compose] (B) as a constant, whereas [compose_complexity] requires fixed
      arguments. *)
  Parameter compose_hcomplexity : forall {A B C CA CB CC} `{Repr A CA} `{Repr B CB} `{Repr C CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 1 ⋉
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 ⋉
       fun ca : ℂI A CA => 1 ⊕ pot <$> cf · (cg · ca)).
  Global Existing Instance compose_hcomplexity.

  (** [Cc f a x = f x a]. *)
  Parameter Cc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 ⋉
       fun ca : ℂI A CA => 1 ⋉
       fun cx : ℂI X CX => 1 ⊕ pot <$> cf · cx · ca).
  Global Existing Instance Cc_complexity.

  (** [Sc f g x = f x (g x)]: the bound variable is used twice. *)
  Parameter Sc_complexity : forall {X A B CX CA CB} `{Repr X CX} `{Repr A CA} `{Repr B CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 1 ⋉
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 1 ⋉
       fun cx : ℂI X CX => 1 ⊕ pot <$> cf · cx · (cg · cx)).
  Global Existing Instance Sc_complexity.

  (** ** Proofs of bounds

      [cbound] proves a goal [ComplexityBound f c], where [c] is the claimed
      bound and [f] a definition (recursive functions: [FixCostModel]). It
      compiles the body of [f], finds the complexity of the compiled term by
      typeclass search, and reduces its comparison with [c] to inequalities
      between costs ([cfinish]), one for each case of the values of the
      inputs, which are named as in [c]. It proves them with [lia] or [nia].

      The inequalities left are [found <= claimed], with both sides
      normalised: they show which costs the claimed bound must cover, or
      which facts on the values are missing. *)

  (** Compute the costs ([cbv], as the complexities found by typeclass
      search are large terms) and the values (combinators). *)
  Ltac csimpl :=
    cbv beta iota zeta delta [app cost_add fmap ret_I ret bind cost res val pot];
    unfold_comb.

  (** Compute the functions of the claimed bound on constructors, but
      neither multiplication nor the tests on values. *)
  Ltac cnorm := cbn -[Nat.mul Nat.eqb Nat.leb Nat.ltb Pos.to_nat].

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

  (** From a goal [bound_order c_found c_claimed] to inequalities. *)
  Ltac cfinish :=
    bo_split; destr_inputs; ccases; try solve [lia | nia]; try ring_simplify.

  (** From a goal [ComplexityBound f c] to [bound_order c_found c]. *)
  Ltac cstart := eapply ComplexityBound_ext_eq; [idtac | unfold_fun; cbc].

  Ltac cbound := cstart; cfinish.
End CombinatorTimeCostModel.
