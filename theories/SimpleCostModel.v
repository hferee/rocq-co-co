From Stdlib Require Import Classes.Morphisms Classes.RelationClasses Program.Basics.

(** We axiomatize a notion of complexity and will import it via the module system. *)
Module Type CostModel.

  (** There is a relation between types representing terms and types representing
    complexity bounds over the latter type. *)
  Parameter complexity_type : Type -> Type -> Prop.

  (* TODO: we might later need to know that this is relation describes a
    partial function. *)

  (** Such type relations will be stored in a typeclass. *)
(*   Class CT A B := {is_complexity_type : complexity_type A B}. *)

  (* Extract the type of complexity bounds from a typeclass instance. *)
(*   Definition ℂT A {B} `{CT A B} := B. *)

  (** There is a notion of complexity terms to complexity bounds. *)
  Parameter has_complexity  : forall {A B : Type}, A -> B -> Prop.
  (* TODO: for now, we require [has_complexity] to relate elements whose
    types are related by CT. We'll see if this is required. *)

  (** Complexity bounds are preserved by some equivalence relation (on terms)
    and pre-order (on complexity bounds). *)
  (* TODO: maybe we can assume an intentional notion of complexity and define
    an extensional one on top of it *)
  Parameter ext_eq : forall {A}, A -> A -> Prop.
  Parameter ex_eq_rel : forall A, Equivalence (@ext_eq A).
  Global Existing Instance ex_eq_rel.

  Parameter bound_order : forall {B}, B -> B -> Prop.
  Parameter bound_order_po : forall B, PreOrder (@bound_order B).
  Global Existing Instance bound_order_po.

  Parameter has_complexity_ext_eq: forall {A B},
    Proper ((ext_eq) ==> (bound_order) ==> impl) (@has_complexity A B).
  Global Existing Instance has_complexity_ext_eq.

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  Class ComplexityBound {A B} (f : A) (c : B) := {CB : has_complexity f c}.

  Global Instance ComplexityBound_ext_eq: forall {A B},
    Proper ((ext_eq) ==> (bound_order) ==> impl) (@ComplexityBound A B).
  Proof. intros ????????[?]. constructor. eapply has_complexity_ext_eq; eauto. Qed.

  (** Useful tactics *)
  (* Replaces the complexity bound with an evar.
   The complexity bound goal will eventually need to be taken from the shelf. *)
  Ltac capply := eapply (fun f => ComplexityBound_ext_eq f f); [reflexivity|shelve|].

  (* Tactic to replace the function with an extensionally equivalent one in
    a [ComplexityBound] goal *)
    Ltac change_fun_with f' := match goal with
  | |- ComplexityBound ?f ?c => 
      eapply (ComplexityBound_ext_eq f' f _ c c (ltac:(reflexivity)))
  end.

End CostModel.

(** ------------------------------------------------------------------------- *)

(** An example of specialization of the cost model to handle time complexity of
  higher-order functions. *)
Module Type BasicTimeCostModel (Import CM : CostModel).

  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat, 
  or make mistakes anymore *)

  (** For function types, their complexity is a function taking as input
    an input of the function, and its complexity.
    Contrary to Künze & Forster, we use a record ; we will see if this helps. *)
  Record ℂI (A CA : Type) := { ival : A; icomp : CA}.
  Infix "⋊" := (Build_ℂI _ _) (at level 40).
  Global Arguments ival {_} {_}.
  Global Arguments icomp {_} {_}.

  (** Similarly, the complexity bound of a function outputs both a normalisation
  cost and the complexity of the output. *)
  Record ℂO CA := { ocost : nat; ocomp : CA }.
  Infix "⋉" := (Build_ℂO _) (at level 40).
  Global Arguments ocost {_}.
  Global Arguments ocomp {_}.

  (* Adds a normalisation cost to a complexity bound *)
  Definition cost_add {C} (n : nat) (b : ℂO C) : ℂO C :=
    {| ocost := n + ocost b ; ocomp := ocomp b |}.

  Global Infix "⊕" := cost_add (at level 60, right associativity).

  (** The type of complexity bounds for functions is built from ℂI and ℂO:
    given an input annotated with its complexity, output a cost and
    and an output annotated with its complexity.
    This is slightly different from coq-library-complexity, where the output
    value is not kept. *)
(*   Parameter fun_CT : forall A B {CA CB} `{CT A CA} `{CT B CB},
    CT (A -> B) (ℂI A -> ℂO CB).
  Global Existing Instance fun_CT. *)

  (* The ordering on complexity bounds is compatible with the pointwise ordering *)
  Parameter bound_order_ext_eq : forall {A B},
    forall (f g : A -> B), (forall x, bound_order (f x) (g x)) -> @bound_order (A -> B) f g.

(*   (* Useful functions to express complexity bounds *)
  (* Cost of applying a function of (input) complexity cg to an argument
    of (input) complexity ca. *)
  Definition cost_apply {A B CA CB} `{CT A CA} `{CT B CB}
    (cg : ℂI (A -> B)) (ca : ℂI A) : nat := ocost (icomp cg ca). *)

  (* More conveniently maybe, keep outputs together with output complexity so
    that we have a monad. *)
  Definition ret {A} : A -> ℂO A := fun ca => 0 ⋉ ca.

  (** Apply a function -- annotated with its complexity -- to an argument
    -- also annotated with its complexity -- and get a cost together with
    the output -- annotated with its complexity *)
  Definition IbindI {A B CA CB}
    (cx : ℂI A CA) (cg : ℂI (A -> B) (ℂI A CA -> ℂO CB)) : ℂO (ℂI B CB) :=
    {| ocost := ocost (icomp cg cx) ; ocomp :=
       {| ival := ival cg (ival cx); icomp := ocomp (icomp cg cx) |}
    |}.

(*   Definition bind {A B CA CB} `{CT A CA} `{CT A CB}
    : ℂO (ℂI A) -> ℂO (ℂI A -> ℂO CB) -> ℂO (ℂI B) := fun oa f =>
    (ocost f + ocost oa) ⊕ ocomp f (ocomp oa).
    (* cost of evaluation the input, plus cost of applying f to it *) *)
 
  Global Infix "I>>=I" := (IbindI) (at level 40).
  
  Definition ObindI {A B CA CB}
    (cx : ℂO (ℂI A CA)) (cg : ℂI (A -> B) _) : ℂO (ℂI B CB) :=
      ocost cx ⊕ IbindI (ocomp cx) cg.
  Global Infix "O>>=I" := (ObindI) (at level 40).

  Definition IbindO {A B CA CB}
    (cx : ℂI A CA) (cg : ℂO (ℂI (A -> B) _)) : ℂO (ℂI B CB) :=
      ocost cg ⊕ IbindI cx (ocomp cg).
  Global Infix "I>>=O" := (IbindO) (at level 40).

  Definition ObindO {A B CA CB}
    (cx : ℂO (ℂI A CA)) (cg : ℂO(ℂI (A -> B) _)) : ℂO (ℂI B CB) :=
    (ocost cx + ocost cg) ⊕ IbindI (ocomp cx) (ocomp cg).
  Global Infix "O>>=O" := (ObindO) (at level 40).

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  Parameter id_complexity : forall {A CA},
    ComplexityBound (fun (x : A) => x) (fun (ca : ℂI A CA) => (1 ⋉ icomp ca) : ℂO CA).
  Global Existing Instance id_complexity.
  
  (* Note : we are using the unfolding of [@id A] here so that typeclass
    resolution works *)


  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B CA CB}
    {v : A} {f : A -> B} {cv : CA} (cf : ℂI A CA -> ℂO CB),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound (f v: B) (ocomp (cf (v ⋊ cv))).

  (** We will conveniently compute within the ℂO (ℂI A) monad where we have
    everything : cost, value and complexity, but we will eventually need to
    escape it into ℂO CA. *)
  (** TODO: terrible naming. And we probably don't need all these bind. *)
  Definition OIbindO {A CA} (cx : ℂO (ℂI A CA)) : ℂO CA :=
    ocost cx ⋉ icomp (ocomp cx).
  Global Notation "a '>>|'" := (OIbindO a) (at level 150).

  (* Unary composition *)
  (* It produces a value whose complexity is obtained by composing the complexity
     of the three inputs ; the normalisation cost is obtained by two successive
     applications. *)
  Parameter comp1_complexity : forall {A B C CA CB CC},
  ComplexityBound (@compose A B C)
    (fun (cf : ℂI (B -> C) (ℂI B CB -> ℂO CC)) => 1 ⋉
     fun (cg : ℂI (A -> B) (ℂI A CA -> ℂO CB)) => 1 ⋉ fun (ca : ℂI A CA) =>
      (1 ⋉ ca) O>>=I cg O>>=I cf >>|
    ).
  (* TODO: fancy notation for complexity type of A -> B? *)

  (* More convenient: the instantiation direct application of compose.
    TODO: do we need both? *)
  Parameter compose_complexity : forall {A B C CA CB CC}
  (f : B -> C) (cf : ℂI B CB -> ℂO CC) (g : A -> B) (cg : ℂI A CA -> ℂO CB),
  ComplexityBound f cf ->
  ComplexityBound g cg ->
  ComplexityBound (compose f g : A -> C)
                  (fun ca => ca I>>=I (g ⋊ cg) O>>=I (f ⋊ cf) >>|).
  Global Existing Instance compose_complexity.

  Parameter constant_complexity : forall {A B CA CB} b {cb},
  ComplexityBound (b : B) (cb : CB) ->
  ComplexityBound (fun (_ : A) => b) (fun (_ : ℂI A CA) => 1 ⋉ cb).
  (* TODO: should this 1 be kept? This will add overhead in many cases.
    Same question for id *)
  Global Existing Instance constant_complexity.
  
  (* Parameter ext_eq_fun : forall {A B} (f g : A -> B),
    (forall x, ext_eq (f x) (g x)) -> ext_eq f g. *)
  Parameter ext_eq_dep_fun : forall {A B} (f g : forall a : A, B a),
    (forall x, ext_eq (f x) (g x)) -> ext_eq f g.

  Lemma ext_eq_eq {A} (a b : A): a = b -> ext_eq a b.
  Proof. intros; subst. reflexivity. Qed.

  Parameter bound_order_output: forall {A} (a b : ℂO A),
    bound_order a b <-> (ocost a <= ocost b /\ bound_order (ocomp a) (ocomp b)).

  Lemma bound_order_eq {A} (a b : A): a = b -> bound_order a b.
  Proof. intros; subst. reflexivity. Qed.
  
  Lemma bound_order_unit (a b : unit) : bound_order a b.
  Proof. destruct a, b. reflexivity. Qed.

  (* Simple tactic that will be used to prove ComplexityBound goals.
    Maybe elaborated later. *)
  Ltac ctac := typeclasses eauto.
End BasicTimeCostModel.