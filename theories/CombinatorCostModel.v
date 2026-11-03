(** * Cost model for the combinators of [Combinators]

    [Compile.compile] turns every lambda-term (and [match], through the case
    combinators of the datatype models) into a convertible term built from
    [Kc], [Ic], [compose], [Cc], [Sc], the lazy closure [Lc] and the closure
    marker [Lm]. The combinators are higher-order constants: their
    complexities take the complexities of their (functional) arguments, so
    that typeclass search finds the complexity of a compiled term by
    following its structure ([cbc]). The costs are those of a closure
    machine (see below). *)

From Complexity Require Import CostModel HOCostModel Combinators Compile.
From Stdlib Require Import Program.Basics Lia.

Module Type CombinatorTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** The complexity of an application [f v] is the output complexity of [f]
      at [v] ([apply_complexity]). As an instance of lowest priority, it lets
      typeclass search follow the structure of compiled terms. *)
  Global Existing Instance apply_complexity | 100.

  (** ** Costs

      A step costs one when it may duplicate work: a beta-step (entering the
      closure [Lc g x]), the duplication of an argument ([Sc]), and, in the
      models of the datatypes, a case analysis, an unfolding of a fixpoint
      and the constructors. The other steps only route values, as the
      environment of a closure machine: partial applications (building
      closures), and the affine combinators [Kc], [Ic], [Lm], [compose],
      [Cc] and those below. They are free: a term made of free steps does at
      most as much work as its size, so that the real work of an evaluation
      is bounded by its cost times the size of the program. *)

  Parameter Kc_complexity : forall {A B CA CB},
    ComplexityBound (@Kc A B) (fun ca : ℂI A CA => 0 ⋉ (fun _ : ℂI B CB => 0 ⋉ icomp ca)).
  Global Existing Instance Kc_complexity.

  Parameter Ic_complexity : forall {A CA},
    ComplexityBound (@Ic A) (fun ca : ℂI A CA => 0 ⋉ icomp ca).
  Global Existing Instance Ic_complexity.

  (** [Lm c] is the closure [c]. *)
  Parameter Lm_complexity : forall {A CA},
    ComplexityBound (@Lm A) (fun ca : ℂI A CA => 0 ⋉ icomp ca).
  Global Existing Instance Lm_complexity.

  (** [compose] as a constant, whereas [compose_complexity] requires fixed
      arguments. *)
  Parameter compose_hcomplexity : forall {A B C CA CB CC},
    ComplexityBound (@compose A B C)
      (fun cf : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 0 ⋉
       fun cg : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 0 ⋉
       fun ca : ℂI A CA => (ca I>>=I cg O>>=I cf >>|)).
  Global Existing Instance compose_hcomplexity.

  (** [Cc f a x = f x a]. *)
  Parameter Cc_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Cc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun ca : ℂI A CA => 0 ⋉
       fun cx : ℂI X CX => ((ca I>>=O (cx I>>=I cf)) >>|)).
  Global Existing Instance Cc_complexity.

  (** [Sc f g x = f x (g x)]: the bound variable is used twice. *)
  Parameter Sc_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Sc X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 0 ⋉
       fun cx : ℂI X CX => 1 ⊕ (((cx I>>=I cg) O>>=O (cx I>>=I cf)) >>|)).
  Global Existing Instance Sc_complexity.

  (** [Lc g x] is a closure: [g x] is evaluated when the next argument is
      supplied, which is a beta-step. *)
  Parameter Lc_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Lc X A B)
      (fun cg : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun cx : ℂI X CX => 0 ⋉
       fun ca : ℂI A CA => 1 ⊕ ((ca I>>=O (cx I>>=I cg)) >>|)).
  Global Existing Instance Lc_complexity.

  (** Branch binders ([Lf], [Lfc]) and delayed computations ([Dl], [Rc],
      [Rc2], [Su]) are affine: they are free. *)
  Parameter Lf_complexity : forall {A CA},
    ComplexityBound (@Lf A) (fun ca : ℂI A CA => 0 ⋉ icomp ca).
  Global Existing Instance Lf_complexity.

  Parameter Lfc_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Lfc X A B)
      (fun cg : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun cx : ℂI X CX => 0 ⋉
       fun ca : ℂI A CA => ((ca I>>=O (cx I>>=I cg)) >>|)).
  Global Existing Instance Lfc_complexity.

  Parameter Dl_complexity : forall {X B CX CB},
    ComplexityBound (@Dl X B)
      (fun ch : ℂI (unit -> B) (ℂI unit unit -> ℂO CB) => 0 ⋉
       fun _ : ℂI X CX => icomp ch (tt ⋊ tt)).
  Global Existing Instance Dl_complexity.

  Parameter Rc_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Rc X A B)
      (fun ch : ℂI (unit -> A -> B) (ℂI unit unit -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun cg : ℂI (X -> A) (ℂI X CX -> ℂO CA) => 0 ⋉
       fun cx : ℂI X CX => (((cx I>>=I cg) O>>=O ((tt ⋊ tt) I>>=I ch)) >>|)).
  Global Existing Instance Rc_complexity.

  Parameter Rc2_complexity : forall {X A B CX CA CB},
    ComplexityBound (@Rc2 X A B)
      (fun cf : ℂI (X -> A -> B) (ℂI X CX -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun ch : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cx : ℂI X CX => ((((tt ⋊ tt) I>>=I ch) O>>=O (cx I>>=I cf)) >>|)).
  Global Existing Instance Rc2_complexity.

  Parameter Su_complexity : forall {A B CA CB},
    ComplexityBound (@Su A B)
      (fun cf : ℂI (unit -> A -> B) (ℂI unit unit -> ℂO (ℂI A CA -> ℂO CB)) => 0 ⋉
       fun cg : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cu : ℂI unit unit => (((cu I>>=I cg) O>>=O (cu I>>=I cf)) >>|)).
  Global Existing Instance Su_complexity.

  (** Decompose [bound_order] goals into inequalities between costs. The
      arguments of functions are named as in the right-hand side (usually
      the claimed bound). *)
  Ltac bo_split :=
    repeat match goal with
    | |- @bound_order (ℂO _) _ _ => apply bound_order_output; split
    | |- @bound_order (_ -> _) _ _ => ext_intro constr:(@bound_order_ext_eq)
    | |- @bound_order unit _ _ => apply bound_order_unit
    end.

  (** Destruct the complexities of the inputs of ground type: [c : ℂI A unit]
      becomes the value of the input, still named [c]. *)
  Ltac destr_inputs :=
    repeat match goal with
    | c : ℂI _ unit |- _ => let v := fresh "v" in destruct c as [v []]; rename v into c
    end.

  (** Compile the function of a [ComplexityBound] goal and search for its
      complexity. Complexity types left undetermined (those of unused
      arguments) can be anything. *)
  Ltac cbc := unshelve (compile_goal; typeclasses eauto); try exact unit.
End CombinatorTimeCostModel.
