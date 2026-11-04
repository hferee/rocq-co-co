(** * Cost model for booleans *)

From Complexity Require Import CostModel HOCostModel Combinators.

(** ** Case combinator (see [Combinators]) *)

Definition bool_case {A : Type} (t f : unit -> A) (b : bool) : A :=
  match b with true => t tt | false => f tt end.

#[global] Typeclasses Opaque bool_case.
#[global] Hint Unfold bool_case : comb.

Module Type BoolTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** Booleans are ground data. *)
  Parameter Repr_bool : Ground bool.
  Global Existing Instance Repr_bool.

  Parameter bool_complexity : forall b : bool, ComplexityBound b tt.
  Global Existing Instance bool_complexity.

  (** Case analysis, with the branches as thunks: only the selected branch is
      evaluated. [if] and every match on a boolean are compiled to it. *)
  Parameter bool_case_complexity : forall {A CA} `{Repr A CA},
    ComplexityBound (@bool_case A)
      (fun ct : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cf : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun cb : ℂI bool unit => 1 ⊕
         if val cb then pot ct (tt ⋊ tt) else pot cf (tt ⋊ tt)).
  Global Existing Instance bool_case_complexity.
End BoolTimeCostModel.
