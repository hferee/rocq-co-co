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
  Parameter bool_complexity : forall b : bool, ComplexityBound b tt.
  Global Existing Instance bool_complexity.

  (** Case analysis, with the branches as thunks: only the selected branch is
      evaluated. [if] and every match on a boolean are compiled to it. *)
  Parameter bool_case_complexity : forall {A CA},
    ComplexityBound (@bool_case A)
      (fun ct : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cf : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun cb : ℂI bool unit => 1 ⊕
         if ival cb then icomp ct (tt ⋊ tt) else icomp cf (tt ⋊ tt)).
  Global Existing Instance bool_case_complexity.
End BoolTimeCostModel.
