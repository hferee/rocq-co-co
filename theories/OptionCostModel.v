(** * Cost model for options (of ground data) *)

From Complexity Require Import CostModel HOCostModel Combinators.

(** ** Case combinator (see [Combinators]) *)

Definition option_case {X A : Type} (s : X -> A) (z : unit -> A) (o : option X) : A :=
  match o with Some x => s x | None => z tt end.

#[global] Typeclasses Opaque option_case.
#[global] Hint Unfold option_case : comb.

Module Type OptionTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (** Options of ground data are ground data. *)
  Parameter option_complexity : forall {A} (o : option A), ComplexityBound o tt.
  Global Existing Instance option_complexity.

  Parameter Some_complexity : forall {A},
    ComplexityBound (@Some A) (fun _ : ℂI A unit => 1 ⋉ tt).
  Global Existing Instance Some_complexity.

  Parameter option_case_complexity : forall {X A CA},
    ComplexityBound (@option_case X A)
      (fun cs : ℂI (X -> A) (ℂI X unit -> ℂO CA) => 0 ⋉
       fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 0 ⋉
       fun co : ℂI (option X) unit => 1 ⊕
         match ival co with
         | Some x => icomp cs (x ⋊ tt)
         | None => icomp cz (tt ⋊ tt)
         end).
  Global Existing Instance option_case_complexity.
End OptionTimeCostModel.
