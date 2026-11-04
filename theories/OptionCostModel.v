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
  Parameter Repr_option : forall {A}, Ground A -> Ground (option A).
  Global Existing Instance Repr_option.

  (** [None] is a value; the other options are built with [Some]. *)
  Parameter None_complexity : forall {A} `{Ground A}, ComplexityBound (@None A) tt.
  Global Existing Instance None_complexity.

  Parameter Some_complexity : forall {A} `{Ground A},
    ComplexityBound (@Some A) (fun _ : ℂI A unit => 1 ⋉ tt).
  Global Existing Instance Some_complexity.

  Parameter option_case_complexity : forall {X A CA} `{Ground X} `{Repr A CA},
    ComplexityBound (@option_case X A)
      (fun cs : ℂI (X -> A) (ℂI X unit -> ℂO CA) => 1 ⋉
       fun cz : ℂI (unit -> A) (ℂI unit unit -> ℂO CA) => 1 ⋉
       fun co : ℂI (option X) unit => 1 ⊕
         match val co with
         | Some x => pot cs (x ⋊ tt)
         | None => pot cz (tt ⋊ tt)
         end).
  Global Existing Instance option_case_complexity.
End OptionTimeCostModel.
