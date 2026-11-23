(** * The cost model

    The axioms ([CostModelCore]), the ground types ([GroundTypes]) and the
    bounds in the sizes of the inputs that they define ([Bounds],
    [HOBounds]), with their tactics ([BoundsTactics]): these bounds are
    shared by all the analyses over a cost model. *)

From Complexity Require Export CostModelCore GroundTypes Bounds BoundsTactics HOBounds.

Module Type CostModel := GroundCostModel <+ Bounds <+ BoundsTactics <+ HOBounds.

(** Costs in [nat]: time and the counts of operations. *)
Module Type NatCostModel := CostModel with Definition Cost := nat with Definition cost_alg := nat_alg.
