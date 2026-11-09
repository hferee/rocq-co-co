(** * The cost model

    The axioms ([CostModelCore]) with the bounds in the size of the inputs
    that they define ([Bounds]): linear and polynomial bounds are then
    shared by all the analyses over a cost model, and their instances found
    by typeclass search. At higher types, the higher-order polynomial
    bounds, and the sizes of functionals ([HOBounds]). *)

From Complexity Require Export CostModelCore Bounds HOBounds.

(** [CostModelCore.CostModelCore]: the module type, not the library. *)
Module Type CostModel := CostModelCore.CostModelCore <+ Bounds <+ HOBounds.
