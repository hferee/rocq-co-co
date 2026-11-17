(** * The time cost model with the analyses of the standard library

    The analyses of the standard library are layers over the time cost model,
    each one a functor over the previous ones ([TimeBoolPair], [TimeNat],
    [TimePos]); an application that uses them is a functor over
    [TimeStdlib], which finds their bounds by typeclass search. *)

From Complexity Require Export ListComplexity ZComplexity SumComplexity.

Module Type TimeStdlib := TimePos <+ ListComplexity <+ ZComplexity <+ SumComplexity.
