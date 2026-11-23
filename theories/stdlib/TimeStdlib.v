(** * The time cost model with the analyses of the standard library

    Each analysis is a functor over the model with the previous ones
    ([TimeBoolPair], [TimeNat], [TimePos], ...). An application is a
    functor over [TimeStdlib], whose bounds typeclass search finds. *)

From Complexity Require Export HOOptionComplexity HOListComplexity ListComplexity ZComplexity
  SumComplexity.

Module Type TimeStdlib := TimePos <+ HOOptionComplexity <+ HOListComplexity <+ ListComplexity
  <+ ZComplexity <+ SumComplexity.
