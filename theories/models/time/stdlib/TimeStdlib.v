(** * The time cost model with the analyses of the standard library

    Each analysis is a functor over the model with the previous ones
    ([TimeBoolPair], [TimeNat], [TimePos], ...). An application is a
    functor over [TimeStdlib], whose bounds typeclass search finds. The
    bounds on [Z] ([ZComplexity], over [TimePos]) are apart: an
    application includes them if it needs them. *)

From Complexity Require Export PosComplexity HOOptionComplexity HOListComplexity ListComplexity
  SumComplexity.

Module Type TimeStdlib := TimePos <+ HOOptionComplexity <+ HOListComplexity <+ ListComplexity
  <+ SumComplexity <+ SumOptionComplexity.
