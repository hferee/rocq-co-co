(** * The compilers, and the one used by [cbound]

    [cbound] compiles the function of its goal (and the functionals of
    recursive functions) with the compiler [ccompiler], a mutable Ltac2
    definition. The compilers:
    - closure conversion ([ClosureCompile]), the default: every lambda
      becomes a closure, its code applied to its environment;
    - bracket abstraction ([BracketCompile]), the former compiler, by
      Turner's combinators.
    A file selects another compiler for its proofs with, for instance,
<<
      #[local] Ltac2 Set ccompiler := fun () => bracket_compile_goal ().
>>
    so that the analyses of the same functions with several compilers can be
    compared ([BracketComparison]). A compiler is a tactic on a goal
    [ComplexityBound f c] that replaces [f] by a convertible term built from
    the combinators ([compile_goal_with], [CompileCommon]). *)

From Ltac2 Require Import Ltac2.
From Complexity Require Export CompileCommon ClosureCompile BracketCompile.

Ltac2 mutable ccompiler : unit -> unit := fun () => closure_compile_goal ().

(** Compile the function of the goal, with [ccompiler]. *)
Ltac compile_goal := ltac2:(ccompiler ()).

(** Compile the function of a [ComplexityBound] goal and search for its
    complexity. Complexity types left undetermined (those of unused
    arguments) can be anything. *)
Ltac cbc := unshelve (compile_goal; typeclasses eauto); try exact unit.
