(** * The compilers, and the one used by [cbound]

    A compiler is a tactic on a goal [ComplexityBound f c] that replaces
    [f] by a convertible term built from the combinators
    ([compile_goal_with], [CompileCommon]): closure conversion
    ([ClosureCompile]), the default, or bracket abstraction
    ([BracketCompile]). *)

From Ltac2 Require Import Ltac2.
From Complexity Require Export CompileCommon ClosureCompile BracketCompile.

(** The compiler of [cbound], for the goal and the functionals of recursive
    functions. A file selects another one for its proofs with
<<
      #[local] Ltac2 Set ccompiler := fun () => bracket_compile_goal ().
>>
    so that the analyses with several compilers can be compared
    ([BracketComparison]). *)
Ltac2 mutable ccompiler : unit -> unit := fun () => closure_compile_goal ().

(** Compile the function of the goal, with [ccompiler]. *)
Ltac compile_goal := ltac2:(ccompiler ()).


