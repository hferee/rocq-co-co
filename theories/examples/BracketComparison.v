(** * Bracket abstraction against closure conversion

    The same functions compiled by bracket abstraction ([BracketCompile],
    the former compiler), with the smallest constants. Their bounds with
    closure conversion ([ClosureCompile], the default) are in [stdlib].
    Both compilers use the case combinators, which take their branches and
    their matched value as functions of an environment, and the same
    functionals for the recursive functions. Closure conversion passes the
    environment of the closure; bracket abstraction passes the matched
    variable, or [tt], and reads the arguments of the constructors in it,
    and threads each variable through the combinators of every subterm:
    closure conversion is cheaper on all of them.

    | function    | bracket abstraction          | closure conversion       |
    | [Nat.add]   | [1 +> 28 n + 26]             | [1 +> 14 n + 10]         |
    | [Nat.mul]   | [1 +> n (28 m + 60) + 26]    | [1 +> n (14 m + 30) + 8] |
    | [andb]      | [1 +> 11]                    | [1 +> 4]                 |
    | [orb]       | [1 +> 9]                     | [1 +> 4]                 |
    | [length]    | [23 len + 17]                | [16 len + 6]             |
    | [Pos.succ]  | [27 size]                    | [14 size]                | *)

From Complexity Require Import TimeCostModel.
From Stdlib Require Import PArith.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** [cbound] with bracket abstraction in this file ([ccompiler], [Compile]):
    the analyses are those of [cbound], with the same functionals for the
    recursive functions ([crec_env], [crec]), only the compiler changes. *)
#[local] Ltac2 Set ccompiler := fun () => bracket_compile_goal ().

Module BracketComparison (Import Time : TimeCostModel).

  Lemma add_complexity : Time.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (28 * val cn + 26) >|).
  Proof. cbound. Qed.
  Existing Instance add_complexity.

  Lemma mul_complexity : Time.ComplexityBound Nat.mul
    (fun cn => 1 +> fun cm =>
       (val cn * (28 * val cm + 60) + 26) >|).
  Proof. cbound. Qed.

  Lemma andb_complexity : Time.ComplexityBound andb
    (fun ca => 1 +> fun cb => 11 >|).
  Proof. cbound. Qed.

  Lemma orb_complexity : Time.ComplexityBound orb
    (fun ca => 1 +> fun cb => 9 >|).
  Proof. cbound. Qed.

  Lemma length_complexity {A} `{Ground A} : Time.ComplexityBound (@length A)
    (fun cl => (23 * length (val cl) + 17) >|).
  Proof. cbound. Qed.

  Lemma succ_complexity : Time.ComplexityBound Pos.succ
    (fun cp => (27 * Pos.size_nat (val cp)) >|).
  Proof. cbound. Qed.
End BracketComparison.
