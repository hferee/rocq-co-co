(** * Bracket abstraction against closure conversion

    The same functions compiled by bracket abstraction ([BracketCompile],
    the former compiler), with the smallest constants. Their bounds with
    closure conversion ([Compile]) are in [stdlib]. Both compilers use the
    case combinators, which take their branches and their matched value as
    functions of an environment. Closure conversion passes the environment
    of the closure; bracket abstraction passes the matched variable, or
    [tt], and reads the arguments of the constructors in it: these reads
    are the overhead of bracket abstraction on the recursion of [length]
    and [Pos.succ]. Closures make functions of several arguments cheaper,
    and partial applications slightly dearer.

    | function    | bracket abstraction      | closure conversion       |
    | [Nat.add]   | [17 +> 35 n + 14]         | [5 +> 25 n + 6]           |
    | [Nat.mul]   | [17 +> n (35 m + 69) + 16] | [5 +> n (25 m + 39) + 6] |
    | [andb]      | [1 +> 11]                 | [2 +> 6]                  |
    | [orb]       | [1 +> 9]                  | [2 +> 6]                  |
    | [length]    | [16 len + 13]            | [17 len + 7]             |
    | [Pos.succ]  | [20 size]                | [15 size]                | *)

From Complexity Require Import TimeCostModel BracketCompile.
From Stdlib Require Import PArith.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module BracketComparison (Import Time : TimeCostModel).

  (** [cbound] with bracket abstraction ([bcbc] with the search of
      [cbound], [csearch]). *)
  Ltac bcbc_found := unshelve (bracket_compile_goal; csearch); try exact unit.
  Ltac bcbound :=
    (tryif crec then [> bcbc_found | idtac]
     else (eapply ComplexityBound_mono; [idtac | unfold_fun; bcbc_found]));
    cfinish.

  Lemma add_complexity : Time.ComplexityBound Nat.add
    (fun cn => 17 +> fun cm => (35 * val cn + 14) >|).
  Proof. bcbound. Qed.
  Existing Instance add_complexity.

  Lemma mul_complexity : Time.ComplexityBound Nat.mul
    (fun cn => 17 +> fun cm =>
       (val cn * (35 * val cm + 69) + 16) >|).
  Proof. bcbound. Qed.

  Lemma andb_complexity : Time.ComplexityBound andb
    (fun ca => 1 +> fun cb => 11 >|).
  Proof. bcbound. Qed.

  Lemma orb_complexity : Time.ComplexityBound orb
    (fun ca => 1 +> fun cb => 9 >|).
  Proof. bcbound. Qed.

  Lemma length_complexity {A} `{Ground A} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 13) >|).
  Proof. bcbound. Qed.

  Lemma succ_complexity : Time.ComplexityBound Pos.succ
    (fun cp => (20 * Pos.size_nat (val cp)) >|).
  Proof. bcbound. Qed.
End BracketComparison.
