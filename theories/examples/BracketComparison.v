(** * Bracket abstraction against closure conversion

    The same functions compiled by bracket abstraction ([BracketCompile],
    the former compiler), with the smallest constants. Their bounds with
    closure conversion ([Compile]) are in [stdlib]: closures make
    partial applications and functions of several arguments cheaper, and
    the recursion of one-argument functions dearer (the function is found
    deeper in the environment of its recursive call).

    | function    | bracket abstraction | closure conversion  |
    | [Nat.add]   | [35 ⋉ 55 n + 7]     | [5 ⋉ 36 n + 14]     |
    | [Nat.mul]   | [9 ⋉ n (55 m + 67) + 13] | [5 ⋉ n (36 m + 52) + 10] |
    | [andb]      | [1 ⋉ 8]             | [2 ⋉ 14]            |
    | [orb]       | [1 ⋉ 6]             | [2 ⋉ 12]            |
    | [length]    | [10 len + 8]        | [17 len + 9]        |
    | [Pos.succ]  | [11 size]           | [18 size]           | *)

From Complexity Require Import TimeCostModel CostModel TimeBasic TimeDatatypes Combinators
  Compile BracketCompile TimeCombinators TimeFix.
From Stdlib Require Import Program.Basics List Arith PArith Lia.

Module BracketComparison (Import M : TimeCostModel).

  (** [cbound] with bracket abstraction. *)
  Ltac bcbound :=
    (tryif crec then [> bcbc | idtac]
     else (eapply ComplexityBound_ext_eq; [idtac | unfold_fun; bcbc]));
    cfinish.

  Lemma add_complexity : ComplexityBound Nat.add
    (fun cn => 35 ⋉ fun cm => (55 * val cn + 7) ⋉ tt).
  Proof. bcbound. Qed.
  Existing Instance add_complexity.

  Lemma mul_complexity : ComplexityBound Nat.mul
    (fun cn => 9 ⋉ fun cm =>
       (val cn * (55 * val cm + 67) + 13) ⋉ tt).
  Proof. bcbound. Qed.

  Lemma andb_complexity : ComplexityBound andb
    (fun ca => 1 ⋉ fun cb => 8 ⋉ tt).
  Proof. bcbound. Qed.

  Lemma orb_complexity : ComplexityBound orb
    (fun ca => 1 ⋉ fun cb => 6 ⋉ tt).
  Proof. bcbound. Qed.

  Lemma length_complexity {A} `{Ground A} : ComplexityBound (@length A)
    (fun cl => (10 * length (val cl) + 8) ⋉ tt).
  Proof. bcbound. Qed.

  Lemma succ_complexity : ComplexityBound Pos.succ
    (fun cp => (11 * Pos.size_nat (val cp)) ⋉ tt).
  Proof. bcbound. Qed.
End BracketComparison.
