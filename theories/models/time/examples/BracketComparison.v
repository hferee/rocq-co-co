(** * Bracket abstraction against closure conversion

    The same functions compiled by bracket abstraction ([BracketCompile]),
    with the smallest constants; their bounds with closure conversion, the
    default, are in [stdlib] and given below. Both compilers use the case
    combinators and the same functionals for the recursive functions.
    Closure conversion passes the environment of the closure; bracket
    abstraction passes the matched variable, or [tt], reads the arguments
    of the constructors in it, and threads each variable through the
    combinators of every subterm: closure conversion is cheaper on all of
    them. *)

From Complexity Require Import TimeCostModel.
From Stdlib Require Import PArith.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

(** [cbound] with bracket abstraction in this file ([ccompiler], [Compile]):
    the analyses are those of [cbound], with the same functionals for the
    recursive functions ([crec_env], [crec]), only the compiler changes. *)
#[local] Ltac2 Set ccompiler := fun () => bracket_compile_goal ().

Module BracketComparison (Import Time : TimeCostModel).

  (** Closure conversion: [1 +> 14 n + 10]. *)
  Lemma add_complexity : Time.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (28 * val cn + 26) >|).
  Proof. cbound. Qed.
  Existing Instance add_complexity.

  (** Closure conversion: [1 +> n (14 m + 30) + 8]. *)
  Lemma mul_complexity : Time.ComplexityBound Nat.mul
    (fun cn => 1 +> fun cm =>
       (val cn * (28 * val cm + 60) + 26) >|).
  Proof. cbound. Qed.

  (** Closure conversion: [1 +> 4], as for [orb]. *)
  Lemma andb_complexity : Time.ComplexityBound andb
    (fun ca => 1 +> fun cb => 11 >|).
  Proof. cbound. Qed.

  Lemma orb_complexity : Time.ComplexityBound orb
    (fun ca => 1 +> fun cb => 9 >|).
  Proof. cbound. Qed.

  (** Closure conversion: [16 len + 6]. *)
  Lemma length_complexity {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Time.ComplexityBound (@length A)
    (fun cl => (23 * length (val cl) + 17) >|).
  Proof. cbound. Qed.

  (** Closure conversion: [14 size]. *)
  Lemma succ_complexity : Time.ComplexityBound Pos.succ
    (fun cp => (27 * Pos.size_nat (val cp)) >|).
  Proof. cbound. Qed.
End BracketComparison.
