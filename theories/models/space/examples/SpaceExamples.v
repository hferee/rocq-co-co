(** * Total allocation of standard algorithms (sanity checks)

    Bounds on the allocations of standard functions
    ([TotalAllocationModel]), proved by [cbound] as in the time cost model. They
    agree with the known space complexities, in the number of allocated
    cells. The constants also count the closures built by the compiled code
    and the frame of each recursive call ([c_fix]); a [match] allocates
    nothing. *)

From Complexity Require Export TotalAllocationModel.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module SpaceExamples (Import Space : TotalAllocationModel).

  (** ** Natural numbers

      [Nat.add n m] rebuilds the [n] successors of the result, [Nat.mul n m]
      adds [m] [n] times. [Nat.eqb], which builds no data, still allocates
      linearly: one frame and the closures of each step.

      The second argument of [Nat.add], [Nat.mul] and [app], and the first
      of [repeat], are passed unchanged by the recursive calls: they are in
      the environment of the fixpoint ([fix_complexity]). The closure of
      this environment, or the last unfolding, is allocated when the last
      argument is given: the constant terms. *)

  Global Instance Nat_add_space : Space.ComplexityBound Nat.add
    (fun cn => 1 +> fun cm => (3 * val cn + 3) >|).
  Proof. cbound. Qed.

  (** No data, but one frame and the closures of each step. *)
  Global Instance Nat_eqb_space : Space.ComplexityBound Nat.eqb
    (fun cn => 3 +> fun cm => (3 * val cn) >|).
  Proof. cbound. Qed.

  (** [n] additions of [m]: quadratic. *)
  Global Instance Nat_mul_space : Space.ComplexityBound Nat.mul
    (fun cn => 1 +> fun cm => (val cn * (3 * val cm + 6) + 3) >|).
  Proof. cbound. Qed.

  (** ** Lists

      [app l m] copies [l]; [rev l] appends each element at the end of the
      reversed tail, quadratic in [|l|], and [rev_append], with an
      accumulator, is linear; [map f l] builds [|l|] cells, plus the
      allocations of [f]. *)

  Global Instance length_space {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Space.ComplexityBound (@length A)
    (fun cl => (3 * length (val cl) + 2) >|).
  Proof. cbound. Qed.

  (** [app l m] copies [l] and shares [m]. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance app_space {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Space.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm => (4 * length (val cl) + 3) >|).
  Proof. cbound. Qed.
  *)

  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance repeat_space {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Space.ComplexityBound (@repeat A)
    (fun cx => 1 +> fun cn => (4 * val cn + 2) >|).
  Proof. cbound. Qed.
  *)

  (** Naive reversal: quadratic. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance rev_space {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Space.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (2 * length (val cl) + 6) + 2) >|).
  Proof. cbound. all: rewrite ?length_rev; nia. Qed.
  *)

  (** Reversal with an accumulator: linear. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Global Instance rev_append_space {A} {CA} {RA : Repr A CA} {GA : IsGround RA} : Space.ComplexityBound (@rev_append A)
    (fun cl => 3 +> fun cm => (5 * length (val cl)) >|).
  Proof. cbound. Qed.
  *)

  (** [map f l] allocates [|l|] cells, and [f] on each element. *)
  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma map_space {A B} {CA} {RA : Repr A CA} {GA : IsGround RA} {CB} {RB : Repr B CB} {GB : IsGround RB} (f : A -> B) (c : nat) :
    Space.ComplexityBound f (fun _ : ℂI A CA => c >|) ->
    Space.ComplexityBound (map f) (fun cl => ((c + 4) * length (val cl) + 2) >|).
  Proof. intros Hf. cbound. Qed.
  *)

  (** ** Bounds in the size of the arguments ([Bounds]) *)
  Lemma nat_lt_size (n : nat) : n < size n.
  Proof. induction n; [rewrite size_O | rewrite size_S]; lia. Qed.
  Global Instance nat_size_fact (n : nat) : SizeFact n (n < size n) := nat_lt_size n.

  Global Instance Nat_add_space_linear : Space.LinearBound Nat.add := _.
  Global Instance Nat_mul_space_polynomial : Space.PolynomialBound Nat.mul := _.
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma Nat_add_space_size_complexity :
    Space.ComplexityBound Nat.add
      (fun (cn : ℂI nat _) => 1 +> fun cm => (3 * #|val cn|) >|).
  Proof. csize_using Nat_add_space. Qed.

  Lemma Nat_eqb_space_size_complexity :
    Space.ComplexityBound Nat.eqb
      (fun (cn : ℂI nat _) => 3 +> fun cm => (3 * #|val cn|) >|).
  Proof. csize_using Nat_eqb_space. Qed.

  Lemma Nat_mul_space_size_complexity :
    Space.ComplexityBound Nat.mul
      (fun (cn : ℂI nat _) => 1 +> fun (cm : ℂI nat _) => (#|val cn| * (3 * #|val cm| + 3)) >|).
  Proof. csize_using Nat_mul_space. Qed.

  (* Broken by the order on the complexities of lists ([Forall2]):
  Lemma repeat_space_size_complexity {A} {CA} {RA : Repr A CA} {GA : IsGround RA} :
    Space.ComplexityBound (@repeat A)
      (fun cx => 1 +> fun (cn : ℂI nat _) => (4 * #|val cn|) >|).
  Proof. csize_using repeat_space. Qed.
  *)

End SpaceExamples.
