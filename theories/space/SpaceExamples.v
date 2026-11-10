(** * Space complexity of standard algorithms (sanity checks)

    Bounds on the allocations of standard functions in the space cost model
    ([SpaceCostModel]), proved by [cbound] as in the time cost model. They
    agree with the known space complexities, in the number of allocated
    cells:
    - [Nat.add n m] rebuilds the [n] successors of the result: linear in
      [n]; [Nat.mul n m] adds [m] [n] times: [n * m];
    - [app l m] copies [l]: linear in [|l|];
    - [rev l] appends each element at the end of the reversed tail: the
      [i]-th append copies [i] cells, quadratic in [|l|]; [rev_append],
      with an accumulator, is linear;
    - [map f l] builds [|l|] cells, plus the allocations of [f];
    - [repeat x n] builds [n] cells; [length l] builds the [|l|]
      successors of its result.

    The constants also count the closures of the compiled code (the
    branches of a [match] are thunks, [Compile]) and the frame of each
    recursive call ([c_fix]). This is why [Nat.eqb], which builds no data,
    still allocates linearly: one frame and the closures of each step. *)

From Complexity Require Export SpaceCostModel.
From Stdlib Require Import List.
Import ListNotations.

Module SpaceExamples (Import Space : SpaceCostModel).

  (** ** Natural numbers *)

  Global Instance Nat_add_space : Space.ComplexityBound Nat.add
    (fun cn => 3 ⋉ fun cm => (7 * val cn + 3) ⋉ tt).
  Proof. cbound. Qed.

  (** No data, but one frame and the closures of each step. *)
  Global Instance Nat_eqb_space : Space.ComplexityBound Nat.eqb
    (fun cn => 3 ⋉ fun cm => (7 * val cn + 3) ⋉ tt).
  Proof. cbound. Qed.

  (** [n] additions of [m]: quadratic. *)
  Global Instance Nat_mul_space : Space.ComplexityBound Nat.mul
    (fun cn => 3 ⋉ fun cm => (val cn * (7 * val cm + 11) + 3) ⋉ tt).
  Proof. cbound. Qed.

  (** ** Lists *)

  Global Instance length_space {A} `{Ground A} : Space.ComplexityBound (@length A)
    (fun cl => (7 * length (val cl) + 4) ⋉ tt).
  Proof. cbound. Qed.

  (** [app l m] copies [l] and shares [m]. *)
  Global Instance app_space {A} `{Ground A} : Space.ComplexityBound (@app A)
    (fun cl => 3 ⋉ fun cm => (9 * length (val cl) + 3) ⋉ tt).
  Proof. cbound. Qed.

  Global Instance repeat_space {A} `{Ground A} : Space.ComplexityBound (@repeat A)
    (fun cx => 4 ⋉ fun cn => (9 * val cn + 3) ⋉ tt).
  Proof. cbound. Qed.

  (** Naive reversal: quadratic. *)
  Global Instance rev_space {A} `{Ground A} : Space.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (9 * length (val cl) + 9) + 3) ⋉ tt).
  Proof. cbound. all: rewrite ?length_rev; nia. Qed.

  (** Reversal with an accumulator: linear. *)
  Global Instance rev_append_space {A} `{Ground A} : Space.ComplexityBound (@rev_append A)
    (fun cl => 3 ⋉ fun cm => (9 * length (val cl) + 3) ⋉ tt).
  Proof. cbound. Qed.

  (** [map f l] allocates [|l|] cells, and [f] on each element. *)
  Lemma map_space {A B} `{Ground A} `{Ground B} (f : A -> B) (c : nat) :
    Space.ComplexityBound f (fun _ => c ⋉ tt) ->
    Space.ComplexityBound (map f) (fun cl => ((c + 9) * length (val cl) + 3) ⋉ tt).
  Proof. intros Hf. cbound. Qed.

  (** ** Bounds in the size of the arguments ([Bounds]) *)
  Lemma nat_lt_size (n : nat) : n < size n.
  Proof. induction n; [apply size_O | pose proof (size_S n); lia]. Qed.
  Global Instance nat_size_fact (n : nat) : SizeFact n (n < size n) := nat_lt_size n.

  Global Instance Nat_add_space_linear : Space.LinearBound Nat.add := _.
  Global Instance Nat_mul_space_polynomial : Space.PolynomialBound Nat.mul := _.
End SpaceExamples.
