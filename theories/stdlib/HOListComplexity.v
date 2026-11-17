(** * Higher-order functions on lists and options of any data

    In the cost model with lists and options of any data ([HOTimeCostModel],
    [TimeLists], [TimeDatatypes]), the elements of a list or of an option
    may be functions, and the complexity of a list is the list of the
    complexities of its elements (of an option, the complexity of its
    element).
    The bounds of the higher-order functions of the standard library are
    then as general as their types: the function and the elements may be of
    any type, and their bounds are those of the function and of the
    elements, given as complexities.

    A list with complexity [cl] is read as the case analysis reads it
    ([list_case_complexity]): its elements [val cl] paired with their
    complexities [pot cl] ([czip cl]), up to the end of the shorter one
    (they have the same length in the instance, but the bounds do not need
    it). The bounds are stated with the functions of the standard library
    on [czip cl]: the costs are the costs of the applications of the
    function to the elements ([list_sum (map _ (czip cl))]), a constant per
    element and a constant; the complexity of the result is that of the
    elements, or that given by the complexity of the function ([map],
    [filter], [find], [flat_map] on [czip cl]). The folds thread an
    accumulator, whose value is the one that the function computes: their
    costs are given by [fold_left_fcost], [fold_right_fcost] and the
    complexities of their results by [fold_left_pot], [fold_right_pot]
    (below). As in [ListComplexity], [cbound] proves the bounds, with the
    smallest constants.

    Not covered yet: [partition], whose result is a pair of lists, of any
    data ([HProdTimeCostModel]). *)

From Complexity Require Export TimeCostModel BoolComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** The elements of a list, with their complexities *)

Definition czip {A CA} (cl : ℂI (list A) (list CA)) : list (ℂI A CA) :=
  map (fun p => fst p ⋊ snd p) (combine (val cl) (pot cl)).

(** The element of an option, with its complexity. *)
Definition czip_option {A CA} (co : ℂI (option A) (option CA)) : option (ℂI A CA) :=
  match val co, pot co with Some x, Some c => Some (x ⋊ c) | _, _ => None end.

(** [cbound] reads them as the case analyses do. *)
#[global] Hint Unfold czip czip_option : costs.
#[local] Hint Unfold list_sum : costs.

(** ** Folds

    The value of an accumulator is the one that the function computes
    ([val cf (val cx) b], [fold_right (val cf) (val ca0) l]), so that the
    recurrences of the bounds hold by computation; a fold of the standard
    library on [czip cl] would compute them from the values of [czip cl],
    equal only after an induction. *)
Section Folds.
  Context {A CA B CB : Type}.

  (** [fold_left f l x]: the costs of the applications of [f] to the
      accumulators and to the elements, and the complexity of the last
      accumulator. The complexity of an accumulator is the one that [f]
      gives, from that of the previous one. *)
  Fixpoint fold_left_fcost (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)))
    (l : list B) (c : list CB) (cx : ℂI A CA) : nat :=
    match l, c with
    | b :: l, cb :: c =>
        let r1 := pot cf cx in
        let r2 := res r1 (b ⋊ cb) in
        cost r1 + cost r2 + fold_left_fcost cf l c (val cf (val cx) b ⋊ res r2)
    | _, _ => 0
    end.

  Fixpoint fold_left_pot (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)))
    (l : list B) (c : list CB) (cx : ℂI A CA) : CA :=
    match l, c with
    | b :: l, cb :: c => fold_left_pot cf l c (val cf (val cx) b ⋊ res (res (pot cf cx) (b ⋊ cb)))
    | _, _ => pot cx
    end.

  (** [fold_right f a0 l]: the same, from the end of the list. *)
  Fixpoint fold_right_pot (cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)))
    (ca0 : ℂI A CA) (l : list B) (c : list CB) : CA :=
    match l, c with
    | b :: l, cb :: c =>
        res (res (pot cf (b ⋊ cb)) (fold_right (val cf) (val ca0) l ⋊ fold_right_pot cf ca0 l c))
    | _, _ => pot ca0
    end.

  Fixpoint fold_right_fcost (cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)))
    (ca0 : ℂI A CA) (l : list B) (c : list CB) : nat :=
    match l, c with
    | b :: l, cb :: c =>
        let r1 := pot cf (b ⋊ cb) in
        cost r1 + cost (res r1 (fold_right (val cf) (val ca0) l ⋊ fold_right_pot cf ca0 l c))
        + fold_right_fcost cf ca0 l c
    | _, _ => 0
    end.

End Folds.

(** The model with lists of any data, with the bounds of the boolean
    operations ([existsb] and [forallb] use [orb] and [andb]). *)
Module Type HOTimeBool := HOTimeCostModel <+ BoolComplexity.

Module HOListComplexity (Import Time : HOTimeBool).

  (** ** First-order functions, on lists of any data *)

  Global Instance length_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  (** The complexity of [l ++ m] is that of the elements of [l], then of [m]. *)
  Global Instance app_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm => (21 * length (val cl) + 10) +> (map pot (czip cl) ++ pot cm)).
  Proof. cbound. Qed.

  (** ** Higher-order functions *)

  Global Instance map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@map A B)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cl)) + 29 * length (val cl) + 6)
         +> map (fun x => res (pot cf x)) (czip cl)).
  Proof. cbound. Qed.

  Global Instance filter_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@filter A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cl)) + 33 * length (val cl) + 6)
         +> map pot (filter (fun x => val cf (val x)) (czip cl))).
  Proof. cbound. Qed.

  (** [find f l] stops at the first element that satisfies [f]: the costs
      of the elements examined, and their number. *)
  Global Instance find_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@find A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (fold_right (fun (x : ℂI A CA) (n : nat) => cost (pot cf x) + (if val cf (val x) then 0 else n))
            0 (czip cl)
          + 26 * fold_right (fun (x : ℂI A CA) (n : nat) => S (if val cf (val x) then 0 else n))
                   0 (czip cl) + 6)
         +> option_map pot (find (fun x : ℂI A CA => val cf (val x)) (czip cl))).
  Proof. cbound. Qed.

  Global Instance existsb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@existsb A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance forallb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@forallb A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance fold_left_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_left A B)
      (fun cf => 1 +> fun cl => 4 +> fun cx =>
         (fold_left_fcost cf (val cl) (pot cl) cx + 40 * length (val cl) + 6)
         +> fold_left_pot cf (val cl) (pot cl) cx).
  Proof. cbound. Qed.

  Global Instance fold_right_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_right A B)
      (fun cf => 1 +> fun ca0 => 2 +> fun cl =>
         (fold_right_fcost cf ca0 (val cl) (pot cl) + 28 * length (val cl) + 10)
         +> fold_right_pot cf ca0 (val cl) (pot cl)).
  Proof. cbound. Qed.

  (** [flat_map f l] appends the lists that [f] gives: the cost of [app] is
      linear in the length of each of them. *)
  Global Instance flat_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@flat_map A B)
      (fun cf : ℂI (A -> list B) (ℂI A CA -> ℂO (list CB)) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cl))
          + 21 * list_sum (map (fun x => length (val cf (val x))) (czip cl))
          + 38 * length (val cl) + 6)
         +> flat_map (fun x => map pot (czip (val cf (val x) ⋊ res (pot cf x)))) (czip cl)).
  Proof. cbound. Qed.

  (** ** Options *)

  Global Instance option_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@option_map A B)
      (fun cf => 1 +> fun co =>
         (match czip_option co with Some x => cost (pot cf x) | None => 0 end + 10)
         +> option_map (fun x => res (pot cf x)) (czip_option co)).
  Proof. cbound. Qed.

End HOListComplexity.

(** The model with lists of any data, with these analyses. *)
Module Type HOTimeStdlib := HOTimeBool <+ HOListComplexity.
