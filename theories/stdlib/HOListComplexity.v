(** * Higher-order functions on lists and options of any data

    In the cost model with lists and options of any data ([HOTimeCostModel],
    [TimeLists], [TimeDatatypes]), the elements of a list or of an option
    may be functions, and the complexity of a list is the list of the
    complexities of its elements (of an option, the complexity of its
    element).
    The bounds of the higher-order functions of the standard library are
    then as general as their types: the function and the elements may be of
    any type, and their bounds are those of the function and of the
    elements, given as complexities. The costs are
    - the costs of the applications of the function to the elements
      ([hsum]), or to the accumulators ([fold_left_fcost],
      [fold_right_fcost]), as its complexity gives them;
    - a constant per element and a constant, those of the recursion;
    and the complexity of the result is that of the elements, or that given
    by the complexity of the function ([hmap], [hfilter], [fold_left_pot],
    [fold_right_pot], [flat_map_pot]).

    A list [l] with complexity [c] is read as the case analysis reads it
    ([list_case_complexity]): its elements paired with their complexities,
    up to the end of the shorter one (they have the same length in the
    instance, but the bounds do not need it). As in [ListComplexity],
    [cbound] proves the bounds, with the smallest constants.

    Not covered: [partition], whose result is a pair of lists (pairs are
    modelled for ground data only). *)

From Complexity Require Export TimeCostModel BoolComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** Functions of the elements, with their complexities *)
Section Elements.
  Context {A CA : Type}.

  (** The sum of [g] on the elements. *)
  Fixpoint hsum (g : ℂI A CA -> nat) (l : list A) (c : list CA) : nat :=
    match l, c with
    | x :: l, cx :: c => g (x ⋊ cx) + hsum g l c
    | _, _ => 0
    end.

  Context {D : Type}.

  (** [g] on each element. *)
  Fixpoint hmap (g : ℂI A CA -> D) (l : list A) (c : list CA) : list D :=
    match l, c with
    | x :: l, cx :: c => g (x ⋊ cx) :: hmap g l c
    | _, _ => []
    end.

  (** The complexities of the elements that satisfy [p]. *)
  Fixpoint hfilter (p : A -> bool) (l : list A) (c : list CA) : list CA :=
    match l, c with
    | x :: l, cx :: c => if p x then cx :: hfilter p l c else hfilter p l c
    | _, _ => []
    end.

  (** [find p]: the sum of [g] on the elements examined, up to the first one
      that satisfies [p]; their number; the complexity of this element. *)
  Fixpoint hfind_sum (p : A -> bool) (g : ℂI A CA -> nat) (l : list A) (c : list CA) : nat :=
    match l, c with
    | x :: l, cx :: c => g (x ⋊ cx) + (if p x then 0 else hfind_sum p g l c)
    | _, _ => 0
    end.

  Fixpoint hfind_len (p : A -> bool) (l : list A) (c : list CA) : nat :=
    match l, c with
    | x :: l, _ :: c => S (if p x then 0 else hfind_len p l c)
    | _, _ => 0
    end.

  Fixpoint hfind (p : A -> bool) (l : list A) (c : list CA) : option CA :=
    match l, c with
    | x :: l, cx :: c => if p x then Some cx else hfind p l c
    | _, _ => None
    end.

  (** On an option [o] with complexity [c]: [g] on its element, if any. *)
  Definition osum (g : ℂI A CA -> nat) (o : option A) (c : option CA) : nat :=
    match o, c with Some x, Some cx => g (x ⋊ cx) | _, _ => 0 end.

  Definition omap (g : ℂI A CA -> D) (o : option A) (c : option CA) : option D :=
    match o, c with Some x, Some cx => Some (g (x ⋊ cx)) | _, _ => None end.
End Elements.

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

  (** [flat_map f l]: the complexities of the elements of the lists that
      [f] gives. *)
  Fixpoint flat_map_pot (cf : ℂI (A -> list B) (ℂI A CA -> ℂO (list CB)))
    (l : list A) (c : list CA) : list CB :=
    match l, c with
    | x :: l, cx :: c => hmap pot (val cf x) (res (pot cf (x ⋊ cx))) ++ flat_map_pot cf l c
    | _, _ => []
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
    (fun cl => 1 +> fun cm => (21 * length (val cl) + 10) +> (hmap pot (val cl) (pot cl) ++ pot cm)).
  Proof. cbound. Qed.

  (** ** Higher-order functions *)

  Global Instance map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@map A B)
      (fun cf => 1 +> fun cl =>
         (hsum (fun x => cost (pot cf x)) (val cl) (pot cl) + 29 * length (val cl) + 6)
         +> hmap (fun x => res (pot cf x)) (val cl) (pot cl)).
  Proof. cbound. Qed.

  Global Instance filter_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@filter A)
      (fun cf => 1 +> fun cl =>
         (hsum (fun x => cost (pot cf x)) (val cl) (pot cl) + 33 * length (val cl) + 6)
         +> hfilter (val cf) (val cl) (pot cl)).
  Proof. cbound. Qed.

  (** [find f l] stops at the first element that satisfies [f]. *)
  Global Instance find_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@find A)
      (fun cf => 1 +> fun cl =>
         (hfind_sum (val cf) (fun x => cost (pot cf x)) (val cl) (pot cl)
          + 26 * hfind_len (val cf) (val cl) (pot cl) + 6)
         +> hfind (val cf) (val cl) (pot cl)).
  Proof. cbound. Qed.

  Global Instance existsb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@existsb A)
      (fun cf => 1 +> fun cl =>
         (hsum (fun x => cost (pot cf x)) (val cl) (pot cl) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance forallb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@forallb A)
      (fun cf => 1 +> fun cl =>
         (hsum (fun x => cost (pot cf x)) (val cl) (pot cl) + 32 * length (val cl) + 6) >|).
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
      (fun cf => 1 +> fun cl =>
         (hsum (fun x => cost (pot cf x)) (val cl) (pot cl)
          + 21 * hsum (fun x => length (val cf (val x))) (val cl) (pot cl)
          + 38 * length (val cl) + 6)
         +> flat_map_pot cf (val cl) (pot cl)).
  Proof. cbound. Qed.

  (** ** Options *)

  Global Instance option_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@option_map A B)
      (fun cf => 1 +> fun co =>
         (osum (fun x => cost (pot cf x)) (val co) (pot co) + 10)
         +> omap (fun x => res (pot cf x)) (val co) (pot co)).
  Proof. cbound. Qed.

End HOListComplexity.

(** The model with lists of any data, with these analyses. *)
Module Type HOTimeStdlib := HOTimeBool <+ HOListComplexity.
