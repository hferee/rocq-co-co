(** * Higher-order functions on lists and options of any data

    The elements of a list or of an option may be functions ([TimeLists],
    [TimeDatatypes]), and the complexity of a list is the list of the
    complexities of its elements (of an option, the complexity of its
    element).
    The bounds of the higher-order functions of the standard library are
    then as general as their types: the function and the elements may be of
    any type, and their bounds are those of the function and of the
    elements, given as complexities.

    A list with complexity [cl] is read as the case analysis reads it
    ([list_case_complexity]): its elements [val cl] paired with their
    complexities [pot cl], the default one for the elements beyond them
    ([czip cdefault cl]). The bounds are stated with the functions of the
    standard library on [czip cdefault cl]: the costs are the costs of the
    applications of the function to the elements
    ([list_sum (map _ (czip cdefault cl))]), a constant per element and a
    constant; the complexity of the result is that of the elements, or that
    given by the complexity of the function ([map], [filter], [find],
    [flat_map] on [czip cdefault cl]). For lists of data of complexity
    [unit], the bounds of [ListComplexity] come first (these have a lower
    priority); [simpl_czip] reads the sums over [czip] as sums over the
    values, when the costs do not depend on the complexities. The folds thread an
    accumulator, whose value is the one that the function computes: their
    costs are given by [fold_left_fcost], [fold_right_fcost] and the
    complexities of their results by [fold_left_pot], [fold_right_pot]
    (below). As in [ListComplexity], [cbound] proves the bounds, with the
    smallest constants.

    Not covered yet: [partition], whose result is a pair of lists, of any
    data ([HProdTimeCostModel]). *)

From Complexity Require Export TimeCostModel BoolComplexity ListFacts.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** The elements of a list, with their complexities *)

(** The value gives the shape: the elements beyond the complexities have
    the default one [d] ([cdefault], as the case analyses give it). *)
Fixpoint dzip {A CA} (d : CA) (l : list A) (c : list CA) : list (ℂI A CA) :=
  match l with
  | [] => []
  | x :: l => (x ⋊ hd d c) :: dzip d l (tl c)
  end.

Definition czip {A CA} (d : CA) (cl : ℂI (list A) (list CA)) : list (ℂI A CA) :=
  dzip d (val cl) (pot cl).

(** The element of an option, with its complexity. *)
Definition czip_option {A CA} (d : CA) (co : ℂI (option A) (option CA)) : option (ℂI A CA) :=
  match val co with Some x => Some (x ⋊ option_dflt d (pot co)) | None => None end.

#[global] Hint Unfold czip czip_option : costs.
#[local] Hint Unfold list_sum : costs.

(** The elements of [czip d cl] are those of [val cl]: the sums of
    functions of the elements that do not depend on their complexities are
    sums over [val cl] ([simpl_czip]). *)
Lemma length_dzip {A CA} (d : CA) (l : list A) (c : list CA) : length (dzip d l c) = length l.
Proof. revert c; induction l as [|x l IH]; intro c; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma map_dzip_val {A CA B} (F : ℂI A CA -> B) (d : CA) (l : list A) (c : list CA) :
  (forall v c1 c2, F (v ⋊ c1) = F (v ⋊ c2)) -> map F (dzip d l c) = map (fun v => F (v ⋊ d)) l.
Proof.
  intro HF. revert c. induction l as [|x l IH]; intro c; cbn; [reflexivity|].
  rewrite IH, (HF x (hd d c) d). reflexivity.
Qed.

(** [simpl_czip]: [simpl_list_sum], then the maps over [czip] of functions
    that do not depend on the complexities of the elements (the condition
    holds by computation) as maps over the values, again distributed. *)
Ltac simpl_czip :=
  simpl_list_sum; unfold czip in *;
  repeat match goal with
  | |- context [map ?F (dzip ?d ?l ?c)] => rewrite (map_dzip_val F d l c (fun _ _ _ => eq_refl))
  | H : context [map ?F (dzip ?d ?l ?c)] |- _ =>
      rewrite (map_dzip_val F d l c (fun _ _ _ => eq_refl)) in H
  end;
  repeat rewrite length_dzip in *;
  cbn [val pot] in *;
  repeat match goal with
  | |- context [map (fun x => ?f x) ?l] => change (map (fun x => f x) l) with (map f l)
  | H : context [map (fun x => ?f x) ?l] |- _ => change (map (fun x => f x) l) with (map f l) in H
  end;
  simpl_list_sum.

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
  Fixpoint fold_left_fcost (d : CB) (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)))
    (l : list B) (c : list CB) (cx : ℂI A CA) : nat :=
    match l with
    | b :: l =>
        let r1 := pot cf cx in
        let r2 := res r1 (b ⋊ hd d c) in
        cost r1 + cost r2 + fold_left_fcost d cf l (tl c) (val cf (val cx) b ⋊ res r2)
    | [] => 0
    end.

  Fixpoint fold_left_pot (d : CB) (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)))
    (l : list B) (c : list CB) (cx : ℂI A CA) : CA :=
    match l with
    | b :: l => fold_left_pot d cf l (tl c) (val cf (val cx) b ⋊ res (res (pot cf cx) (b ⋊ hd d c)))
    | [] => pot cx
    end.

  (** [fold_right f a0 l]: the same, from the end of the list. *)
  Fixpoint fold_right_pot (d : CB) (cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)))
    (ca0 : ℂI A CA) (l : list B) (c : list CB) : CA :=
    match l with
    | b :: l =>
        res (res (pot cf (b ⋊ hd d c))
               (fold_right (val cf) (val ca0) l ⋊ fold_right_pot d cf ca0 l (tl c)))
    | [] => pot ca0
    end.

  Fixpoint fold_right_fcost (d : CB) (cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)))
    (ca0 : ℂI A CA) (l : list B) (c : list CB) : nat :=
    match l with
    | b :: l =>
        let r1 := pot cf (b ⋊ hd d c) in
        cost r1 + cost (res r1 (fold_right (val cf) (val ca0) l ⋊ fold_right_pot d cf ca0 l (tl c)))
        + fold_right_fcost d cf ca0 l (tl c)
    | [] => 0
    end.

End Folds.

(** The model, with the bounds of the boolean
    operations ([existsb] and [forallb] use [orb] and [andb]). *)
Module Type HOTimeBool := HOTimeCostModel <+ BoolComplexity.

Module HOListComplexity (Import Time : HOTimeBool).

  (** ** First-order functions, on lists of any data *)

  Global Instance length_hcomplexity {A CA} `{Repr A CA} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 6) >|) | 10.
  Proof. cbound. Qed.

  (** The complexity of [l ++ m] is that of the elements of [l], then of [m]. *)
  Global Instance app_hcomplexity {A CA} `{Repr A CA} : Time.ComplexityBound (@app A)
    (fun cl : ℂI (list A) (list CA) => 1 +> fun cm : ℂI (list A) (list CA) => (21 * length (val cl) + 10) +> (map pot (czip cdefault cl) ++ pot cm)) | 10.
  Proof. cbound. Qed.

  (** ** Higher-order functions

      Their bounds have a lower priority than those of [ListComplexity],
      which come first for the lists of data of complexity [unit]. *)

  Global Instance map_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 29 * length (val cl) + 6)
         +> map (fun x => res (pot cf x)) (czip cdefault cl)) | 10.
  Proof. cbound. Qed.

  Global Instance filter_hcomplexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@filter A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 33 * length (val cl) + 6)
         +> map pot (filter (fun x => val cf (val x)) (czip cdefault cl))) | 10.
  Proof. cbound. Qed.

  (** [find f l] stops at the first element that satisfies [f]: the costs
      of the elements examined, and their number. *)
  Global Instance find_hcomplexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@find A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (fold_right (fun (x : ℂI A CA) (n : nat) => cost (pot cf x) + (if val cf (val x) then 0 else n))
            0 (czip cdefault cl)
          + 26 * fold_right (fun (x : ℂI A CA) (n : nat) => S (if val cf (val x) then 0 else n))
                   0 (czip cdefault cl) + 6)
         +> option_map pot (find (fun x : ℂI A CA => val cf (val x)) (czip cdefault cl))) | 10.
  Proof. cbound. Qed.

  Global Instance existsb_hcomplexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@existsb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 32 * length (val cl) + 6) >|) | 10.
  Proof. cbound. Qed.

  Global Instance forallb_hcomplexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@forallb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 32 * length (val cl) + 6) >|) | 10.
  Proof. cbound. Qed.

  Global Instance fold_left_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_left A B)
      (fun cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)) => 1 +>
       fun cl : ℂI (list B) (list CB) => 4 +> fun cx : ℂI A CA =>
         (fold_left_fcost cdefault cf (val cl) (pot cl) cx + 40 * length (val cl) + 6)
         +> fold_left_pot cdefault cf (val cl) (pot cl) cx) | 10.
  Proof. cbound. Qed.

  Global Instance fold_right_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_right A B)
      (fun cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)) => 1 +>
       fun ca0 : ℂI A CA => 2 +> fun cl : ℂI (list B) (list CB) =>
         (fold_right_fcost cdefault cf ca0 (val cl) (pot cl) + 28 * length (val cl) + 10)
         +> fold_right_pot cdefault cf ca0 (val cl) (pot cl)) | 10.
  Proof. cbound. Qed.

  (** [flat_map f l] appends the lists that [f] gives: the cost of [app] is
      linear in the length of each of them. *)
  Global Instance flat_map_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@flat_map A B)
      (fun cf : ℂI (A -> list B) (ℂI A CA -> ℂO (list CB)) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl))
          + 21 * list_sum (map (fun x => length (val cf (val x))) (czip cdefault cl))
          + 38 * length (val cl) + 6)
         +> flat_map (fun x => map pot (czip cdefault (val cf (val x) ⋊ res (pot cf x)))) (czip cdefault cl)) | 10.
  Proof. cbound. Qed.

  (** ** Options *)

  Global Instance option_map_hcomplexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@option_map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun co : ℂI (option A) (option CA) =>
         (match czip_option cdefault co with Some x => cost (pot cf x) | None => 0 end + 10)
         +> option_map (fun x => res (pot cf x)) (czip_option cdefault co)) | 10.
  Proof. cbound. Qed.

End HOListComplexity.

(** The model with these analyses (they are also in [TimeStdlib]). *)
Module Type HOTimeStdlib := HOTimeBool <+ HOListComplexity.
