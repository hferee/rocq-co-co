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
    [flat_map] on [czip cdefault cl]). [simpl_czip] reads the sums over
    [czip] as sums over the values, when the costs do not depend on the
    complexities (for lists of ground data, and functions on them). The folds thread an
    accumulator, whose value is the one that the function computes: their
    costs are given by [fold_left_fcost], [fold_right_fcost] and the
    complexities of their results by [fold_left_pot], [fold_right_pot]
    (below). As in [ListComplexity], [cbound] proves the bounds, with the
    smallest constants.

    Not covered yet: [partition], whose result is a pair of lists, of any
    data ([ProdTimeCostModel]). *)

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

(** The facts on the values of [filter] ([ValueFact]): the elements kept
    are at most those of the list, and their measures at most theirs. *)
#[global] Instance filter_value_fact {A} (p : A -> bool) (l : list A) :
  ValueFact (filter p l) (fun y => length y <= length l) := filter_length_le p l.
#[global] Instance map_filter_value_fact {A} (h : A -> nat) (p : A -> bool) (l : list A) :
  ValueFact (map h (filter p l)) (fun y => list_sum y <= list_sum (map h l)) :=
  list_sum_map_filter_le h p l.

(** The model, with the bounds of the boolean operations ([existsb] and
    [forallb] use [orb] and [andb]). *)
Module Type TimeBool := TimeCostModel.TimeCostModel <+ BoolComplexity.

Module HOListComplexity (Import Time : TimeBool).

  (** ** First-order functions, on lists of any data *)

  Global Instance length_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  (** The complexity of [l ++ m] is that of the elements of [l], then of [m]. *)
  Global Instance app_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@app A)
    (fun cl : ℂI (list A) (list CA) => 1 +> fun cm : ℂI (list A) (list CA) => (21 * length (val cl) + 10) +> (map pot (czip cdefault cl) ++ pot cm)).
  Proof. cbound. Qed.

  (** ** Higher-order functions *)

  Global Instance map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 29 * length (val cl) + 6)
         +> map (fun x => res (pot cf x)) (czip cdefault cl)).
  Proof. cbound. Qed.

  Global Instance filter_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@filter A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 33 * length (val cl) + 6)
         +> map pot (filter (fun x => val cf (val x)) (czip cdefault cl))).
  Proof. cbound. Qed.

  (** [find f l] stops at the first element that satisfies [f]: the costs
      of the elements examined, and their number. *)
  Global Instance find_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@find A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (fold_right (fun (x : ℂI A CA) (n : nat) => cost (pot cf x) + (if val cf (val x) then 0 else n))
            0 (czip cdefault cl)
          + 26 * fold_right (fun (x : ℂI A CA) (n : nat) => S (if val cf (val x) then 0 else n))
                   0 (czip cdefault cl) + 6)
         +> option_map pot (find (fun x : ℂI A CA => val cf (val x)) (czip cdefault cl))).
  Proof. cbound. Qed.

  Global Instance existsb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@existsb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance forallb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@forallb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance fold_left_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_left A B)
      (fun cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B CB -> ℂO CA)) => 1 +>
       fun cl : ℂI (list B) (list CB) => 4 +> fun cx : ℂI A CA =>
         (fold_left_fcost cdefault cf (val cl) (pot cl) cx + 40 * length (val cl) + 6)
         +> fold_left_pot cdefault cf (val cl) (pot cl) cx).
  Proof. cbound. Qed.

  Global Instance fold_right_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@fold_right A B)
      (fun cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA)) => 1 +>
       fun ca0 : ℂI A CA => 2 +> fun cl : ℂI (list B) (list CB) =>
         (fold_right_fcost cdefault cf ca0 (val cl) (pot cl) + 28 * length (val cl) + 10)
         +> fold_right_pot cdefault cf ca0 (val cl) (pot cl)).
  Proof. cbound. Qed.

  (** For a function of constant complexity, the costs of its applications
      in [fold_left] are linear in the length. *)
  Lemma fold_left_fcost_constant {A CA B CB} (dc : CB) (f : A -> B -> A) (c1 c2 : nat) (r : CA)
    (l : list B) (c : list CB) cx :
    fold_left_fcost dc (f ⋊ (fun _ : ℂI A CA => c1 +> fun _ : ℂI B CB => c2 +> r)) l c cx
    = (c1 + c2) * length l.
  Proof.
    revert c cx. induction l as [|b t IH]; intros c cx; cbn [fold_left_fcost length]; cbn; [lia|].
    rewrite IH. lia.
  Qed.

  (** A closed bound of [fold_right], in the sizes: when the applications
      of [f] cost at most [c1] and [g #|x| #|y|], for a monotone [g], and
      each one adds at most the size of the element and [d] to the
      accumulator, each costs at most [c1 + g #|l| (#|a0| + #|l| + d *
      length l)], whatever the complexities. *)
  Section ClosedBound.
    Context {A CA B CB : Type} `{Size A} `{Size B}.
    Context (dc : CB) (cf : ℂI (B -> A -> A) (ℂI B CB -> ℂO (ℂI A CA -> ℂO CA))) (ca0 : ℂI A CA).
    Context (c1 d : nat) (g : nat -> nat -> nat).
    Hypothesis g_mono : forall x y x' y', x <= x' -> y <= y' -> g x y <= g x' y'.
    Hypothesis cf_cost1 : forall x cx, cost (pot cf (x ⋊ cx)) <= c1.
    Hypothesis cf_cost2 : forall x cx y cy, cost (res (pot cf (x ⋊ cx)) (y ⋊ cy)) <= g #|x| #|y|.
    Hypothesis cf_size : forall x y, #|val cf x y| <= #|x| + #|y| + d.

    Lemma fold_right_size_le l : #|fold_right (val cf) (val ca0) l| <= #|val ca0| + #|l| + d * length l.
    Proof.
      induction l as [|x l IH]; cbn [fold_right length]; [lia|].
      rewrite size_cons. pose proof (cf_size x (fold_right (val cf) (val ca0) l)). lia.
    Qed.

    Lemma fold_right_fcost_le_gen S L l c :
      #|l| <= S -> length l <= L ->
      fold_right_fcost dc cf ca0 l c <= length l * (c1 + g S (#|val ca0| + S + d * L)).
    Proof.
      revert c. induction l as [|x l IH]; intros c HS HL; cbn [fold_right_fcost length]; [lia|].
      rewrite size_cons in HS. cbn [length] in HL.
      pose proof (cf_cost1 x (hd dc c)).
      pose proof (cf_cost2 x (hd dc c) (fold_right (val cf) (val ca0) l) (fold_right_pot dc cf ca0 l (tl c))).
      pose proof (fold_right_size_le l).
      assert (g #|x| #|fold_right (val cf) (val ca0) l| <= g S (#|val ca0| + S + d * L))
        by (apply g_mono; nia).
      specialize (IH (tl c) ltac:(lia) ltac:(lia)). nia.
    Qed.

    Lemma fold_right_fcost_le l c :
      fold_right_fcost dc cf ca0 l c <= length l * (c1 + g #|l| (#|val ca0| + #|l| + d * length l)).
    Proof. apply fold_right_fcost_le_gen; lia. Qed.
  End ClosedBound.

  (** The closed bound of [fold_right f], for a function [f] on ground data
      of such a complexity. *)
  Lemma fold_right_size_complexity {A CA} {RA : Repr A CA} {GA : IsGround RA} `{Size A}
      {B CB} {RB : Repr B CB} {GB : IsGround RB} `{Size B}
      (f : B -> A -> A) (c1 d : nat) (g : nat -> nat -> nat) :
    (forall x y x' y', x <= x' -> y <= y' -> g x y <= g x' y') ->
    Time.ComplexityBound f (fun cx : ℂI B CB => c1 +> fun cy : ℂI A CA => g #|val cx| #|val cy| >|) ->
    (forall x y, #|f x y| <= #|x| + #|y| + d) ->
    Time.ComplexityBound (fold_right f)
      (fun ca0 : ℂI A CA => 2 +> fun cl : ℂI (list B) (list CB) =>
         (length (val cl) * (c1 + g #|val cl| (#|val ca0| + #|val cl| + d * length (val cl)))
          + 28 * length (val cl) + 10) >|).
  Proof.
    intros Hg Hf Hd.
    eapply ComplexityBound_mono; [| exact (apply_complexity _ Hf fold_right_complexity)].
    cbv beta; cbn [res]; bo_split; cbn [cost val pot res]; [lia|].
    match goal with |- context [fold_right_fcost ?dc ?cf ?ca0 ?l ?c] =>
      pose proof (fold_right_fcost_le dc cf ca0 c1 d g Hg (fun _ _ => le_n _) (fun _ _ _ _ => le_n _) Hd l c) end.
    lia.
  Qed.

  (* TODO: a closed bound for fold_left, as fold_right_fcost_le, from the
    relation between complexity and size; then for other higher-order list
    functions, like iter. *)

  (** [flat_map f l] appends the lists that [f] gives: the cost of [app] is
      linear in the length of each of them. *)
  Global Instance flat_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@flat_map A B)
      (fun cf : ℂI (A -> list B) (ℂI A CA -> ℂO (list CB)) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (list_sum (map (fun x => cost (pot cf x)) (czip cdefault cl))
          + 21 * list_sum (map (fun x => length (val cf (val x))) (czip cdefault cl))
          + 38 * length (val cl) + 6)
         +> flat_map (fun x => map pot (czip cdefault (val cf (val x) ⋊ res (pot cf x)))) (czip cdefault cl)).
  Proof. cbound. Qed.

  (** ** Options *)

  Global Instance option_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@option_map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun co : ℂI (option A) (option CA) =>
         (match czip_option cdefault co with Some x => cost (pot cf x) | None => 0 end + 10)
         +> option_map (fun x => res (pot cf x)) (czip_option cdefault co)).
  Proof. cbound. Qed.


End HOListComplexity.

