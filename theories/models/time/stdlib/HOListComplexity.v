(** * Functions on lists of any data

    The elements, and the function of a higher-order function, are of any
    type: the bounds are in their complexities. [cbound] proves them, with
    the smallest constants. Not covered yet: [partition], whose result is a
    pair of lists. *)

From Complexity Require Export BoolComplexity SumComplexity ListFacts.
From Stdlib Require Import List.
Import ListNotations.
(** [filter_map] is that of [ListFacts], not the lemma of [List]. *)
Import ListFacts.

(** The elements of a list of sums (Haskell's [lefts] and [rights]). *)
Fixpoint lefts {A B} (l : list (A + B)) : list A :=
  match l with [] => [] | inl a :: l => a :: lefts l | inr _ :: l => lefts l end.
Fixpoint rights {A B} (l : list (A + B)) : list B :=
  match l with [] => [] | inl _ :: l => rights l | inr b :: l => b :: rights l end.

(** No timeout in the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** The elements of a list, with their complexities

    [ccombine cl]: the elements of [val cl] with their complexities in
    [pot cl], as many as both have; all of them at a well-formed input
    ([wf_list]). Not unfolded by the computation. *)
Definition ccombine {A CA} (cl : ℂI (list A) (list CA)) : list (ℂI A CA) :=
  map (fun xc => fst xc ⋊ snd xc) (combine (val cl) (pot cl)).
Arguments ccombine : simpl never.

Lemma ccombine_nil {A CA} (c : list CA) : ccombine ((@nil A) ⋊ c) = [].
Proof. reflexivity. Qed.

Lemma ccombine_cons {A CA} (x : A) l (h : CA) t :
  ccombine ((x :: l) ⋊ (h :: t)) = (x ⋊ h) :: ccombine (l ⋊ t).
Proof. reflexivity. Qed.

(** [sum_costs c xs]: the sum of the costs of [c] on the elements of [xs].
    Not unfolded by the computation. *)
Definition sum_costs {A CA CB} (c : ℂI A CA -> ℂO CB) (xs : list (ℂI A CA)) : nat :=
  list_sum (map (fun x => cost (c x)) xs).
Arguments sum_costs : simpl never.

Lemma sum_costs_nil {A CA CB} (c : ℂI A CA -> ℂO CB) : sum_costs c [] = 0.
Proof. reflexivity. Qed.

Lemma sum_costs_cons {A CA CB} (c : ℂI A CA -> ℂO CB) x xs :
  sum_costs c (x :: xs) = cost (c x) + sum_costs c xs.
Proof. reflexivity. Qed.

(** When [pot cl] has the length of [val cl], the maps over [ccombine cl]
    of functions that ignore the complexities are maps over [val cl]. *)
Lemma length_ccombine {A CA} (cl : ℂI (list A) (list CA)) :
  length (pot cl) = length (val cl) -> length (ccombine cl) = length (val cl).
Proof. intro H. unfold ccombine. rewrite length_map, length_combine, H. lia. Qed.

Lemma map_ccombine_val {A CA B} (F : ℂI A CA -> B) (cl : ℂI (list A) (list CA)) (d : CA) :
  length (pot cl) = length (val cl) -> (forall v c1 c2, F (v ⋊ c1) = F (v ⋊ c2)) ->
  map F (ccombine cl) = map (fun v => F (v ⋊ d)) (val cl).
Proof.
  destruct cl as [l c]. unfold ccombine. cbn [val pot]. intros Hlen HF. revert c Hlen.
  induction l as [|x l IH]; intros [|h c] Hlen; cbn in *; try discriminate; [reflexivity|].
  f_equal; [apply HF | apply IH; lia].
Qed.

(** ** Folds

    The costs and the complexity of the result of a fold, computed with
    the values of the accumulators ([val cf (val cx) b]), so that they
    follow the fold by computation. *)
Section Folds.
  Context {A CA B CB : Type}.

  (** [fold_left f l x]: the costs of the applications of [f], and the
      complexity of the last accumulator. *)
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

(** The values of [filter] ([ValueFact]): at most the elements of the
    list. *)
#[global] Instance filter_value_fact {A} (p : A -> bool) (l : list A) :
  ValueFact (filter p l) (fun y => length y <= length l) := filter_length_le p l.
#[global] Instance map_filter_value_fact {A} (h : A -> nat) (p : A -> bool) (l : list A) :
  ValueFact (map h (filter p l)) (fun y => list_sum y <= list_sum (map h l)) :=
  list_sum_map_filter_le h p l.

(** The model with the bounds of [orb] and [andb], for [existsb] and
    [forallb]. *)
Module Type TimeBool := TimeCostModel.TimeCostModel <+ BoolComplexity.

Module HOListComplexity (Import Time : TimeBool).

  (** ** Tactics

      [simpl_ccombine] rewrites the maps over [ccombine cl] of functions
      that ignore the complexities as maps over [val cl], at a well-formed
      input ([Hwf]), and distributes the sums ([simpl_list_sum]). *)
  Ltac simpl_ccombine :=
    unfold sum_costs in *; cbn [cost res val pot] in *; cnorm_types;
    repeat match goal with
    | Hw : wf (val ?cl) (pot ?cl) |- context [ccombine ?cl] =>
        lazymatch goal with
        | _ : length (pot cl) = length (val cl) |- _ => fail
        | _ => pose proof (wf_length _ _ Hw)
        end
    end;
    repeat match goal with
    | Hl : length (pot ?cl) = length (val ?cl) |- context [map ?F (ccombine ?cl)] =>
        rewrite (map_ccombine_val F cl cdefault Hl (fun _ _ _ => eq_refl))
    | Hl : length (pot ?cl) = length (val ?cl) |- context [length (ccombine ?cl)] =>
        rewrite (length_ccombine cl Hl)
    | Hl : length (pot ?cl) = length (val ?cl), H : context [map ?F (ccombine ?cl)] |- _ =>
        rewrite (map_ccombine_val F cl cdefault Hl (fun _ _ _ => eq_refl)) in H
    | Hl : length (pot ?cl) = length (val ?cl), H : context [length (ccombine ?cl)] |- _ =>
        rewrite (length_ccombine cl Hl) in H
    end;
    simpl_list_sum; cbn [val pot] in *;
    repeat match goal with
    | |- context [map (fun x => ?f x) ?l] => change (map (fun x => f x) l) with (map f l)
    | H : context [map (fun x => ?f x) ?l] |- _ => change (map (fun x => f x) l) with (map f l) in H
    end;
    simpl_list_sum; cnorm_types.

  (** [ccombine_case] closes the goals that [cbound] leaves for a bound
      over [ccombine cl]: it splits the well-formed complexity of the list
      as its case analysis does ([wf_cons]), and computes. *)
  Ltac ccombine_case :=
    match goal with
    | E : val ?cl = _ |- context [ccombine ?cl] =>
        let lv := fresh "lv" in let lc := fresh "lc" in
        destruct cl as [lv lc]; cbn [val pot] in *; subst lv;
        try match goal with
        | W : wf (_ :: _) lc |- _ =>
            let h := fresh "h" in let t := fresh "t" in let Hl := fresh "Hl" in
            destruct (wf_cons _ _ _ W) as (h & t & Hl & _); subst lc
        end
    end;
    cbn [hd tl] in *;
    repeat match goal with H : ?v = _ |- _ => is_var v; subst v end;
    rewrite ?ccombine_nil, ?ccombine_cons; unfold list_sum;
    cbn [hd tl map filter filter_map find fold_right flat_map option_map val pot];
    rewrite ?sum_costs_cons, ?sum_costs_nil;
    repeat match goal with E0 : val ?f ?x = _ |- context [val ?f ?x] => rewrite E0 end;
    cbn [hd tl map filter filter_map find fold_right flat_map option_map val pot];
    try unfold cost, res in *; cnorm_types.

  (** ** First-order functions, on lists of any data *)

  Global Instance length_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  (** The complexities of the results below are those of the inputs
      ([pot cl]); [cbound] computes them from the case analyses, which
      agree at a well-formed input: [wf_case] splits it as they do. *)
  Local Ltac wf_case :=
    match goal with
    | E : val ?cl = _, W : wf (val ?cl) (pot ?cl) |- _ =>
        rewrite E in W;
        first [apply wf_nil in W; rewrite W | destruct (wf_cons _ _ _ W) as (? & ? & -> & _)]
    end.

  (** The complexity of [l ++ m] is that of the elements of [l], then of [m]. *)
  Global Instance app_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@app A)
    (fun cl : ℂI (list A) (list CA) => 1 +> fun cm : ℂI (list A) (list CA) =>
       (21 * length (val cl) + 10) +> (pot cl ++ pot cm)).
  Proof. cbound; wf_case; reflexivity. Qed.

  (** The tail of the empty list is built, with the complexity [[]]. *)
  Global Instance tl_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@tl A) (fun cl : ℂI (list A) (list CA) => 3 +> tl (pot cl)).
  Proof. cbound. wf_case. reflexivity. Qed.

  (** [hd d l] at [[]] is [d], with its complexity. *)
  Global Instance hd_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@hd A) (fun cd => 1 +> fun cl => 6 +> hd (pot cd) (pot cl)).
  Proof. cbound; wf_case; reflexivity. Qed.

  (** [rev] appends each element to the reversed tail: quadratic. *)
  Global Instance rev_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (11 * length (val cl) + 23) + 6) +> rev (pot cl)).
  Proof. cbound; [rewrite length_rev; lia | wf_case; reflexivity ..]. Qed.

  (** [firstn], [skipn] and [nth] recurse on the index. *)
  Global Instance firstn_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@firstn A)
    (fun cn => 4 +> fun cl => (39 * val cn + 6) +> firstn (val cn) (pot cl)).
  Proof. cbound; wf_case; reflexivity. Qed.

  Global Instance skipn_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@skipn A)
    (fun cn => 4 +> fun cl => (32 * val cn + 6) +> skipn (val cn) (pot cl)).
  Proof. cbound; wf_case; reflexivity. Qed.

  Global Instance nth_complexity {A CA} `{Repr A CA} : Time.ComplexityBound (@nth A)
    (fun cn => 4 +> fun cl => 2 +> fun cd => (48 * val cn + 14) +> nth (val cn) (pot cl) (pot cd)).
  Proof. cbound; wf_case; reflexivity. Qed.

  (** ** Higher-order functions *)

  Global Instance map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 29 * length (val cl) + 6)
         +> map (fun x => res (pot cf x)) (ccombine cl)).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

  Global Instance filter_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@filter A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 33 * length (val cl) + 6)
         +> filter_map (fun x => if val cf (val x) then Some (pot x) else None) (ccombine cl)).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

  (** [find f l] stops at the first element that satisfies [f]. *)
  Global Instance find_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@find A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (fold_right
            (fun (x : ℂI A CA) (n : nat) => cost (pot cf x) + (if val cf (val x) then 0 else n))
            0 (ccombine cl)
          + 26 * fold_right (fun (x : ℂI A CA) (n : nat) => S (if val cf (val x) then 0 else n))
                   0 (ccombine cl) + 6)
         +> option_map pot (find (fun x : ℂI A CA => val cf (val x)) (ccombine cl))).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

  Global Instance existsb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@existsb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 32 * length (val cl) + 6) >|).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

  Global Instance forallb_complexity {A CA} `{Repr A CA} :
    Time.ComplexityBound (@forallb A)
      (fun cf : ℂI (A -> bool) (ℂI A CA -> ℂO unit) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl) + 32 * length (val cl) + 6) >|).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

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

  (** [flat_map f l] appends the lists that [f] gives: in their
      lengths. *)
  Global Instance flat_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@flat_map A B)
      (fun cf : ℂI (A -> list B) (ℂI A CA -> ℂO (list CB)) => 1 +> fun cl : ℂI (list A) (list CA) =>
         (sum_costs (pot cf) (ccombine cl)
          + 21 * list_sum (map (fun x => length (val cf (val x))) (ccombine cl))
          + 38 * length (val cl) + 6)
         +> flat_map (fun x => res (pot cf x)) (ccombine cl)).
  Proof. cbound; ccombine_case; first [reflexivity | lia]. Qed.

  (** ** Lists of sums

      The elements with their complexities ([czip_sum], [SumComplexity]).
      An element [inl] costs [27], an element [inr] [22]. *)
  Global Instance lefts_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@lefts A B)
      (fun cl : ℂI (list (A + B)) (list (CA + CB)) => (27 * length (val cl) + 6)
                 +> map (@pot A CA) (lefts (map (czip_sum cdefault cdefault) (ccombine cl)))).
  Proof. cbound; ccombine_case; cbn [lefts rights map]; first [reflexivity | lia]. Qed.
  Global Instance rights_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@rights A B)
      (fun cl : ℂI (list (A + B)) (list (CA + CB)) => (27 * length (val cl) + 6)
                 +> map (@pot B CB) (rights (map (czip_sum cdefault cdefault) (ccombine cl)))).
  Proof. cbound; ccombine_case; cbn [lefts rights map]; first [reflexivity | lia]. Qed.
End HOListComplexity.

(** The model with the bounds of the functions on lists of any data. *)
Module Type TimeHOLists := TimeBool <+ HOListComplexity.
