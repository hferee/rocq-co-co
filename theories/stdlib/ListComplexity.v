(** * Complexity of list functions from the standard library

    As in [NatComplexity]: [cbound] proves the bounds, with the smallest
    constants. These functions are
    defined in sections: their type and function parameters are fixed
    arguments of the fixpoint. A functional parameter comes with a
    hypothesis on its complexity ([fold_left_complexity]), or is an
    argument of the function, in the environment of its fixpoint
    ([fold_left_ground_hcomplexity], [fold_right_ground_hcomplexity], [map_complexity],
    ...); [fold_right_fcost_le] closes the costs of [fold_right] in the
    sizes, from the growth of the accumulator.

    The bounds of [map], [filter], [existsb], [forallb] and [flat_map] are
    those of [HOListComplexity], for lists of ground data: the costs of the
    applications of the function to the elements ([list_sum (map _ l)]), a
    constant per element and a constant. When the function is known (a
    closure of the function analysed), [cbound] leaves these sums in the
    inequalities: [simpl_list_sum] ([ListFacts]) distributes them over the
    sums and the products by factors that do not depend on the element,
    and the lemmas [list_sum_map_le], [list_sum_map_le_const] and
    [list_sum_map_le_affine] bound the terms that remain. *)

From Complexity Require Export NatComplexity ListFacts.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module ListComplexity (Import Time : TimeNat).


  (** ** Sizes *)
  Lemma length_lt_size {A} `{Size A} (l : list A) : length l < size l.
  Proof. induction l as [|a l]; cbn [length]; [rewrite size_nil | rewrite size_cons]; lia. Qed.

  Lemma list_sum_lt_size (l : list nat) : list_sum l + length l < size l.
  Proof.
    induction l as [|a l]; [rewrite size_nil; cbn; lia |].
    change (list_sum (a :: l)) with (a + list_sum l). cbn [length].
    pose proof (nat_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  (** Lists of lists: the total length of the elements (and their sums for
      lists of numbers). *)
  Lemma list_lengths_lt_size {A} `{Size A} (l : list (list A)) :
    list_sum (map (@length A) l) + length l < size l.
  Proof.
    induction l as [|a l IH]; [rewrite size_nil; cbn; lia|].
    cbn [map length]. change (list_sum (?x :: ?m)) with (x + list_sum m).
    pose proof (length_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Lemma list_sums_lt_size (l : list (list nat)) :
    list_sum (map list_sum l) + list_sum (map (@length nat) l) + length l < size l.
  Proof.
    induction l as [|a l IH]; [rewrite size_nil; cbn; lia|].
    cbn [map length]. change (list_sum (?x :: ?m)) with (x + list_sum m).
    pose proof (list_sum_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Global Instance length_size_fact {A} `{Size A} (l : list A) :
    SizeFact l (length l < size l) | 10 := length_lt_size l.
  Global Instance list_sum_size_fact (l : list nat) :
    SizeFact l (list_sum l + length l < size l) | 1 := list_sum_lt_size l.
  Global Instance list_lengths_size_fact {A} `{Size A} (l : list (list A)) :
    SizeFact l (list_sum (map (@length A) l) + length l < size l) | 2 := list_lengths_lt_size l.
  Global Instance list_sums_size_fact (l : list (list nat)) :
    SizeFact l (list_sum (map list_sum l) + list_sum (map (@length nat) l) + length l < size l) | 0 :=
    list_sums_lt_size l.

  (** ** List tail *)
  Instance complexity_tl {A} `{Ground A} :
    Time.ComplexityBound (@tl A) (fun lc => 3 >|) := _.

  Global Instance length_complexity {A} `{Ground A} : Time.ComplexityBound (@length A)
    (fun cl => (16 * length (val cl) + 6) >|) := _.

  Global Instance app_complexity {A} `{Ground A} : Time.ComplexityBound (@app A)
    (fun cl => 1 +> fun cm =>
       (21 * length (val cl) + 10) >|) := _.

  (** [seq] is recursive on its second argument; the first one changes. *)
  Global Instance seq_complexity : Time.ComplexityBound seq
    (fun cs => 4 +> fun cn => (33 * val cn + 4) >|) := _.

  (** [firstn], [skipn] and [nth] recurse on the index, [repeat] on the
      number of copies. *)
  Global Instance firstn_complexity {A} `{Ground A} : Time.ComplexityBound (@firstn A)
    (fun cn => 4 +> fun cl => (39 * val cn + 6) >|) := _.
  Global Instance skipn_complexity {A} `{Ground A} : Time.ComplexityBound (@skipn A)
    (fun cn => 4 +> fun cl => (32 * val cn + 6) >|) := _.
  Global Instance nth_complexity {A} `{Ground A} : Time.ComplexityBound (@nth A)
    (fun cn => 4 +> fun cl => 2 +> fun cd => (48 * val cn + 14) >|) := _.
  Global Instance repeat_complexity {A} `{Ground A} : Time.ComplexityBound (@repeat A)
    (fun cx => 1 +> fun cn => (21 * val cn + 6) >|) := _.
  Global Instance hd_complexity {A} `{Ground A} : Time.ComplexityBound (@hd A)
    (fun cd => 1 +> fun cl => 6 >|) := _.

  (** [rev] appends each element at the end of the reversed tail:
      quadratic. *)
  Global Instance rev_complexity {A} `{Ground A} : Time.ComplexityBound (@rev A)
    (fun cl => (length (val cl) * (11 * length (val cl) + 23) + 6) >|).
  Proof. cbound. rewrite length_rev. nia. Qed.

  (** [concat] appends each list: linear in the length of the result. *)
  Global Instance concat_complexity {A} `{Ground A} : Time.ComplexityBound (@concat A)
    (fun cl => (21 * length (concat (val cl)) + 30 * length (val cl) + 6) >|).
  Proof. cbound. rewrite length_app. lia. Qed.

  Global Instance combine_complexity {A B} `{Ground A} `{Ground B} : Time.ComplexityBound (@combine A B)
    (fun cl => 4 +> fun cm => (54 * length (val cl) + 6) >|) := _.

  (** [fold_left f], for a function [f] on ground data whose partial and
      full applications cost at most [c1] and [c2]. [f] is fixed: it is a
      parameter of the fixpoint, kept in the environment of its closure. *)
  Lemma fold_left_complexity {A B} `{Ground A} `{Ground B} (f : A -> B -> A) (c1 c2 : nat) :
    Time.ComplexityBound f (fun _ => c1 +> fun _ => c2 >|) ->
    Time.ComplexityBound (fold_left f)
      (fun cl => 4 +> fun cx =>
         ((c1 + c2 + 31) * length (val cl) + 6) >|).
  Proof. intro Hf. cbound. Qed.

  (** `fold_left f l x`, from the complexity [cf] of `f` and [cx] of `x`:
      the costs of the applications of `f` to the accumulators and to the
      elements, as [cf] gives them ([fold_left_fcost]), and the complexity
      of the last accumulator ([fold_left_pot]). The complexity of an
      accumulator is the one that [cf] gives at the previous step, so that
      the accumulator may be of any type, a function for instance. *)
  Fixpoint fold_left_fcost {A CA B : Type}
    (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B unit -> ℂO CA)))
    (l : list B) (cx : ℂI A CA) : nat :=
    match l with
    | [] => 0
    | b :: t =>
        let r1 := pot cf cx in          (* f x *)
        let r2 := res r1 (b ⋊ tt) in    (* f x b *)
        cost r1 + cost r2 + fold_left_fcost cf t (val cf (val cx) b ⋊ res r2)
    end.

  Fixpoint fold_left_pot {A CA B : Type}
    (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B unit -> ℂO CA)))
    (l : list B) (cx : ℂI A CA) : CA :=
    match l with
    | [] => pot cx
    | b :: t => fold_left_pot cf t (val cf (val cx) b ⋊ res (res (pot cf cx) (b ⋊ tt)))
    end.

  (** For a function of constant complexity, on ground data, the costs of
      its applications are linear in the length. *)
  Lemma fold_left_fcost_constant {A B} (f : A -> B -> A) (c1 c2 : nat) l cx :
    fold_left_fcost (f ⋊ (fun _ : ℂI A unit => c1 +> fun _ : ℂI B unit => c2 >|)) l cx = (c1 + c2) * length l.
  Proof.
    revert cx. induction l as [|b t IH]; intro cx; cbn [fold_left_fcost length]; cbn; [lia|].
    rewrite IH. lia.
  Qed.

  (** [fold_left] itself, a higher-order bound: for any function `f`, of
      complexity [cf], and an accumulator of any type. The bound of
      `fold_left f` follows for any bound of `f` ([apply_complexity]); for
      a constant one, on ground data, it is a linear bound in the length, of
      slope [c1 + c2 + 40] ([fold_left_fcost_constant]). [fold_left] is a
      fixpoint under `fun f`: `f` is in the environment of the fixpoint
      ([crec_env]), and the recursive calls do not pass it again. *)
  Lemma fold_left_ground_hcomplexity {A CA B} `{Repr A CA} `{Ground B} :
    Time.ComplexityBound (@fold_left A B)
      (fun cf => 1 +> fun cl => 4 +> fun cx =>
         (fold_left_fcost cf (val cl) cx + 40 * length (val cl) + 6) +> fold_left_pot cf (val cl) cx).
  Proof. cbound. Qed.

  (** [fold_right f a0 l], for any function [f] on ground data, of
      complexity [cf]: the costs of the applications of [f] to the elements
      and to the accumulators, as [cf] gives them ([fold_right_fcost]); the
      accumulators are the values that [f] computes. *)
  Fixpoint fold_right_fcost {A B : Type}
    (cf : ℂI (B -> A -> A) (ℂI B unit -> ℂO (ℂI A unit -> ℂO unit))) (a0 : A) (l : list B) : nat :=
    match l with
    | [] => 0
    | b :: t =>
        let r1 := pot cf (b ⋊ tt) in
        cost r1 + cost (res r1 (fold_right (val cf) a0 t ⋊ tt)) + fold_right_fcost cf a0 t
    end.

  Lemma fold_right_ground_hcomplexity {A B} `{Ground A} `{Ground B} :
    Time.ComplexityBound (@fold_right A B)
      (fun cf => 1 +> fun ca0 => 2 +> fun cl =>
         (fold_right_fcost cf (val ca0) (val cl) + 28 * length (val cl) + 10) >|).
  Proof. cbound. Qed.

  (** A closed bound, in the sizes: when the applications of [f] cost at
      most [c1] and [g #|x| #|y|], for a monotone [g], and each one adds at
      most the size of the element and [d] to the accumulator, each costs
      at most [c1 + g #|l| (#|a0| + #|l| + d * length l)]. *)
  Section ClosedBound.
    Context {A B : Type} `{Size A} `{Size B}.
    Context (cf : ℂI (B -> A -> A) (ℂI B unit -> ℂO (ℂI A unit -> ℂO unit))) (a0 : A).
    Context (c1 d : nat) (g : nat -> nat -> nat).
    Hypothesis g_mono : forall x y x' y', x <= x' -> y <= y' -> g x y <= g x' y'.
    Hypothesis cf_cost1 : forall x, cost (pot cf (x ⋊ tt)) <= c1.
    Hypothesis cf_cost2 : forall x y, cost (res (pot cf (x ⋊ tt)) (y ⋊ tt)) <= g #|x| #|y|.
    Hypothesis cf_size : forall x y, #|val cf x y| <= #|x| + #|y| + d.

    Lemma fold_right_size_le l : #|fold_right (val cf) a0 l| <= #|a0| + #|l| + d * length l.
    Proof.
      induction l as [|x l IH]; cbn [fold_right length]; [lia|].
      rewrite size_cons. pose proof (cf_size x (fold_right (val cf) a0 l)). lia.
    Qed.

    Lemma fold_right_fcost_le_gen S L l :
      #|l| <= S -> length l <= L ->
      fold_right_fcost cf a0 l <= length l * (c1 + g S (#|a0| + S + d * L)).
    Proof.
      induction l as [|x l IH]; intros HS HL; cbn [fold_right_fcost length]; [lia|].
      rewrite size_cons in HS. cbn [length] in HL.
      pose proof (cf_cost1 x). pose proof (cf_cost2 x (fold_right (val cf) a0 l)).
      pose proof (fold_right_size_le l).
      assert (g #|x| #|fold_right (val cf) a0 l| <= g S (#|a0| + S + d * L)) by (apply g_mono; nia).
      specialize (IH ltac:(lia) ltac:(lia)). nia.
    Qed.

    Lemma fold_right_fcost_le l :
      fold_right_fcost cf a0 l <= length l * (c1 + g #|l| (#|a0| + #|l| + d * length l)).
    Proof. apply fold_right_fcost_le_gen; lia. Qed.
  End ClosedBound.

  (** The closed bound of [fold_right f], for a function [f] of such a
      complexity. *)
  Lemma fold_right_size_complexity {A B} `{Ground A} `{Size A} `{Ground B} `{Size B}
      (f : B -> A -> A) (c1 d : nat) (g : nat -> nat -> nat) :
    (forall x y x' y', x <= x' -> y <= y' -> g x y <= g x' y') ->
    Time.ComplexityBound f (fun cx : ℂI B unit => c1 +> fun cy : ℂI A unit => g #|val cx| #|val cy| >|) ->
    (forall x y, #|f x y| <= #|x| + #|y| + d) ->
    Time.ComplexityBound (fold_right f)
      (fun ca0 : ℂI A unit => 2 +> fun cl : ℂI (list B) (list unit) =>
         (length (val cl) * (c1 + g #|val cl| (#|val ca0| + #|val cl| + d * length (val cl)))
          + 28 * length (val cl) + 10) >|).
  Proof.
    intros Hg Hf Hd.
    eapply ComplexityBound_mono; [| exact (apply_complexity _ Hf fold_right_ground_hcomplexity)].
    cbv beta; cbn [res]; bo_split; destr_inputs; cbn [cost val pot res]; [lia|].
    match goal with |- context [fold_right_fcost ?cf ?a0 ?l] =>
      pose proof (fold_right_fcost_le cf a0 c1 d g Hg (fun _ => le_n _) (fun _ _ => le_n _) Hd l) end.
    lia.
  Qed.

  (* TODO: a closed bound for fold_left, as fold_right_fcost_le, from the
    relation between complexity and size; then for other higher-order list
    functions, like iter. *)

  (** [map], [filter], [existsb], [forallb] and [flat_map], for any
      function [f] on ground data, of complexity [cf]: the costs of its
      applications to the elements, as [cf] gives them. [existsb] and
      [forallb] may stop before the end: the bound counts all the
      elements. *)
  Global Instance map_complexity {A B} `{Ground A} `{Ground B} :
    Time.ComplexityBound (@map A B)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf (x ⋊ tt))) (val cl)) + 29 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance filter_complexity {A} `{Ground A} :
    Time.ComplexityBound (@filter A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf (x ⋊ tt))) (val cl)) + 33 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance existsb_complexity {A} `{Ground A} :
    Time.ComplexityBound (@existsb A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf (x ⋊ tt))) (val cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  Global Instance forallb_complexity {A} `{Ground A} :
    Time.ComplexityBound (@forallb A)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf (x ⋊ tt))) (val cl)) + 32 * length (val cl) + 6) >|).
  Proof. cbound. Qed.

  (** [flat_map f l] appends the lists that [f] gives: the cost of [app] is
      linear in the length of each of them. *)
  Global Instance flat_map_complexity {A B} `{Ground A} `{Ground B} :
    Time.ComplexityBound (@flat_map A B)
      (fun cf => 1 +> fun cl =>
         (list_sum (map (fun x => cost (pot cf (x ⋊ tt))) (val cl))
          + 21 * list_sum (map (fun x => length (val cf x)) (val cl))
          + 38 * length (val cl) + 6) >|).
  Proof. cbound. Qed.
  (** ** Bounds in the size of the arguments

      [fold_left] is higher-order: its bound depends on the one of its
      function. *)
  Global Instance tl_constant_bound {A} `{Ground A} `{Size A} : Time.ConstantBound (@tl A) := _.
  Global Instance length_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@length A) := _.
  Global Instance app_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@app A) := _.
  Global Instance seq_linear_bound : Time.LinearBound seq := _.
  Global Instance firstn_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@firstn A) := _.
  Global Instance skipn_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@skipn A) := _.
  Global Instance nth_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@nth A) := _.
  Global Instance repeat_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@repeat A) := _.
  Global Instance hd_constant_bound {A} `{Ground A} `{Size A} : Time.ConstantBound (@hd A) := _.
  Global Instance rev_polynomial_bound {A} `{Ground A} `{Size A} : Time.PolynomialBound (@rev A) := _.
  Global Instance combine_linear_bound {A B} `{Ground A} `{Size A} `{Ground B} `{Size B} :
    Time.LinearBound (@combine A B) := _.
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma seq_size_complexity :
    Time.ComplexityBound seq
      (fun cs => 4 +> fun (cn : ℂI nat _) => (33 * #|val cn| + 0) >|).
  Proof. csize_using seq_complexity. Qed.

End ListComplexity.
