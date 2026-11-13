(** * Complexity of list functions from the standard library

    As in [NatComplexity]: [cbound] proves the bounds, with the smallest
    constants. These functions are
    defined in sections: their type and function parameters are fixed
    arguments of the fixpoint. A functional parameter comes with a
    hypothesis on its complexity ([fold_left_complexity]), or is an
    argument of the function, in the environment of its fixpoint
    ([fold_left_hcomplexity]). *)

From Complexity Require Export NatComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.


Module ListComplexity (Import Time : TimeNat).


  (** ** Sizes *)
  Lemma length_lt_size {A} `{Size A} (l : list A) : length l < size l.
  Proof. induction l as [|a l]; [apply size_nil | pose proof (size_cons a l); cbn [length]; lia]. Qed.

  Lemma list_sum_lt_size (l : list nat) : list_sum l + length l < size l.
  Proof.
    induction l as [|a l]; [apply size_nil|].
    change (list_sum (a :: l)) with (a + list_sum l). cbn [length].
    pose proof (nat_lt_size a). pose proof (size_cons a l). lia.
  Qed.

  Global Instance length_size_fact {A} `{Size A} (l : list A) :
    SizeFact l (length l < size l) | 10 := length_lt_size l.
  Global Instance list_sum_size_fact (l : list nat) :
    SizeFact l (list_sum l + length l < size l) | 1 := list_sum_lt_size l.

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

  (** [fold_left f], for a function [f] on ground data whose partial and
      full applications cost at most [c1] and [c2]. [f] is fixed: it is a
      parameter of the fixpoint, kept in the environment of its closure. *)
  Lemma fold_left_complexity {A B} `{Ground A} `{Ground B} (f : A -> B -> A) (c1 c2 : nat) :
    Time.ComplexityBound f (fun _ => c1 +> fun _ => c2 >|) ->
    Time.ComplexityBound (fold_left f)
      (fun cl => 4 +> fun cx =>
         ((c1 + c2 + 31) * length (val cl) + 6) >|).
  Proof. intro Hf. cbound. Qed.

(** The cost of `fold_left f l x`, from the complexity [cf] of `f` and
    [cx] of `x`: [k_nil] at the end of the list and, at each element `b`,
    [k_step] and the costs of the applications of `f` to the accumulator
    and to `b`, as [cf] gives them. The potential of the accumulator is
    the one that [cf] gives at the previous step, so that the accumulator
    may be of any type, a function for instance. The result is the last
    accumulator, with its potential. *)

  Fixpoint fold_left_cost {A CA B : Type} (k_nil k_step : nat)
    (cf : ℂI (A -> B -> A) (ℂI A CA -> ℂO (ℂI B unit -> ℂO CA)))
    (l : list B) (cx : ℂI A CA) : ℂO CA :=
    match l with
    | [] => k_nil +> pot cx
    | b :: t =>
        let r1 := pot cf cx in          (* f x *)
        let r2 := res r1 (b ⋊ tt) in    (* f x b *)
        (k_step + cost r1 + cost r2) ⊕
          fold_left_cost k_nil k_step cf t (val cf (val cx) b ⋊ res r2)
    end.

(** For a function of constant complexity, on ground data, the cost is
    linear in the length. *)
Lemma fold_left_cost_constant {A B} (f : A -> B -> A) (c1 c2 k_nil k_step : nat) l cx :
  cost (fold_left_cost k_nil k_step (f ⋊ (fun _ => c1 +> fun _ => c2 >|)) l cx)
  = (c1 + c2 + k_step) * length l + k_nil.
Proof.
  revert cx. induction l as [|b t IH]; intro cx; cbn [fold_left_cost length]; cbn; [lia|].
  rewrite IH. lia.
Qed.

  (** [fold_left] itself, a higher-order bound: for any function `f`, of
      complexity [cf], and an accumulator of any type ([fold_left_cost]).
      The bound of `fold_left f` follows for any bound of `f`
      ([apply_complexity]); for a constant one, on ground data, it is a
      linear bound in the length, of slope [c1 + c2 + 40]
      ([fold_left_cost_constant]). [fold_left] is a fixpoint under
      `fun f`: `f` is in the environment of the fixpoint ([crec_env]), and
      the recursive calls do not pass it again. *)
  Lemma fold_left_hcomplexity {A CA B} `{Repr A CA} `{Ground B} :
    Time.ComplexityBound (@fold_left A B)
      (fun cf => 1 +> fun cl => 4 +> fun cx => fold_left_cost 6 40 cf (val cl) cx).
  Proof. cbound. Qed.

  (* TODO: use the relation between complexity and size to obtain a closed 
    complexity bound for fold_left. *)

  (* TODO: once it's done, also find the bounds for other higher-order list
    functions like fold_right or iter. *)
  (** ** Bounds in the size of the arguments

      [fold_left] is higher-order: its bound depends on the one of its
      function. *)
  Global Instance tl_constant_bound {A} `{Ground A} `{Size A} : Time.ConstantBound (@tl A) := _.
  Global Instance length_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@length A) := _.
  Global Instance app_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@app A) := _.
  Global Instance seq_linear_bound : Time.LinearBound seq := _.
  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma seq_size_complexity :
    Time.ComplexityBound seq
      (fun cs => 4 +> fun (cn : ℂI nat _) => (33 * #|val cn| + 0) >|).
  Proof. csize_using seq_complexity. Qed.

End ListComplexity.
