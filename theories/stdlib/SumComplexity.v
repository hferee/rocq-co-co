(** * Complexity of the functions on sums

    The standard library defines the sum [A + B] (with [inl] and [inr]) but
    no function on it. The usual ones are defined here (Haskell's [isLeft],
    [either], [lefts], ...), and [cbound] proves their bounds, as in
    [NatComplexity], with the smallest constants.

    Sums are of any data ([SumTimeCostModel] in [TimeDatatypes]): the
    complexity of a sum is the sum of the complexities, and a bound reads
    the element with its complexity ([czip_sum]). The functions on sums
    alone are proved over the model without lists ([SumComplexity], over
    [TimeCostModelBase]); those on lists of sums ([SumListComplexity]) read
    the lists with their complexities ([czip]), as for lists of any data. *)

From Complexity Require Export TimeCostModel HOListComplexity.
From Stdlib Require Import List.
Import ListNotations.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** ** The functions *)

Definition is_inl {A B} (x : A + B) : bool := match x with inl _ => true | inr _ => false end.
Definition is_inr {A B} (x : A + B) : bool := match x with inl _ => false | inr _ => true end.

Definition sum_swap {A B} (x : A + B) : B + A :=
  match x with inl a => inr a | inr b => inl b end.

(** The non-dependent eliminator ([either] in Haskell). *)
Definition sum_elim {A B C} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with inl a => f a | inr b => g b end.

Definition sum_map {A B C D} (f : A -> C) (g : B -> D) (x : A + B) : C + D :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

Definition get_inl {A B} (x : A + B) : option A :=
  match x with inl a => Some a | inr _ => None end.
Definition get_inr {A B} (x : A + B) : option B :=
  match x with inl _ => None | inr b => Some b end.

(** The elements of a list of sums. *)
Fixpoint lefts {A B} (l : list (A + B)) : list A :=
  match l with [] => [] | inl a :: l => a :: lefts l | inr _ :: l => lefts l end.
Fixpoint rights {A B} (l : list (A + B)) : list B :=
  match l with [] => [] | inl _ :: l => rights l | inr b :: l => b :: rights l end.

(** A sum with its complexity, as the case analysis reads it: its element
    with its complexity, or with the default [da] or [db] when the
    complexity is of the other side (which does not happen; the models use
    [cdefault]). *)
Definition czip_sum {A CA B CB} (da : CA) (db : CB) (c : ℂI (A + B) (CA + CB)) : ℂI A CA + ℂI B CB :=
  match val c, pot c with
  | inl a, inl ca => inl (a ⋊ ca)
  | inl a, inr _ => inl (a ⋊ da)
  | inr b, inr cb => inr (b ⋊ cb)
  | inr b, inl _ => inr (b ⋊ db)
  end.
#[global] Hint Unfold czip_sum : costs.

(** ** Sums *)

Module SumComplexity (Import Time : TimeCostModelBase).

  Global Instance is_inl_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@is_inl A B) (fun cx => 3 >|) := _.
  Global Instance is_inr_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@is_inr A B) (fun cx => 3 >|) := _.

  Global Instance sum_swap_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@sum_swap A B)
      (fun cx => 5 +> match czip_sum cdefault cdefault cx with
                      | inl x => @inr CB CA (pot x)
                      | inr y => @inl CB CA (pot y)
                      end).
  Proof. cbound. Qed.

  Global Instance sum_elim_complexity {A CA B CB C CC} `{Repr A CA} `{Repr B CB} `{Repr C CC} :
    Time.ComplexityBound (@sum_elim A B C)
      (fun cf : ℂI (A -> C) (ℂI A CA -> ℂO CC) => 1 +>
       fun cg : ℂI (B -> C) (ℂI B CB -> ℂO CC) => 2 +>
       fun cx : ℂI (A + B) (CA + CB) =>
         10 ⊕ match czip_sum cdefault cdefault cx with inl x => pot cf x | inr y => pot cg y end).
  Proof. cbound. Qed.

  Global Instance sum_map_complexity {A CA B CB C CC D CD}
    `{Repr A CA} `{Repr B CB} `{Repr C CC} `{Repr D CD} :
    Time.ComplexityBound (@sum_map A B C D)
      (fun cf : ℂI (A -> C) (ℂI A CA -> ℂO CC) => 1 +>
       fun cg : ℂI (B -> D) (ℂI B CB -> ℂO CD) => 2 +>
       fun cx : ℂI (A + B) (CA + CB) =>
         12 ⊕ match czip_sum cdefault cdefault cx with
              | inl x => @inl CC CD <$> pot cf x
              | inr y => @inr CC CD <$> pot cg y
              end).
  Proof. cbound. Qed.

End SumComplexity.

(** ** Options and lists of sums *)

Module SumListComplexity (Import Time : TimeCostModel).

  Global Instance get_inl_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@get_inl A B)
      (fun cx : ℂI (A + B) (CA + CB) => 5 +> match czip_sum cdefault cdefault cx with
                      | inl x => Some (pot x)
                      | inr _ => @None CA
                      end).
  Proof. cbound. Qed.
  Global Instance get_inr_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@get_inr A B)
      (fun cx : ℂI (A + B) (CA + CB) => 5 +> match czip_sum cdefault cdefault cx with
                      | inl _ => @None CB
                      | inr y => Some (pot y)
                      end).
  Proof. cbound. Qed.

  (** An element [inl] costs [27], an element [inr] [22] (it builds no
      cell). *)
  Global Instance lefts_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@lefts A B)
      (fun cl : ℂI (list (A + B)) (list (CA + CB)) => (27 * length (val cl) + 6)
                 +> map (@pot A CA) (lefts (map (czip_sum cdefault cdefault) (czip cdefault cl)))).
  Proof. cbound. Qed.
  Global Instance rights_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@rights A B)
      (fun cl : ℂI (list (A + B)) (list (CA + CB)) => (27 * length (val cl) + 6)
                 +> map (@pot B CB) (rights (map (czip_sum cdefault cdefault) (czip cdefault cl)))).
  Proof. cbound. Qed.

End SumListComplexity.
