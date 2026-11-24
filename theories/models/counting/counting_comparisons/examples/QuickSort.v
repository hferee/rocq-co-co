(** * Quicksort, counting comparisons

    The deterministic quicksort of van der Weegen and McKinna ("A
    Machine-Checked Proof of the Average-Case Complexity of Quicksort in
    Coq", TYPES 2008): the head is the pivot, and one pass of comparisons
    partitions the tail into the smaller, equal and greater elements. The
    coefficient of [c_cmp] in its bound, [qs_cmps l], counts its
    comparisons. *)

From Complexity Require Export CmpCount.
From Stdlib Require Import List Lia Recdef.
Import ListNotations.

(** The timeout of the library ([ctimeout_lib]). *)
#[local] Ltac2 Set ctimeout := ctimeout_lib.

Module QuickSort (Import M : CmpOpsTimeCostModel).

  Local Ltac wf_case :=
    match goal with
    | E : val ?cl = _, W : wf (val ?cl) (pot ?cl) |- _ =>
        rewrite E in W;
        first [apply wf_nil in W; rewrite W | destruct (wf_cons _ _ _ W) as (? & ? & -> & _)]
    end.

  (** [l ++ m]: [length l + 1] unfoldings, no comparison. *)
  Global Instance app_complexity {A CA} `{Repr A CA} : ComplexityBound (@app A)
    (fun cl : ℂI (list A) (list CA) => 0 +> fun cm : ℂI (list A) (list CA) =>
       (length (val cl) + 1) +> (pot cl ++ pot cm)).
  Proof. cbound; wf_case; reflexivity. Qed.

  (** ** Partition *)

  Fixpoint partition (p : elt) (l : list elt) : list elt * list elt * list elt :=
    match l with
    | [] => ([], [], [])
    | x :: t =>
        match partition p t with
        | (lo, eq, hi) =>
            match cmp x p with
            | Lt => (x :: lo, eq, hi)
            | Eq => (lo, x :: eq, hi)
            | Gt => (lo, eq, x :: hi)
            end
        end
    end.

  Lemma partition_length p l :
    let '(lo, eq, hi) := partition p l in length lo + length eq + length hi = length l.
  Proof.
    induction l as [|x t IH]; [reflexivity|]. cbn.
    destruct (partition p t) as [[lo eq] hi]. destruct (cmp x p); cbn; lia.
  Qed.

  (** The complexities of lists of elements: [tt] for each. *)
  Definition units {A} (l : list A) : list unit := map (fun _ => tt) l.
  Definition units3 {A} (r : list A * list A * list A) :=
    let '(lo, eq, hi) := r in (units lo, units eq, units hi).

  (** One comparison and one unfolding per element. *)
  Global Instance partition_complexity : ComplexityBound partition
    (fun cp => 0 +> fun cl => ((c_cmp + 1) * length (val cl) + 1) +>
       units3 (partition (val cp) (val cl))).
  Proof.
    cbound.
    all: cbn [units3] in *;
         repeat match goal with H : (_, _, _) = (_, _, _) |- _ => injection H as <- <- <- end.
    all: try lia.
    all: cbn [partition units3]; repeat match goal with H : ?x = _ |- context [?x] => rewrite H end;
         cbn; reflexivity.
  Qed.
  (** ** Quicksort *)

  Local Ltac part_lt :=
    intros; match goal with H : partition ?p ?t = (_, _, _) |- _ =>
      pose proof (partition_length p t) as Hl; rewrite H in Hl; cbn; lia end.

  Function qs (l : list elt) {measure length l} : list elt :=
    match l with
    | [] => []
    | p :: t => match partition p t with (lo, eq, hi) => qs lo ++ p :: eq ++ qs hi end
    end.
  Proof. all: part_lt. Defined.

  (** Its comparisons: [length t] to partition [p :: t], then those of the
      recursive calls. *)
  Function qs_cmps (l : list elt) {measure length l} : nat :=
    match l with
    | [] => 0
    | p :: t => match partition p t with (lo, _, hi) => length t + qs_cmps lo + qs_cmps hi end
    end.
  Proof. all: part_lt. Defined.

  Lemma qs_length l : length (qs l) = length l.
  Proof.
    functional induction (qs l); [reflexivity|].
    pose proof (partition_length p t) as Hl. rewrite e0 in Hl.
    rewrite !length_app; cbn; rewrite length_app; lia.
  Qed.

  Global Instance qs_value_fact l : ValueFact (qs l) (fun r => length r = length l) := qs_length l.

  (** [qs_cmps l] comparisons; the unfoldings, at most [2] per comparison and
      [6] per element. *)
  Lemma qs_complexity : ComplexityBound qs
    (fun cl => ((c_cmp + 2) * qs_cmps (val cl) + 6 * length (val cl) + 1) +> units (qs (val cl))).
  Proof.
    cbound.
    all: cbn [units3] in *;
         repeat match goal with H : (_, _, _) = (_, _, _) |- _ => injection H as <- <- <- end.
    all: match goal with H : partition ?p ?t = (_, _, _) |- _ =>
           pose proof (partition_length p t) as Hl; rewrite H in Hl;
           first [rewrite (qs_cmps_equation (p :: t)) | rewrite (qs_equation (p :: t))];
           cbv iota beta; rewrite H; cbv iota beta end.
    - rewrite !qs_length, !Nat.mul_add_distr_l. lia.
    - unfold units. rewrite !map_app. cbn [map]. rewrite map_app. reflexivity.
  Qed.
End QuickSort.
