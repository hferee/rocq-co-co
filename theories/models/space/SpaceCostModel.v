(** * Peak space

    The memory in use at the high point of a computation, the memory freed
    by the garbage collector being reused ([TotalAllocationModel] never
    frees). A cost is a profile [sprof]:
    - [peak]: the high point, above the memory in use at the start;
    - [keep]: the memory allocated and still reachable from the result;
    - [steps]: the unfoldings, which keep the fixpoint rule sound
      ([TimeFix]), as a loop may run in constant space.
    In sequence, the first result is kept during the second computation
    ([sseq]); a frame is held during the evaluation of a subterm, then
    freed ([saround]). [keep] is an upper bound: what the result may
    reach is counted, even if it is garbage.

    This is the reachable heap of the profiling semantics of
    Paraskevopoulou and Appel ("Closure conversion is safe for space",
    ICFP 2019). Here closures are linked: a closure keeps the whole
    environment where it is built ([Combinators]), which they show is not
    safe for space, unlike flat closures. *)

From Complexity Require Export TimeCostModel.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Record sprof := SP { steps : nat; peak : nat; keep : nat }.

(** By matching, which the tactics reduce ([csimpl]). *)
Definition sseq (a b : sprof) : sprof :=
  let 'SP s p k := a in let 'SP s' p' k' := b in SP (s + s') (Nat.max p (k + p')) (k + k').
Definition saround (a b : sprof) : sprof :=
  let 'SP s p k := a in let 'SP s' p' k' := b in SP (s + s') (Nat.max p (k + p')) k'.
Definition sle (a b : sprof) : Prop :=
  let 'SP s p k := a in let 'SP s' p' k' := b in s <= s' /\ p <= p' /\ k <= k'.
Definition speak (a : sprof) : nat := let 'SP _ p _ := a in p.

#[global] Instance sle_preorder : PreOrder sle.
Proof. split; [intros [] | intros [] [] []]; cbn; lia. Qed.

#[global] Instance space_alg : CostAlg sprof :=
  {| czero := SP 0 0 0; cseq := sseq; caround := saround; cle := sle;
     ctick := SP 1 0 0; cnat := speak; cofnat n := SP n n 0; cnat_cofnat _ := eq_refl |}.

(** [n] cells allocated, and kept. *)
Definition cells (n : nat) : sprof := SP 0 n n.

(** The tactics compute the profiles ([costs]), and prove a property of
    a peak, a maximum, for each of its terms ([max_split]): [lia] would
    split cases. *)
#[global] Hint Unfold space_alg sseq saround sle speak cells : costs.

Lemma max_split (P : nat -> Prop) a b : P a -> P b -> P (Nat.max a b).
Proof. intros Ha Hb. destruct (Nat.max_spec a b) as [[_ ->] | [_ ->]]; assumption. Qed.

Ltac2 Set cnorm_hook as previous := fun () =>
  previous ();
  ltac1:(repeat match goal with
         | |- _ /\ _ => split
         | |- context [Nat.max ?a ?b] => pattern (Nat.max a b); apply max_split
         end).

Module Type SpaceCostModel := ParamCostModel
  with Definition Cost := sprof with Definition cost_alg := space_alg
  (* a closure: a cell; a frame: a cell, held during the evaluation *)
  with Definition c_clo := cells 1 with Definition c_frame := cells 1
  (* a call extends the environment with the argument *)
  with Definition c_Lam := cells 1
  with Definition c_ehd := cells 0 with Definition c_etl := cells 0
  with Definition c_Kc := cells 0 with Definition c_Ic := cells 0
  with Definition c_compose := cells 0 with Definition c_Cc := cells 0
  with Definition c_Sc := cells 0
  (* a constructor: a cell; a case analysis extends the environment with
     the arguments of the constructor *)
  with Definition c_case_bool := cells 0
  with Definition c_S := cells 1 with Definition c_case_nat := cells 1
  with Definition c_cons := cells 1 with Definition c_case_list := cells 2
  with Definition c_Some := cells 1 with Definition c_case_option := cells 1
  with Definition c_pair := cells 1 with Definition c_case_prod := cells 2
  with Definition c_ctor_sum := cells 1 with Definition c_case_sum := cells 1
  with Definition c_ctor_Z := cells 1 with Definition c_case_Z := cells 1
  (* an unfolding: a step, and the environment extended with the function *)
  with Definition c_fix := SP 1 1 1.
