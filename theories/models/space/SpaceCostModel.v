(** * Peak space

    The memory in use at the high point of a computation, the memory freed
    by the garbage collector being reused ([AllocationCostModel] never
    frees). A cost is a profile [SP steps need ret]:
    - [need]: the memory needed at the start, the high point above the
      memory in use then;
    - [ret]: the memory returned (freed) at the end;
    - [steps]: the unfoldings, which keep the fixpoint rule sound
      ([FixCosts]), as a loop may run in constant space.
    On [need] and [ret], the resource monoid of the high-water marks of
    Hoffmann and Hofmann ("Amortized resource analysis with polymorphic
    recursion and partial big-step operational semantics", APLAS 2010), as
    in calf ([ResourceMonoid]): in sequence ([sseq]), the second
    computation runs in what the first returns. Allocating [n] cells is
    [cells n], freeing them [frees n]; a frame is allocated, then freed
    ([c_frame], [c_pop]). [need - ret] is the memory still allocated at the
    end: an upper bound on what the result reaches, garbage included.

    This is the reachable heap of the profiling semantics of
    Paraskevopoulou and Appel ("Closure conversion is safe for space",
    ICFP 2019). Here closures are linked: a closure keeps the whole
    environment where it is built ([Combinators]), which they show is not
    safe for space, unlike flat closures. *)

From Complexity Require Export Generic PeakSpace.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Record sprof := SP { steps : nat; need : nat; ret : nat }.

(** By matching, which the tactics reduce ([csimpl]). *)
Definition sseq (a b : sprof) : sprof :=
  let 'SP s p p' := a in let 'SP s' q q' := b in SP (s + s') (p + (q - p')) (q' + (p' - q)).
(** [a] is below [b]: fewer steps, less memory needed, more returned. *)
Definition sle (a b : sprof) : Prop :=
  let 'SP s p p' := a in let 'SP s' q q' := b in s <= s' /\ p <= q /\ q' <= p'.
Definition speak (a : sprof) : nat := let 'SP _ p _ := a in p.

(** [n] cells allocated, [n] cells freed. *)
Definition cells (n : nat) : sprof := SP 0 n 0.
Definition frees (n : nat) : sprof := SP 0 0 n.

(** The tactics compute the profiles ([costs]), whose truncated
    subtractions [lia] handles. *)
#[global] Hint Unfold sseq sle speak cells frees : costs.

Ltac2 Set cnorm_hook as previous := fun () =>
  previous (); ltac1:(repeat match goal with |- _ /\ _ => split end).

(** The generic cost model ([Generic]), and the releases of the scopes
    and loops ([PeakSpace]). *)
Module Type ParamSpaceCostModel := ParamCostModel <+ PeakSpaceAxioms.

Module Type SpaceCostModel := ParamSpaceCostModel
  with Definition Cost := sprof with Definition cle := sle
  (* the bounds in the sizes are on the peak *)
  with Definition cnat := speak
  with Definition czero := SP 0 0 0 with Definition cplus := sseq
  (* a closure: a cell; a frame: a cell, freed after the evaluation *)
  with Definition c_clo := cells 1 with Definition c_frame := cells 1 with Definition c_pop := frees 1
  (* a call extends the environment with the argument *)
  with Definition c_Lam := cells 1
  with Definition c_ehd := cells 0 with Definition c_etl := cells 0
  with Definition c_Kc := cells 0 with Definition c_consume := cells 0 with Definition c_etlc := cells 0 with Definition c_Ic := cells 0
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
  with Definition c_fix := SP 1 1 0
  (* a scope with a ground result frees the cells of its environment; an
     iteration: a step *)
  with Definition c_unLam := frees 1 with Definition c_uncase_nat := frees 1
  with Definition c_uncase_list := frees 2 with Definition c_iter := SP 1 0 0.
