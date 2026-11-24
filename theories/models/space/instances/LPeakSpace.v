(** * Peak space of L, on an environment machine

    L run by the environment machine of [LMachine], whose closures and
    environments are cells of a heap. Each cell has a stamp, the order of
    its allocation: two values share a cell when they have the same stamp,
    and a cell only points to older ones (no mutation). The memory in use
    is the set of the cells reachable from the roots of the computation,
    those of its context included: a garbage collector frees the others.

    A run has a profile ([SpaceCostModel]): its steps, the memory above
    its start at its high point, and the memory that it returns at its end
    ([need] and [ret]). *)

From Stdlib Require Import List Lia PeanoNat.
From Complexity Require Import SpaceCostModel.
From Undecidability.L Require Import L.
Import ListNotations.
Local Open Scope nat_scope.

(** ** The machine *)

(** A closure, with its stamp, its code and its environment; an
    environment, a list of cells. *)
Inductive value : Type := clos (i : nat) (s : term) (E : envr)
with envr : Type := enil | econs (i : nat) (v : value) (E : envr).

Fixpoint lookup (E : envr) (n : nat) : option value :=
  match E, n with
  | econs _ v _, 0 => Some v
  | econs _ _ E, S n => lookup E n
  | enil, _ => None
  end.

(** The cells reachable from a value, from an environment. *)
Fixpoint vcells (v : value) : list nat :=
  match v with clos i _ E => i :: ecells E end
with ecells (E : envr) : list nat :=
  match E with enil => [] | econs i v E => i :: vcells v ++ ecells E end.

(** The memory in use: the cells of a list of stamps, without repetition. *)
Definition mem (l : list nat) : nat := length (nodup Nat.eq_dec l).

Definition is_value_term (t : term) : bool := match t with app _ _ => false | _ => true end.

(** The frame of a subterm of an application that is not a value: one
    cell, the stamp [c]. *)
Definition frame (c : nat) (t : term) : list nat := if is_value_term t then [] else [c].
Definition frame_size (t : term) : nat := if is_value_term t then 0 else 1.

(** [ev K c E s v c' n p]: in a context that holds the cells [K], [s], in
    [E], evaluates to [v] in [n] β-steps, allocating the stamps from [c]
    to [c' - 1], with [p] cells in use at its high point, those of [K]
    included.
    - A variable is read, and a λ allocates a closure.
    - An application evaluates its function in a frame, holding [E] for
      its argument, then its argument in a frame, holding the function,
      then the body of the function in its environment extended with the
      argument, a new cell: in tail position, the context of the
      application only. *)
Inductive ev : list nat -> nat -> envr -> term -> value -> nat -> nat -> nat -> Prop :=
| ev_var K c E n v :
    lookup E n = Some v ->
    ev K c E (var n) v c 0 (mem (K ++ ecells E))
| ev_lam K c E s :
    ev K c E (lam s) (clos c s E) (S c) 0
      (Nat.max (mem (K ++ ecells E)) (mem (K ++ c :: ecells E)))
| ev_app K c E s t u E' i w v c1 c2 c3 n1 n2 n3 p1 p2 p3 :
    ev (K ++ frame c s ++ ecells E) (S c) E s (clos i u E') c1 n1 p1 ->
    ev (K ++ frame c1 t ++ vcells (clos i u E')) (S c1) E t w c2 n2 p2 ->
    ev K (S c2) (econs c2 w E') u v c3 n3 p3 ->
    ev K c E (app s t) v c3 (S (n1 + n2 + n3)) (Nat.max p1 (Nat.max p2 p3)).

(** The call of a closure [f] on [w], in a context [K]: its body, in its
    environment extended with [w], a new cell. *)
Definition call (K : list nat) (c : nat) (f w v : value) (c' n p : nat) : Prop :=
  match f with clos _ u E => ev K (S c) (econs c w E) u v c' n p end.

(** The profile of a call of [f] on [w] that returns [v], in a context
    that holds [K]: its steps, the memory above its start at its high
    point, and the memory that it returns at its end. *)
Definition call_profile (K : list nat) (f w v : value) (n p : nat) : sprof :=
  SP n (p - mem (K ++ vcells f ++ vcells w)) (p - mem (K ++ vcells v)).

(** ** A first check: the identity

    The call of [λ x. x] on [w] reads [x]: the memory of its environment,
    the new cell and the cells of [w]. The step of the call is counted by
    the application that makes it. *)
Lemma call_id K c j w :
  call K c (clos j (var 0) enil) w w (S c) 0 (mem (K ++ c :: vcells w)).
Proof.
  cbn [call]. replace (mem (K ++ c :: vcells w)) with (mem (K ++ ecells (econs c w enil))).
  - eapply (ev_var K (S c) (econs c w enil) 0 w). reflexivity.
  - cbn [ecells]. rewrite app_nil_r. reflexivity.
Qed.
