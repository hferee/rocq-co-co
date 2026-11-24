(** * The allocation cost model with sizes (aside)

    An experiment, set aside: the definition of the sizes is still open
    ([hosize-plan.md]). *)

From Complexity Require Export AllocationCostModel.

Module Type SizedAllocationAxioms
  (Import CM : CostModel
    with Definition Cost := nat with Definition cle := le with Definition cnat := fun n : nat => n).

  (** [cshift h k c]: [c] with [k] added to the cost of every application. *)
  Fixpoint cshift {σ A CA} (h : HigherOrder σ A CA) (k : nat) : CA -> CA :=
    match h in HigherOrder σ A CA return CA -> CA with
    | ho_ground _ _ => fun c => c
    | ho_arr _ h2 => fun c x => k + cost (c x) +> cshift h2 k (res (c x))
    end.

  (** The footprint of the values: the memory that represents them. *)
  Parameter footprint : forall {A CA} (R : Repr A CA), Size A.

  (** The base types of [h] are measured at most by their footprint. *)
  Fixpoint Footprinted {σ A CA} (h : HigherOrder σ A CA) : Prop :=
    match h with
    | @ho_ground A _ RA sA => forall x : A, sA x <= footprint RA x
    | ho_arr h1 h2 => Footprinted h1 /\ Footprinted h2
    end.

  (** The allocations are size bounds ([CSized], [HOBounds]), up to a
      constant (the literals of the program): a function only creates what
      it allocates, its questions, the sub-dialogues they trigger, and its
      values. A time bound on a functional could then be expressed in the
      time and the space of its arguments ([smaj], [HPolyBoundS]). *)
  Parameter sized_allocations : forall σ A CA (h : HigherOrder σ A CA) f c,
    Footprinted h -> HOBound h f c -> exists k, CSized h f (cshift h k c).
End SizedAllocationAxioms.

Module Type SizedAllocationCostModel := AllocationCostModel.AllocationCostModel <+ SizedAllocationAxioms.
