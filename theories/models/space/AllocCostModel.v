(** * The total allocation model with sizes (aside)

    An experiment, set aside: the definition of the sizes is still open
    ([hosize-plan.md]). *)

From Complexity Require Export TotalAllocationModel.

Module Type SizedAllocCostModel (Import CM : CostModel).

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
    Footprinted h -> HOBound h f c -> exists k, CSized h f (cplus h k c).
End SizedAllocCostModel.

Module Type AllocCostModel := TotalAllocationModel.TotalAllocationModel <+ SizedAllocCostModel.
