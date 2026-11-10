(** * The space cost model with sizes (aside)

    The space cost model ([SpaceCostModel]) with an axiom relating its
    allocations to the sizes of functionals ([CSized], [HOBounds]): a bound
    on the allocation of a function is a bound on its size
    ([sized_allocations]), so that a time bound on a functional could be
    expressed in the time and the space of its arguments ([smaj],
    [HPolyBoundS]). The sizes charge only what a function creates: its
    questions, the sub-dialogues they trigger, and the values it creates.
    The ground values are measured at most by their footprint, the memory
    that represents them ([footprint]).

    This is an experiment, set aside: the definition of the sizes is still
    open (see [hosize-plan.md]). *)

From Complexity Require Export SpaceCostModel.

Module Type SizedAllocCostModel (Import CM : CostModel).

  (** The footprint of the ground values: the memory that represents them. *)
  Parameter footprint : forall {A}, Ground A -> Size A.

  (** The ground types of [h] are measured at most by their footprint. *)
  Fixpoint Footprinted {σ A CA} (h : HigherOrder σ A CA) : Prop :=
    match h with
    | @ho_ground A RA sA => forall x : A, sA x <= footprint RA x
    | ho_arr h1 h2 => Footprinted h1 /\ Footprinted h2
    end.

  (** The allocations are size bounds, up to a constant (the literals of
      the program): a function only creates what it allocates. *)
  Parameter sized_allocations : forall σ A CA (h : HigherOrder σ A CA) f c,
    Footprinted h -> HOBound h f c -> exists k, CSized h f (cplus h k c).
End SizedAllocCostModel.

Module Type AllocCostModel := SpaceCostModel.SpaceCostModel <+ SizedAllocCostModel.
