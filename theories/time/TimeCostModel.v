(** * The time cost model

    The axioms of the time cost model, as one signature, over which the
    analyses are functors. The generic part ([CostModel]: complexities and
    their bounds) is independent of the resource; the costs of the
    primitives are those of time: application ([BasicTimeCostModel]), the
    combinators of compiled terms ([CombinatorTimeCostModel]), the datatypes
    ([TimeDatatypes]) and fixpoints ([FixTimeCostModel]). *)

From Complexity Require Export CostModel TimeBasic TimeCombinators TimeDatatypes
  TimeFix.

Module Type TimeCostModel := CostModel.CostModel <+ BasicTimeCostModel <+ CombinatorTimeCostModel
  <+ BoolTimeCostModel <+ NatTimeCostModel <+ ListTimeCostModel <+ OptionTimeCostModel
  <+ ProdTimeCostModel <+ ZTimeCostModel <+ FixTimeCostModel.
