(** * The time cost model

    The axioms of the time cost model, as one signature, over which the
    analyses are functors. The generic part ([CostModel]: complexities and
    their bounds) is independent of the resource; the costs of the
    primitives are those of time: application ([BasicTimeCostModel]), the
    combinators of compiled terms ([CombinatorTimeCostModel]), the datatypes
    ([TimeDatatypes]) and fixpoints ([FixTimeCostModel]).

    The costs of the primitives are constants, parameters of the module
    types ([c_clo], [c_step], [c_S], [c_case_nat], ..., [c_fix]).
    [ParamTimeCostModel] leaves them abstract. A cost model is a choice of
    layers and a choice of constants, fixed with [with Definition]: in
    [TimeCostModel], over which the analyses of the standard library are
    proved, every constant is [1] (each application is a beta-step of L,
    [LInstance]). [TimeArith] defines another model, from other layers. *)

From Complexity Require Export TimeDatatypes TimeFix.

Module Type ParamTimeCostModel := CostModel.CostModel <+ BasicTimeCostModel
  <+ CombinatorTimeCostModel <+ BoolTimeCostModel <+ NatTimeCostModel <+ ListTimeCostModel
  <+ OptionTimeCostModel <+ ProdTimeCostModel <+ ZTimeCostModel <+ FixTimeCostModel.

Module Type TimeCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_step := 1
  with Definition c_case_bool := 1
  with Definition c_S := 1 with Definition c_case_nat := 1
  with Definition c_cons := 1 with Definition c_case_list := 1
  with Definition c_Some := 1 with Definition c_case_option := 1
  with Definition c_pair := 1 with Definition c_case_prod := 1
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 1
  with Definition c_fix := 1.
