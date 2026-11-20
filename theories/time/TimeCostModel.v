(** * The time cost model

    The axioms of the time cost model, as one signature, over which the
    analyses are functors: the generic part ([CostModel]), application
    ([BasicTimeCostModel]), the combinators of compiled terms
    ([CombinatorTimeCostModel]), the datatypes ([TimeDatatypes],
    [TimeLists]) and fixpoints ([FixTimeCostModel]). *)

From Complexity Require Export TimeDatatypes TimeLists TimeFix.

(** The layers without lists, options and pairs. The costs of the
    primitives are constants, parameters of the module types ([c_clo], ...,
    [c_fix]), left abstract here: a cost model is a choice of layers and of
    constants, fixed with [with Definition]. *)
Module Type ParamTimeCostModelBase := CostModel.CostModel <+ BasicTimeCostModel
  <+ CombinatorTimeCostModel <+ BoolTimeCostModel <+ NatTimeCostModel
  <+ SumTimeCostModel <+ SumGround <+ ZTimeCostModel <+ FixTimeCostModel.

(** The same, with the constants of [TimeCostModel]: the analyses that do not
    use lists, options or pairs ([BoolComplexity]) are functors over it. *)
Module Type TimeCostModelBase := ParamTimeCostModelBase
  with Definition c_clo := 1 with Definition c_frame := 0
  with Definition c_ehd := 1 with Definition c_etl := 1 with Definition c_Lam := 1
  with Definition c_Kc := 1 with Definition c_Ic := 1 with Definition c_compose := 1
  with Definition c_Cc := 1 with Definition c_Sc := 1
  with Definition c_case_bool := 1
  with Definition c_S := 1 with Definition c_case_nat := 1
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 1
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 1
  with Definition c_fix := 1.

(** With lists, options and pairs of any data, functions included; ground
    data (numbers, pairs of numbers, ...) are those whose complexities
    carry no information ([IsGround]). Lists are not ground: their
    complexities have their lengths ([wf_list]). *)
Module Type ParamTimeCostModel := ParamTimeCostModelBase
  <+ ListTimeCostModel <+ ListShapes <+ OptionTimeCostModel <+ OptionGround
  <+ ProdTimeCostModel <+ ProdGround.

(** Every constant is [1]: each application is a β-step of L
    ([LInstance]). The analyses of the standard library are proved over
    this model. *)
Module Type TimeCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_frame := 0
  with Definition c_ehd := 1 with Definition c_etl := 1 with Definition c_Lam := 1
  with Definition c_Kc := 1 with Definition c_Ic := 1 with Definition c_compose := 1
  with Definition c_Cc := 1 with Definition c_Sc := 1
  with Definition c_case_bool := 1
  with Definition c_S := 1 with Definition c_case_nat := 1
  with Definition c_cons := 1 with Definition c_case_list := 1
  with Definition c_Some := 1 with Definition c_case_option := 1
  with Definition c_pair := 1 with Definition c_case_prod := 1
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 1
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 1
  with Definition c_fix := 1.

