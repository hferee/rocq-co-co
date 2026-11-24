(** * The generic cost model

    The cost model shared by all the models, its costs left abstract: the
    combinators ([CombinatorCosts]), the datatypes ([DatatypeCosts],
    [ListCosts]) and fixpoints ([FixCosts]), over [CostModel]. A model fixes
    the costs and the constants ([TimeCostModel], [AllocationCostModel],
    [SpaceCostModel]). *)

From Complexity Require Export DatatypeCosts ListCosts FixCosts.

(** The generic cost model without lists, options and pairs. The costs of the
    primitives are constants, parameters of the module types ([c_clo], ...,
    [c_fix]), left abstract here, as the costs ([Cost], [cle], [cplus],
    ...): a cost model is a choice of parts of the generic cost model, of
    costs and of constants, fixed with [with Definition]. *)
Module Type ParamCostModelBase := CostModel.CostModel <+ BasicCostModel
  <+ CombinatorCostModel <+ BoolCostModel <+ NatCostModel
  <+ SumCostModel <+ SumGround <+ ZCostModel <+ FixCostModel.

(** With lists, options and pairs of any data, functions included; ground
    data (numbers, pairs of numbers, ...) are those whose complexities
    carry no information ([IsGround]). Lists are not ground: their
    complexities have their lengths ([wf_list]). *)
Module Type ParamCostModel := ParamCostModelBase
  <+ ListCostModel <+ ListWf <+ OptionCostModel <+ OptionGround
  <+ ProdCostModel <+ ProdGround.

