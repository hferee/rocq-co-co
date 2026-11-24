(** * The allocation cost model

    The memory that a computation allocates, never freed: the generic cost
    model ([Generic]) with costs in [nat], the allocations of the
    primitives: at least the peak of the memory in use ([SpaceCostModel]). *)

From Complexity Require Export TimeCostModel.

(** Costs are added along a computation ([CostOps.capp]). Each
    constant is at most its value in [TimeCostModel]: every allocation
    happens in a step, so the total allocation is at most the time. *)
Module Type AllocationCostModel := ParamTimeCostModel
  (* a closure and a constructor allocate one cell; the combinators and the
     case analyses only read memory *)
  with Definition c_clo := 1 with Definition c_frame := 0 with Definition c_pop := 0
  with Definition c_ehd := 0 with Definition c_etl := 0 with Definition c_Lam := 0
  with Definition c_Kc := 0 with Definition c_consume := 0 with Definition c_etlc := 0 with Definition c_Ic := 0 with Definition c_compose := 0
  with Definition c_Cc := 0 with Definition c_Sc := 0
  with Definition c_case_bool := 0
  with Definition c_S := 1 with Definition c_case_nat := 0
  with Definition c_cons := 1 with Definition c_case_list := 0
  with Definition c_Some := 1 with Definition c_case_option := 0
  with Definition c_pair := 1 with Definition c_case_prod := 0
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 0
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 0
  (* an unfolding allocates a frame: the fixpoint rule needs [1 <= c_fix] *)
  with Definition c_fix := 1.
