(** * The space cost model

    The memory that a computation allocates: the layers of the time cost
    model, with the allocations of the primitives as costs. *)

From Complexity Require Export TimeCostModel.

(** The total allocation, without deallocation: costs are added along a
    computation ([CostModelCore.app]), so that the peak of the memory in
    use, a maximum, is not expressible. Each constant is at most its value
    in [TimeCostModel]: every allocation happens in a step, so the space of
    a computation is at most its time. *)
Module Type SpaceCostModel := ParamTimeCostModel
  (* a closure and a constructor allocate one cell; the combinators and the
     case analyses only read memory *)
  with Definition c_clo := 1 with Definition c_frame := 0
  with Definition c_ehd := 0 with Definition c_etl := 0 with Definition c_Lam := 0
  with Definition c_Kc := 0 with Definition c_Ic := 0 with Definition c_compose := 0
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
