(** * The space cost model

    The cost of a computation is the memory it allocates: the space
    counterpart of [TimeCostModel]. The layers of the time cost model are
    parametric in the cost of each primitive ([ParamTimeCostModel]); the
    space cost model is the same layers with the allocations of the
    primitives:
    - a closure ([c_clo]) and a constructor ([c_S], [c_cons], [c_Some],
      [c_pair], [c_ctor_Z]) allocate one cell;
    - the unfolding of a recursive function ([c_fix]) allocates one frame
      (the fixpoint rule needs [1 <= c_fix]: a recursion that allocates
      nothing could not be bounded);
    - an application ([c_step]) and a case analysis ([c_case_bool], ...)
      allocate nothing: they read memory.

    The space is the total allocation, without deallocation. The costs of
    the cost model are added along a computation ([CostModelCore.app]), so
    the peak of the memory in use, which would take a maximum, is not
    expressible.

    Each constant is at most its value in [TimeCostModel]: every allocation
    happens in a step, so the space of a computation is at most its time. *)

From Complexity Require Export TimeCostModel.

Module Type SpaceCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_step := 0 with Definition c_frame := 0
  with Definition c_case_bool := 0
  with Definition c_S := 1 with Definition c_case_nat := 0
  with Definition c_cons := 1 with Definition c_case_list := 0
  with Definition c_Some := 1 with Definition c_case_option := 0
  with Definition c_pair := 1 with Definition c_case_prod := 0
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 0
  with Definition c_fix := 1.
