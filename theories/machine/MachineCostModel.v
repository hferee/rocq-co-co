(** * The cost model of the environment machine for L

    The time cost model ([ParamTimeCostModel], and [ParamHOTimeCostModel]
    with lists and options of any data), with the constants of the
    environment machine for L ([LMachine], its instance), in steps of the
    machine:
    - [c_clo = 1]: a partial application allocates a closure;
    - [c_step = 16]: a full application of a combinator (the projections of
      an environment, a Scott-encoded pair, are the dearest);
    - [c_frame = 2]: an evaluation in non-tail position pushes and pops a
      frame; a tail call does not;
    - [c_case_bool = 25], [c_case_nat = 33], [c_case_list = 46],
      [c_case_option = 35], [c_case_prod = 39], [c_case_Z = 43]: a case
      analysis, building the environment of its branch;
    - [c_S = c_cons = c_Some = c_pair = c_ctor_Z = 1]: a constructor
      allocates a closure;
    - [c_fix = 36]: an unfolding (L has no recursion primitive: the
      function is rebuilt by self-application).
    The analyses over [MachineTimeCostModel] ([MachineExamples]) bound
    running times of this machine. *)

From Complexity Require Export TimeCostModel.

Module Type MachineTimeCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_step := 16 with Definition c_frame := 2
  with Definition c_case_bool := 25
  with Definition c_S := 1 with Definition c_case_nat := 33
  with Definition c_cons := 1 with Definition c_case_list := 46
  with Definition c_Some := 1 with Definition c_case_option := 35
  with Definition c_pair := 1 with Definition c_case_prod := 39
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 43
  with Definition c_fix := 36.

(** The same, with lists and options of any data. *)
Module Type MachineHOTimeCostModel := ParamHOTimeCostModel
  with Definition c_clo := 1 with Definition c_step := 16 with Definition c_frame := 2
  with Definition c_case_bool := 25
  with Definition c_S := 1 with Definition c_case_nat := 33
  with Definition c_cons := 1 with Definition c_case_list := 46
  with Definition c_Some := 1 with Definition c_case_option := 35
  with Definition c_pair := 1 with Definition c_case_prod := 39
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 43
  with Definition c_fix := 36.
