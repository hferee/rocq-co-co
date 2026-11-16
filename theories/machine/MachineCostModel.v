(** * The cost model of the environment machine for L

    The time cost model ([ParamTimeCostModel], and [ParamHOTimeCostModel]
    with lists and options of any data), with the constants of the
    environment machine for L ([LMachine], its instance), in steps of the
    machine:
    - [c_clo = 1]: a partial application allocates a closure;
    - a full application of a combinator: [c_ehd = 15] and [c_etl = 16] (the
      projections of an environment, a Scott-encoded pair, are the
      dearest), [c_Lam = 5], [c_Kc = 2], [c_Ic = 1], [c_compose = 8],
      [c_Cc = 8], [c_Sc = 10] (the reads of the variables of the
      combinator, its β-steps, and the closure of the environment for
      [Lam]);
    - [c_frame = 2]: an evaluation in non-tail position pushes and pops a
      frame; a tail call does not;
    - [c_case_bool = 25], [c_case_nat = 33], [c_case_list = 46],
      [c_case_option = c_case_sum = 35], [c_case_prod = 39],
      [c_case_Z = 43]: a case analysis, building the environment of its
      branch;
    - [c_S = c_cons = c_Some = c_pair = c_ctor_sum = c_ctor_Z = 1]: a constructor
      allocates a closure;
    - [c_fix = 36]: an unfolding (L has no recursion primitive: the
      function is rebuilt by self-application).
    The analyses over [MachineTimeCostModel] ([MachineExamples]) bound
    running times of this machine. *)

From Complexity Require Export TimeCostModel.

Module Type MachineTimeCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_frame := 2
  with Definition c_ehd := 15 with Definition c_etl := 16 with Definition c_Lam := 5
  with Definition c_Kc := 2 with Definition c_Ic := 1 with Definition c_compose := 8
  with Definition c_Cc := 8 with Definition c_Sc := 10
  with Definition c_case_bool := 25
  with Definition c_S := 1 with Definition c_case_nat := 33
  with Definition c_cons := 1 with Definition c_case_list := 46
  with Definition c_Some := 1 with Definition c_case_option := 35
  with Definition c_pair := 1 with Definition c_case_prod := 39
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 35
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 43
  with Definition c_fix := 36.

(** The same, with lists and options of any data. *)
Module Type MachineHOTimeCostModel := ParamHOTimeCostModel
  with Definition c_clo := 1 with Definition c_frame := 2
  with Definition c_ehd := 15 with Definition c_etl := 16 with Definition c_Lam := 5
  with Definition c_Kc := 2 with Definition c_Ic := 1 with Definition c_compose := 8
  with Definition c_Cc := 8 with Definition c_Sc := 10
  with Definition c_case_bool := 25
  with Definition c_S := 1 with Definition c_case_nat := 33
  with Definition c_cons := 1 with Definition c_case_list := 46
  with Definition c_Some := 1 with Definition c_case_option := 35
  with Definition c_pair := 1 with Definition c_case_prod := 39
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 35
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 43
  with Definition c_fix := 36.
