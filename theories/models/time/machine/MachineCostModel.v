(** * The cost model of the environment machine for L

    The time cost model with the constants of the environment machine
    ([LMachine], its instance), in steps of the machine: the analyses over
    it ([MachineExamples]) bound running times of the machine. *)

From Complexity Require Export TimeCostModel.

Module Type MachineTimeCostModel := ParamTimeCostModel
  (* a partial application allocates a closure; an evaluation in non-tail
     position pushes and pops a frame *)
  with Definition c_clo := 1 with Definition c_frame := 2 with Definition c_pop := 0
  (* a combinator: the reads of its variables and its β-steps; those that
     project an environment, a Scott-encoded pair, are the dearest *)
  with Definition c_ehd := 15 with Definition c_etl := 16 with Definition c_Lam := 5
  with Definition c_Kc := 2 with Definition c_consume := 23 with Definition c_etlc := 21 with Definition c_Ic := 1 with Definition c_compose := 8
  with Definition c_Cc := 8 with Definition c_Sc := 10
  (* a case analysis builds the environment of its branch; a constructor
     allocates a closure *)
  with Definition c_case_bool := 25
  with Definition c_S := 1 with Definition c_case_nat := 33
  with Definition c_cons := 1 with Definition c_case_list := 46
  with Definition c_Some := 1 with Definition c_case_option := 35
  with Definition c_pair := 1 with Definition c_case_prod := 39
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 35
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 43
  (* L has no recursion primitive: the function is rebuilt by
     self-application *)
  with Definition c_fix := 36.

