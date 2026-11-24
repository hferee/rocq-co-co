(** * The time cost model

    The generic cost model ([Generic]) with costs in [nat]: the axioms of
    the time cost model, as one signature, over which the analyses are
    functors. *)

From Complexity Require Export Generic.

(** The generic cost model without lists, options and pairs ([ParamCostModelBase]),
    with costs in [nat]: time. *)
Module Type ParamTimeCostModelBase := ParamCostModelBase
  with Definition Cost := nat with Definition cle := le
  with Definition cnat := fun n : nat => n
  with Definition czero := 0 with Definition cplus := Nat.add.

(** The same, with the constants of [TimeCostModel]: the analyses that do not
    use lists, options or pairs ([BoolComplexity]) are functors over it. *)
Module Type TimeCostModelBase := ParamTimeCostModelBase
  with Definition c_clo := 1 with Definition c_frame := 0 with Definition c_pop := 0
  with Definition c_ehd := 1 with Definition c_etl := 1 with Definition c_Lam := 1
  with Definition c_Kc := 1 with Definition c_consume := 1 with Definition c_etlc := 1 with Definition c_Ic := 1 with Definition c_compose := 1
  with Definition c_Cc := 1 with Definition c_Sc := 1
  with Definition c_case_bool := 1
  with Definition c_S := 1 with Definition c_case_nat := 1
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 1
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 1
  with Definition c_fix := 1.

(** The generic cost model, with costs in [nat]. *)
Module Type ParamTimeCostModel := ParamCostModel
  with Definition Cost := nat with Definition cle := le
  with Definition cnat := fun n : nat => n
  with Definition czero := 0 with Definition cplus := Nat.add.

(** Every constant is [1]: each application is a β-step of L
    ([LInstance]). The analyses of the standard library are proved over
    this model. *)
Module Type TimeCostModel := ParamTimeCostModel
  with Definition c_clo := 1 with Definition c_frame := 0 with Definition c_pop := 0
  with Definition c_ehd := 1 with Definition c_etl := 1 with Definition c_Lam := 1
  with Definition c_Kc := 1 with Definition c_consume := 1 with Definition c_etlc := 1 with Definition c_Ic := 1 with Definition c_compose := 1
  with Definition c_Cc := 1 with Definition c_Sc := 1
  with Definition c_case_bool := 1
  with Definition c_S := 1 with Definition c_case_nat := 1
  with Definition c_cons := 1 with Definition c_case_list := 1
  with Definition c_Some := 1 with Definition c_case_option := 1
  with Definition c_pair := 1 with Definition c_case_prod := 1
  with Definition c_ctor_sum := 1 with Definition c_case_sum := 1
  with Definition c_ctor_Z := 1 with Definition c_case_Z := 1
  with Definition c_fix := 1.

