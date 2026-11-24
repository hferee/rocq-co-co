(** * Counting comparisons

    The comparison [cmp] of an abstract type [elt] is the only primitive
    charged, [c_cmp], abstract; an unfolding costs [1] ([c_fix], which
    cannot be [0], [FixCosts]). The coefficient of [c_cmp] in a bound counts
    the comparisons. *)

From Complexity Require Export TimeCostModel.

(** The abstract type and its comparison. *)
Module Type CmpElt (Import CM : CostModel) (Import BT : BasicCostModel CM)
  (Import ZD : ZData CM).
  Parameter elt : Type.
  #[global] Declare Instance Repr_elt : Repr elt unit.
  #[global] Declare Instance elt_complexity : forall x : elt, ComplexityBound x tt.

  Parameter cmp : elt -> elt -> comparison.
  Parameter c_cmp : Cost.
  #[global] Hint Unfold c_cmp : costs.
  #[global] Declare Instance cmp_complexity :
    ComplexityBound cmp (fun _ => c_clo +> fun _ => c_cmp >|).
End CmpElt.

Module Type ParamCmpTimeCostModel := ParamTimeCostModel <+ CmpElt.

(** Only comparisons and unfoldings are charged. *)
Module Type CmpOpsTimeCostModel := ParamCmpTimeCostModel
  with Definition c_clo := 0 with Definition c_frame := 0 with Definition c_pop := 0
  with Definition c_ehd := 0 with Definition c_etl := 0 with Definition c_Lam := 0
  with Definition c_Kc := 0 with Definition c_consume := 0 with Definition c_etlc := 0 with Definition c_Ic := 0 with Definition c_compose := 0
  with Definition c_Cc := 0 with Definition c_Sc := 0
  with Definition c_case_bool := 0
  with Definition c_S := 0 with Definition c_case_nat := 0
  with Definition c_cons := 0 with Definition c_case_list := 0
  with Definition c_Some := 0 with Definition c_case_option := 0
  with Definition c_pair := 0 with Definition c_case_prod := 0
  with Definition c_ctor_sum := 0 with Definition c_case_sum := 0
  with Definition c_ctor_Z := 0 with Definition c_case_Z := 0
  with Definition c_fix := 1.
