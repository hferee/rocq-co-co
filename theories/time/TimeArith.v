(** * Arithmetic as primitive: a cost model counting operations

    [NatArithTimeCostModel] makes [Nat.add] and [Nat.mul] primitives, whose
    costs are given by constants: one for the partial application
    ([c_add_clo], [c_mul_clo]), the coefficients of a linear bound for
    [Nat.add] in its first argument [n] ([c_add_n * n + c_add]), and those
    of a bilinear bound for [Nat.mul] ([n * (c_mul_nm * m + c_mul_n) +
    c_mul]).

    [ParamArithTimeCostModel] is a signature with these primitives, the
    constructor [S], booleans and lists, but no case analysis on [nat]: the
    cost of a match on a number is unknown, and [cbc] fails on it. Functions
    on numbers are then analysed through [Nat.add] and [Nat.mul] only.

    [ArithOpsTimeCostModel] charges the arithmetic operations only: an
    addition costs [c_add], a multiplication [c_mul], an unfolding of a
    fixpoint [c_fix], and everything else is free. These three constants are
    abstract, so that the bounds are linear forms in them, whose
    coefficients are the numbers of additions, multiplications and
    unfoldings ([HornerCount]). Unfoldings cannot be free: free unfoldings
    would give every function every bound ([TimeFix], [UnguardedFix]); the
    analyses of recursive functions assume [1 <= c_fix].
    [ArithCountTimeCostModel] sets the three constants to [1]: the cost of a
    function is then its total number of operations. These models do not
    bound the running time: unit-cost multiplication computes [2 ^ 2 ^ n] in
    [n] steps, so that polynomial bounds in the sizes of the inputs lose
    their usual meaning.

    L is an instance of [ParamArithTimeCostModel], with the bounds of
    [Nat.add] and [Nat.mul] proved in [NatComplexity] as constants
    ([LArith]), but not of [ArithOpsTimeCostModel]: unary addition takes
    linear time. *)

From Complexity Require Export TimeDatatypes TimeFix.

Module Type NatArithTimeCostModel (Import CM : CostModel) (Import ND : NatData CM).

  Parameter c_add_clo c_add_n c_add : nat.
  Parameter c_mul_clo c_mul_nm c_mul_n c_mul : nat.
  #[global] Hint Unfold c_add_clo c_add_n c_add c_mul_clo c_mul_nm c_mul_n c_mul : costs.

  #[global] Declare Instance add_complexity : ComplexityBound Nat.add
    (fun cn => c_add_clo ⋉ fun cm => (c_add_n * val cn + c_add) ⋉ tt).

  #[global] Declare Instance mul_complexity : ComplexityBound Nat.mul
    (fun cn => c_mul_clo ⋉ fun cm => (val cn * (c_mul_nm * val cm + c_mul_n) + c_mul) ⋉ tt).
End NatArithTimeCostModel.

Module Type ParamArithTimeCostModel := CostModel.CostModel <+ BasicTimeCostModel
  <+ CombinatorTimeCostModel <+ BoolTimeCostModel
  <+ NatData <+ NatCtorTimeCostModel <+ NatArithTimeCostModel
  <+ ListTimeCostModel <+ FixTimeCostModel.

Module Type ArithOpsTimeCostModel := ParamArithTimeCostModel
  with Definition c_add_clo := 0 with Definition c_add_n := 0
  with Definition c_mul_clo := 0 with Definition c_mul_nm := 0 with Definition c_mul_n := 0
  with Definition c_clo := 0 with Definition c_step := 0
  with Definition c_case_bool := 0 with Definition c_S := 0
  with Definition c_cons := 0 with Definition c_case_list := 0.

Module Type ArithCountTimeCostModel := ArithOpsTimeCostModel
  with Definition c_add := 1 with Definition c_mul := 1 with Definition c_fix := 1.
