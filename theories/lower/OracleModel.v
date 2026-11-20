(** * A cost model with oracles, for lower bounds

    The time cost model, with any constants, and an axiom with negative
    content: a functional with a bound treats its argument as an oracle.
    It generalises [comparison_trees] ([ComparisonModel]), which is specific
    to lists of elements compared at cost [1]. *)

From Complexity Require Export TimeCostModel Dialogues.

Module Type OracleAxiom (Import T : ParamTimeCostModel).
  (** The number of steps of a unit of cost. *)
  Parameter K : nat.

  (** A functional [F : (A -> B) -> C] of ground types with a bound is a
      dialogue tree ([Dialogues]), whose number of questions to an oracle
      [g] is at most [K] times the cost of [F g] when each question costs
      [1]. It is the quantitative form of the continuity of the definable
      functionals (Escardó's dialogue trees), and it is not about sorting:
      comparison-based algorithms are the functionals of their comparison
      ([SortingDialogue]). It is plausible because a function can only use
      an argument by applying it, which the model charges; [K] is the
      number of steps of a unit of cost ([8] in L, [1] on the machine). It
      has no instance in L, whose realisers only see the computable
      oracles: an instance would be a realisability model whose oracles are
      opaque, as in the relational models of parametricity. *)
  Parameter dialogues :
    forall {A CA B CB C CC} {RA : Repr A CA} {RB : Repr B CB} {RC : Repr C CC}
      {GA : IsGround RA} {GB : IsGround RB} {GC : IsGround RC}
      (F : (A -> B) -> C) (cF : ℂI (A -> B) (ℂI A CA -> ℂO CB) -> ℂO CC),
    ComplexityBound F cF ->
    exists d : dialogue A B C, forall g,
      deval d g = F g /\ queries d g <= K * cost (cF (g ⋊ (fun _ => 1 +> cdefault))).
End OracleAxiom.

Module Type OracleTimeCostModel := ParamTimeCostModel <+ OracleAxiom.

(** Only the questions, and the unfoldings, are counted, as when counting
    the comparisons of a sorting algorithm in a course; [c_fix] stays [1],
    which the fixpoint rule needs, and a question is a unit of cost. *)
Module Type OracleCountModel := OracleTimeCostModel
  with Definition c_clo := 0 with Definition c_frame := 0
  with Definition c_ehd := 0 with Definition c_etl := 0 with Definition c_Lam := 0
  with Definition c_Kc := 0 with Definition c_Ic := 0 with Definition c_compose := 0
  with Definition c_Cc := 0 with Definition c_Sc := 0
  with Definition c_case_bool := 0
  with Definition c_S := 0 with Definition c_case_nat := 0
  with Definition c_cons := 0 with Definition c_case_list := 0
  with Definition c_Some := 0 with Definition c_case_option := 0
  with Definition c_pair := 0 with Definition c_case_prod := 0
  with Definition c_ctor_sum := 0 with Definition c_case_sum := 0
  with Definition c_ctor_Z := 0 with Definition c_case_Z := 0
  with Definition c_fix := 1
  with Definition K := 1.
