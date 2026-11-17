(** * Cost analysis of the ETH algorithm ([ETHAlgorithm])

    The functions are analysed as they are written in [ETHAlgorithm], by
    [cbound] ([TimeFix]): the compiler only replaces terms by
    convertible ones. The constants are the smallest ones
    for the shape of each bound (see [NatComplexity]). This file is the start
    of the analysis; the remarks at the end list what is covered. *)

From Complexity Require Export TimeStdlib ETHAlgorithm ETHData ETHFacts.
From Stdlib Require Import List ZArith QArith Qreduction Qround.
Import ListNotations.
Local Open Scope nat_scope.

(** No timeout for the tactics in the proofs of the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

Module ETHCost (Import Time : TimeStdlib).


  (** [memN x l]: recursive on its second argument. Each step compares with
      [Nat.eqb], whose cost is linear in [x] (unary numbers); [orb] evaluates
      both arguments. *)
  Global Instance memN_complexity : Time.ComplexityBound memN
    (fun cx => 1 +> fun cl =>
       (length (val cl) * (28 * val cx + 45) + 6) >|) := _.

  Global Instance countN_complexity : Time.ComplexityBound countN
    (fun cx => 1 +> fun cl =>
       (length (val cl) * (28 * val cx + 67) + 6) >|) := _.

  (** `eqbN a b`: recursive on its first argument, matches the second one. *)
  Global Instance eqbN_complexity : Time.ComplexityBound eqbN
    (fun ca => 4 +> fun cb =>
       (28 * list_sum (val ca) + 67 * length (val ca) + 8) >|) := _.

  (** [insert_uniq x l]: the recursive call only happens in the last
      branch; its other branches return [l] itself. *)
  Global Instance insert_uniq_complexity : Time.ComplexityBound insert_uniq
    (fun cx => 1 +> fun cl =>
       (length (val cl) * (56 * val cx + 105) + 12) >|) := _.

  (** [range n = seq 0 n]: not recursive, it follows from [seq]. *)
  Global Instance range_complexity : Time.ComplexityBound range
    (fun cn => (33 * val cn + 4) >|) := _.

  (** [fold_left Nat.add]: the cost of each addition is linear in the
      accumulator, so the bound depends on the values. *)
  Global Instance fold_left_add_complexity : Time.ComplexityBound (fold_left Nat.add)
    (fun cl => 4 +> fun ca =>
       (length (val cl) * (14 * (val ca + list_sum (val cl)) + 42) + 6) >|) := _.

  Global Instance sumN_complexity : Time.ComplexityBound sumN
    (fun cl =>
       (length (val cl) * (14 * list_sum (val cl) + 42) + 13) >|) := _.
  (** [indexN x l]: as [memN], it stops at the first occurrence. *)
  Global Instance indexN_complexity : Time.ComplexityBound indexN
    (fun cx => 1 +> fun cl => (length (val cl) * (28 * val cx + 41) + 6) >|) := _.

  (** [lexltbN a b]: each step compares the heads twice ([<?], [=?]),
      whose costs are linear in the head of [a]. *)
  Global Instance lexltbN_complexity : Time.ComplexityBound lexltbN
    (fun ca => 4 +> fun cb => (56 * list_sum (val ca) + 132 * length (val ca) + 8) >|) := _.

  (** [fold_left Nat.max]: the cost of [Nat.max acc x] is linear in the
      accumulator, at most its initial value plus the elements. *)
  Global Instance fold_left_max_complexity : Time.ComplexityBound (fold_left Nat.max)
    (fun cl => 4 +> fun ca =>
       (length (val cl) * (30 * (val ca + list_sum (val cl)) + 41) + 6) >|) := _.

  Global Instance maxN_complexity : Time.ComplexityBound maxN
    (fun cl => (length (val cl) * (30 * list_sum (val cl) + 41) + 13) >|) := _.

  (** [set_nth] and [remove_nth] recurse on the list and the index, and
      stop at the index. *)
  Global Instance set_nth_complexity {A} `{Ground A} : Time.ComplexityBound (@set_nth A)
    (fun cl => 4 +> fun ci => 2 +> fun cx => (57 * val ci + 25) >|) := _.
  Global Instance remove_nth_complexity {A} `{Ground A} : Time.ComplexityBound (@remove_nth A)
    (fun cl => 4 +> fun ci => (41 * val ci + 12) >|) := _.

  (** [chunks size count l]: [count] times [firstn size] and [skipn size]. *)
  Global Instance chunks_complexity {A} `{Ground A} : Time.ComplexityBound (@chunks A)
    (fun cs => 1 +> fun cn => 4 +> fun cl => (val cn * (71 * val cs + 67) + 6) >|) := _.

  (** The rounded divisions, logarithms and roots. *)
  Global Instance ceil_div_complexity : Time.ComplexityBound ceil_div
    (fun ca => 1 +> fun cb => (100 * val ca + 86 * val cb + 77) >|) := _.
  Global Instance clog2_complexity : Time.ComplexityBound clog2
    (fun cn => (116 * val cn + 63) >|) := _.
  Global Instance csqrt_complexity : Time.ComplexityBound csqrt
    (fun cn => (136 * val cn + 64) >|).
  Proof.
    cbound.
    all: pose proof (Nat.sqrt_le_lin cn); pose proof (Nat.sqrt_spec cn ltac:(lia)) as [Hs _];
         try unfold Nat.square in Hs; try rewrite Nat.pow_2_r in Hs; lia.
  Qed.

  (** [subsetN a b]: [memN x b] for each element [x] of [a] ([forallb], on
      the closure of [b]). [cbound] leaves the sum of the costs of the
      elements, distributed by [simpl_list_sum]. *)
  Global Instance subsetN_complexity : Time.ComplexityBound subsetN
    (fun ca => 1 +> fun cb =>
       (length (val cb) * (28 * list_sum (val ca) + 45 * length (val ca)) + 46 * length (val ca) + 12) >|).
  Proof. cbound. simpl_list_sum. nia. Qed.

  (** Each insertion costs at most the length of the original list
      ([length_sort_uniq], [ETHFacts]). *)
  Global Instance fold_right_insert_uniq_complexity : Time.ComplexityBound (fold_right insert_uniq [])
    (fun cl => (length (val cl) * (56 * list_sum (val cl) + 105 * length (val cl)) + 6) >|).
  Proof.
    cbound. match goal with |- context [length (fold_right insert_uniq [] ?l)] => pose proof (length_sort_uniq l) end.
    nia.
  Qed.

  Global Instance sort_uniq_complexity : Time.ComplexityBound sort_uniq
    (fun cl => (length (val cl) * (56 * list_sum (val cl) + 105 * length (val cl)) + 6) >|) := _.

  (** ** Formulas *)

  (** The codes of the literals: [Nat.div2], [Nat.odd]. *)
  Global Instance code_var_complexity : Time.ComplexityBound code_var
    (fun cc => (9 * val cc + 9) >|) := _.
  Global Instance code_pos_complexity : Time.ComplexityBound code_pos
    (fun cc => (8 * val cc + 15) >|) := _.
  Global Instance code_neg_complexity : Time.ComplexityBound code_neg
    (fun cc => (36 * val cc + 33) >|) := _.

  (** [nclause_eval x C]: for each code [c] of [C], [nth (code_var c) x],
      whose cost is linear in [code_var c <= c / 2]. *)
  Global Instance nclause_eval_complexity : Time.ComplexityBound nclause_eval
    (fun cx => 1 +> fun cC => (41 * list_sum (val cC) + 96 * length (val cC) + 12) >|).
  Proof.
    cbound. simpl_list_sum.
    pose proof (list_sum_map_le (fun x => 2 * code_var x) (fun x => x) cC (fun x _ => code_var_le x)).
    simpl_list_sum. lia.
  Qed.

  (** [ncnf_eval x F]: the sum over the clauses, in the sums of their codes
      and in their lengths. *)
  Global Instance ncnf_eval_complexity : Time.ComplexityBound ncnf_eval
    (fun cx => 1 +> fun cF =>
       (41 * list_sum (map list_sum (val cF)) + 96 * list_sum (map (@length nat) (val cF))
        + 44 * length (val cF) + 14) >|).
  Proof. cbound. simpl_list_sum. lia. Qed.

  (** [tautological C]: [memN (code_neg c) C] for each code [c] of [C]. *)
  Global Instance tautological_complexity : Time.ComplexityBound tautological
    (fun cC => (length (val cC) * (28 * list_sum (val cC) + 73 * length (val cC))
                + 36 * list_sum (val cC) + 78 * length (val cC) + 11) >|).
  Proof.
    cbound. simpl_list_sum.
    pose proof (list_sum_map_le_affine code_neg 1 1 cC (fun x _ => ltac:(pose proof (code_neg_le x); lia))).
    nia.
  Qed.

  (** [insert_clause C F] compares [C] with the clauses of [F]
      ([lexltbN], [eqbN]); [sort_clauses] inserts each clause, as
      [sort_uniq]. *)
  Global Instance insert_clause_complexity : Time.ComplexityBound insert_clause
    (fun cC => 1 +> fun cF =>
       (length (val cF) * (84 * list_sum (val cC) + 199 * length (val cC) + 71) + 12) >|) := _.

  (** The products of the length of the sorted clauses by the measures of
      the clause inserted, which [nia] does not find. *)
  Global Instance fold_right_insert_clause_complexity : Time.ComplexityBound (fold_right insert_clause [])
    (fun cF =>
       (length (val cF) * (84 * list_sum (map list_sum (val cF)) + 199 * list_sum (map (@length nat) (val cF))
                           + 36 * length (val cF)) + 6) >|).
  Proof.
    cbound.
    match goal with |- context [length (fold_right insert_clause [] ?l)] => pose proof (length_sort_clauses l) as Hl end.
    match goal with |- context [list_sum ?C] => is_var C;
      pose proof (Nat.mul_le_mono_r _ _ (list_sum C) Hl); pose proof (Nat.mul_le_mono_r _ _ (length C) Hl) end.
    cnorm_types. lia.
  Qed.

  Global Instance sort_clauses_complexity : Time.ComplexityBound sort_clauses
    (fun cF =>
       (length (val cF) * (84 * list_sum (map list_sum (val cF)) + 199 * list_sum (map (@length nat) (val cF))
                           + 36 * length (val cF)) + 6) >|) := _.

  Global Instance strict_subset_complexity : Time.ComplexityBound strict_subset
    (fun ca => 1 +> fun cb =>
       (length (val ca) * (28 * list_sum (val cb) + 90 * length (val cb) + 46)
        + length (val cb) * (28 * list_sum (val ca) + 46) + 46) >|) := _.

  (** [has_empty_clause F]: the test of each clause is a [match] on it,
      which [cbound] leaves in the sum: its cost is at most [8]. *)
  Global Instance has_empty_clause_complexity : Time.ComplexityBound has_empty_clause
    (fun cF => (40 * length (val cF) + 6) >|).
  Proof.
    cbound. match goal with |- context [list_sum (map ?f ?l)] =>
      pose proof (list_sum_map_le_const f 8 l (fun x _ => ltac:(destruct x; cbn; lia))) end.
    lia.
  Qed.

  (** [max_width F]: [maxN] on the lengths of the clauses. *)
  Global Instance max_width_complexity : Time.ComplexityBound max_width
    (fun cF => (length (val cF) * (30 * list_sum (map (@length nat) (val cF)) + 76)
                + 16 * list_sum (map (@length nat) (val cF)) + 22) >|).
  Proof. cbound. simpl_list_sum. cnorm_types. nia. Qed.

  (** The bounds in the sizes of the arguments: polynomial. *)
  Global Instance indexN_polynomial_bound : Time.PolynomialBound indexN := _.
  Global Instance lexltbN_polynomial_bound : Time.PolynomialBound lexltbN := _.
  Global Instance maxN_polynomial_bound : Time.PolynomialBound maxN := _.
  Global Instance set_nth_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@set_nth A) := _.
  Global Instance remove_nth_linear_bound {A} `{Ground A} `{Size A} : Time.LinearBound (@remove_nth A) := _.
  Global Instance chunks_polynomial_bound {A} `{Ground A} `{Size A} : Time.PolynomialBound (@chunks A) := _.
  Global Instance ceil_div_linear_bound : Time.LinearBound ceil_div := _.
  Global Instance clog2_linear_bound : Time.LinearBound clog2 := _.
  Global Instance csqrt_linear_bound : Time.LinearBound csqrt := _.
  Global Instance subsetN_polynomial_bound : Time.PolynomialBound subsetN := _.
  Global Instance insert_uniq_polynomial_bound : Time.PolynomialBound insert_uniq := _.
  Global Instance sort_uniq_polynomial_bound : Time.PolynomialBound sort_uniq := _.
  Global Instance code_var_linear_bound : Time.LinearBound code_var := _.
  Global Instance code_pos_linear_bound : Time.LinearBound code_pos := _.
  Global Instance code_neg_linear_bound : Time.LinearBound code_neg := _.
  Global Instance nclause_eval_polynomial_bound : Time.PolynomialBound nclause_eval := _.
  Global Instance ncnf_eval_polynomial_bound : Time.PolynomialBound ncnf_eval := _.
  Global Instance tautological_polynomial_bound : Time.PolynomialBound tautological := _.
  Global Instance insert_clause_polynomial_bound : Time.PolynomialBound insert_clause := _.
  Global Instance sort_clauses_polynomial_bound : Time.PolynomialBound sort_clauses := _.
  Global Instance strict_subset_polynomial_bound : Time.PolynomialBound strict_subset := _.
  Global Instance has_empty_clause_linear_bound : Time.LinearBound has_empty_clause := _.
  Global Instance max_width_polynomial_bound : Time.PolynomialBound max_width := _.

  (** ** Bounds in the sizes of the arguments, with their constants

      The bounds above are in the values and lengths of the arguments;
      each of these is at most the size ([#|x|], [SizeFact]), so that
      they give bounds in the sizes ([csize]). *)

  Lemma memN_size_complexity :
    Time.ComplexityBound memN
      (fun (cx : ℂI nat _) => 1 +> fun (cl : ℂI (list nat) _) => (#|val cl| * (28 * #|val cx| + 17) + 0) >|).
  Proof. csize_using memN_complexity. Qed.

  Lemma countN_size_complexity :
    Time.ComplexityBound countN
      (fun (cx : ℂI nat _) => 1 +> fun (cl : ℂI (list nat) _) => (#|val cl| * (28 * #|val cx| + 39) + 0) >|).
  Proof. csize_using countN_complexity. Qed.

  Lemma eqbN_size_complexity :
    Time.ComplexityBound eqbN
      (fun (ca : ℂI (list nat) _) => 4 +> fun cb => (2 * #|val ca| + 65 * #|val ca| + 0) >|).
  Proof. csize_using eqbN_complexity. Qed.

  Lemma insert_uniq_size_complexity :
    Time.ComplexityBound insert_uniq
      (fun (cx : ℂI nat _) => 1 +> fun (cl : ℂI (list nat) _) => (#|val cl| * (56 * #|val cx| + 49) + 0) >|).
  Proof. csize_using insert_uniq_complexity. Qed.

  Lemma range_size_complexity :
    Time.ComplexityBound range
      (fun (cn : ℂI nat _) => (33 * #|val cn| + 0) >|).
  Proof. csize_using range_complexity. Qed.

  Lemma fold_left_add_size_complexity :
    Time.ComplexityBound (fold_left Nat.add)
      (fun (cl : ℂI (list nat) _) => 4 +> fun (ca : ℂI nat _) => (#|val cl| * (14 * (#|val ca| + #|val cl|) + 0) + 0) >|).
  Proof. csize_using fold_left_add_complexity. Qed.

  Lemma sumN_size_complexity :
    Time.ComplexityBound sumN
      (fun (cl : ℂI (list nat) _) => (#|val cl| * (7 * #|val cl| + 28) + 0) >|).
  Proof. csize_using sumN_complexity. Qed.

End ETHCost.

(** ** The functions on the data types of the algorithm

    With the axioms of these types ([ETHData]): for now, the literals. *)
Module ETHDataCost (Import Time : TimeStdlib) (Import D : ETHData Time).
  Include ETHCost Time.

  (** *** Sizes: a literal is larger than its variable, a clause than the
      sum of its variables and its length. *)
  Lemma lvar_lt_size l : lvar l < size l.
  Proof. destruct l as [v p]. rewrite size_mkLit. cbn. pose proof (nat_lt_size v). lia. Qed.
  Global Instance literal_size_fact (l : literal) : SizeFact l (lvar l < size l) := lvar_lt_size l.
  Lemma clause_lt_size (C : list literal) : list_sum (map lvar C) + length C < size C.
  Proof.
    induction C as [|l C IH]; [rewrite size_nil; cbn; lia|].
    cbn [map length]. change (list_sum (?x :: ?m)) with (x + list_sum m).
    pose proof (lvar_lt_size l). pose proof (size_cons l C). lia.
  Qed.
  Global Instance clause_size_fact (C : list literal) :
    SizeFact C (list_sum (map lvar C) + length C < size C) | 1 := clause_lt_size C.
  (** *** Bounds *)
  Global Instance lvar_complexity : Time.ComplexityBound lvar (fun cl => 5 >|) := _.
  Global Instance lpos_complexity : Time.ComplexityBound lpos (fun cl => 3 >|) := _.
  Global Instance lvar_constant_bound : Time.ConstantBound lvar := _.
  Global Instance lpos_constant_bound : Time.ConstantBound lpos := _.
  Global Instance lit_code_complexity : Time.ComplexityBound lit_code
    (fun cl => (56 * lvar (val cl) + 96) >|) := _.
  Global Instance lit_code_linear_bound : Time.LinearBound lit_code := _.
  (** [norm_clause C] sorts the codes of the literals of [C], at most
      [2 * lvar l + 1] each ([lit_code_le]). *)
  Global Instance norm_clause_complexity : Time.ComplexityBound norm_clause
    (fun cC => (length (val cC) * (112 * list_sum (map lvar (val cC)) + 161 * length (val cC))
                + 56 * list_sum (map lvar (val cC)) + 125 * length (val cC) + 15) >|).
  Proof.
    cbound. simpl_list_sum.
    pose proof (list_sum_map_le lit_code (fun l => S (2 * lvar l)) cC
                  (fun l _ => ltac:(cbv beta; pose proof (lit_code_le l); lia))) as H.
    simpl_list_sum. pose proof (Nat.mul_le_mono_l _ _ (length cC) H).
    cnorm_types. lia.
  Qed.
  Global Instance norm_clause_polynomial_bound : Time.PolynomialBound norm_clause := _.
End ETHDataCost.

(** * Coverage of [ETHAlgorithm] by the current models

    With the generic fixpoint axiom ([TimeFix]), every structurally
    recursive function can be analysed as written, whatever its number of
    arguments, the position of its recursive argument, the matches of its
    body (also on other arguments), the depth of its recursive calls, and
    its type arguments; mutual recursion goes through an indexed function
    (see [Pos.add] in [PosComplexity]). This covers in particular the
    functions that were out of reach of the former recursors: polymorphic
    fixpoints ([fold_tuples], [find_tuple], [fold_sublists], [zipWith],
    [set_nth], ...), fixpoints with more than two arguments
    ([spar_M_search], [sparsify_fold], [rv_mul_aux], [Nat.div] through
    [divmod], ...), toplevel matches on other arguments ([nth],
    [combinations]), and deeper recursive calls ([Nat.even], [Nat.div2]).

    Still missing in the model:

    - Local fixpoints (the [go] of [lifted_factor]) are not analysed: their
      bounds are declared first, for the function of the variables they
      use ([Examples]).
    - The data types of the algorithm ([params], [design], [literal],
      [pair_eig]) come with their own axioms: representation, sizes,
      constructors, case analyses ([ETHData]: all of them for [literal],
      the first two for the others).

    Not a matter of expressiveness, but of proofs about the values computed
    (the paper's appendices): the bit sizes of the rationals manipulated by
    the counting routine, the size of the sparsification tree, and the
    parameter checks of [choose_params] for large inputs. *)

(** ** Plan: the bounds that lead to [count_sat]

    The statements below, in the order of [ETHAlgorithm], are the bounds to
    prove to reach the main function [count_sat]; each ends with [Abort].
    Their forms:
    - [Time.PolynomialBound f]: a polynomial in the sizes of the arguments
      (unary for [nat]: in their values);
    - [exists c, Time.ComplexityBound f ...]: an explicit shape, for the
      functions whose cost is exponential in some arguments (powers of
      numbers, enumerations), with the factor read from the definition;
    - for the higher-order functions: their bound from that of their
      function argument, closed under polynomials, or, for the enumerations,
      the number of the elements enumerated times a bound [g] on the cost of
      the argument (and a bound on the growth of the accumulator);
    - for the top layers ([count_zeros], [count_sparse_formula],
      [count_sat]): the shape claimed by the paper,
      [(n+m)^O(1) 2^O(rho n)], with constants depending on the width or the
      sparsity.
    The bounds of [memN], [countN], [eqbN], [insert_uniq], [range],
    [sumN], [indexN], [lexltbN], [maxN], [set_nth], [remove_nth],
    [chunks], [ceil_div], [clog2], [csqrt], [subsetN], [sort_uniq] and of
    the functions on formulas [code_var], [code_pos], [code_neg],
    [nclause_eval], [ncnf_eval], [tautological], [insert_clause],
    [sort_clauses], [strict_subset], [has_empty_clause] and [max_width]
    are proved above ([ETHCost]), and those of the functions on literals
    [lvar], [lpos], [lit_code] and [norm_clause] with the axioms of
    [literal] ([ETHDataCost]).

    Prerequisites (not yet in the library):
    - the axioms of the data types of the algorithm, which come with the
      algorithm ([ETHData]): those of [literal] are there; [params],
      [design] (records) and [pair_eig] have their representations and
      sizes, their constructors and case analyses are still to be
      axiomatised, as for [literal];
    - bounds of functions of the standard library (section 0 below: the
      remaining ones);
    - higher-order functions on ground lists: [map], [filter], [existsb],
      [forallb] and [flat_map] have bounds in the costs of their function
      ([ListComplexity]), which [subsetN], [tautological], ... use; the
      folds with a function that is a closure ([zipWith], [embed], ...)
      do not ([fold_left_hcomplexity] is not closed, and [fold_right] has
      no such bound yet: [sort_uniq] and [sort_clauses] analyse it with
      their function fixed).
    The subexponential bounds of the top layers also need the facts of the
    paper on the parameters: the numerical checks of [choose_params] pass
    for large [n] (otherwise the counts fall back to exhaustive search). *)

(** The exponent of the paper: rho(n) = n (log log n)^2 / sqrt (log n). *)
Definition rho (n : nat) : nat := n * Nat.log2 (Nat.log2 n) ^ 2 / S (Nat.sqrt (Nat.log2 n)).

Module ETHPlan (Import Time : TimeStdlib) (Import D : ETHData Time).

  (** *** 0. The standard library

      Proved in the library: [Nat.pred], [max], [min], [div2], [even],
      [odd], [log2], [sqrt], [div], [modulo], [testbit] ([NatComplexity]);
      [firstn], [skipn], [nth], [repeat], [hd], [rev], [concat] (in the
      length of the result), [combine] ([ListComplexity]). *)
  Lemma Nat_land_polynomial : Time.PolynomialBound Nat.land. Abort.
  Lemma Nat_lxor_polynomial : Time.PolynomialBound Nat.lxor. Abort.
  (** [Nat.pow] is exponential in its second argument (unary numbers). *)
  Lemma Nat_pow_exponential : exists c, Time.ComplexityBound Nat.pow
    (fun cn => c +> fun cm => (c * S (val cn) ^ (S (val cm))) >|). Abort.

  Lemma Qred_polynomial : Time.PolynomialBound Qred. Abort.
  Lemma Qplus_polynomial : Time.PolynomialBound Qplus. Abort.
  Lemma Qminus_polynomial : Time.PolynomialBound Qminus. Abort.
  Lemma Qmult_polynomial : Time.PolynomialBound Qmult. Abort.
  Lemma Qinv_polynomial : Time.PolynomialBound Qinv. Abort.
  Lemma Qdiv_polynomial : Time.PolynomialBound Qdiv. Abort.
  Lemma Qopp_polynomial : Time.PolynomialBound Qopp. Abort.
  Lemma Qeq_bool_polynomial : Time.PolynomialBound Qeq_bool. Abort.
  Lemma Qle_bool_polynomial : Time.PolynomialBound Qle_bool. Abort.
  Lemma inject_Z_polynomial : Time.PolynomialBound inject_Z. Abort.
  Lemma Qfloor_polynomial : Time.PolynomialBound Qfloor. Abort.

  (** The bounds of [map], [filter], [existsb], [forallb] and [flat_map]
      in the costs of their function, a closure, are in [ListComplexity];
      the statements below are their closures under polynomials. *)
  Section Lists.
    Context {A B : Type} `{Ground A} `{Size A} `{Ground B} `{Size B}.
    Lemma concat_polynomial : Time.PolynomialBound (@concat A). Abort.
    Lemma list_prod_polynomial : Time.PolynomialBound (@list_prod A B). Abort.
    Lemma map_polynomial (f : A -> B) : Time.PolynomialBound f -> Time.PolynomialBound (map f). Abort.
    Lemma flat_map_polynomial (f : A -> list B) :
      Time.PolynomialBound f -> Time.PolynomialBound (flat_map f). Abort.
    Lemma filter_polynomial (f : A -> bool) : Time.PolynomialBound f -> Time.PolynomialBound (filter f). Abort.
    Lemma forallb_polynomial (f : A -> bool) : Time.PolynomialBound f -> Time.PolynomialBound (forallb f). Abort.
    Lemma existsb_polynomial (f : A -> bool) : Time.PolynomialBound f -> Time.PolynomialBound (existsb f). Abort.
    (** The folds: polynomial when the accumulator grows at most additively. *)
    Lemma fold_left_polynomial (f : B -> A -> B) (d : nat) :
      Time.PolynomialBound f -> (forall b a, #|f b a| <= #|b| + #|a| + d) ->
      Time.PolynomialBound (fold_left f). Abort.
    Lemma fold_right_polynomial (f : A -> B -> B) (d : nat) :
      Time.PolynomialBound f -> (forall a b, #|f a b| <= #|a| + #|b| + d) ->
      Time.PolynomialBound (fold_right f). Abort.
    Lemma Nat_iter_polynomial (f : A -> A) (d : nat) :
      Time.PolynomialBound f -> (forall a, #|f a| <= #|a| + d) ->
      Time.PolynomialBound (fun n => Nat.iter n f). Abort.
  End Lists.

  (** *** 1. Generic utilities *)

  Lemma sumZ_polynomial : Time.PolynomialBound sumZ. Abort.
  Lemma zipWith_polynomial {A B C} `{Ground A} `{Size A} `{Ground B} `{Size B} `{Ground C}
    (f : A -> B -> C) : Time.PolynomialBound f -> Time.PolynomialBound (zipWith f). Abort.
  Lemma zinterval_polynomial : Time.PolynomialBound zinterval. Abort.

  (** The enumerations: [|alphabet| ^ len] tuples (and subsets of [l] of
      size [k], all subsets of [l]), each with one application of [f]; the
      accumulator grows by at most [d] at each one. *)
  Lemma fold_tuples_complexity {A B} `{Ground A} `{Size A} `{Ground B} `{Size B}
    (f : B -> list A -> B) (cf : ℂI B unit -> ℂO (ℂI (list A) unit -> ℂO unit)) (g : nat -> nat) (d : nat) :
    Time.ComplexityBound f cf ->
    (forall a t, cost (cf (a ⋊ tt)) + cost (res (cf (a ⋊ tt)) (t ⋊ tt)) <= g (#|a| + #|t|)) ->
    (forall a t, #|f a t| <= #|a| + d) -> (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun len alphabet acc prefix => fold_tuples len alphabet f acc prefix)
      (fun (cn : ℂI nat unit) => c +> fun (ca : ℂI (list A) unit) => c +> fun (cacc : ℂI B unit) => c +>
       fun (cp : ℂI (list A) unit) =>
         (S (length (val ca)) ^ val cn *
            (g (#|val cacc| + d * S (length (val ca)) ^ val cn + c * S (val cn + #|val ca| + #|val cp|) ^ c)
             + c * S (val cn + #|val ca| + #|val cp|) ^ c)) >|). Abort.

  Lemma find_first_polynomial {A B} `{Ground A} `{Size A} `{Ground B} (f : A -> option B) :
    Time.PolynomialBound f -> Time.PolynomialBound (find_first f). Abort.

  Lemma find_tuple_complexity {A} `{Ground A} `{Size A}
    (p : list A -> bool) (cp : ℂI (list A) unit -> ℂO unit) (g : nat -> nat) :
    Time.ComplexityBound p cp -> (forall t, cost (cp (t ⋊ tt)) <= g #|t|) ->
    (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun len alphabet prefix => find_tuple len alphabet p prefix)
      (fun (cn : ℂI nat unit) => c +> fun (ca : ℂI (list A) unit) => c +> fun (cpr : ℂI (list A) unit) =>
         (S (length (val ca)) ^ val cn *
            (g (c * S (val cn + #|val ca| + #|val cpr|) ^ c) + c * S (val cn + #|val ca| + #|val cpr|) ^ c)) >|).
  Abort.

  Lemma combinations_complexity : exists c, Time.ComplexityBound combinations
    (fun (cl : ℂI (list nat) unit) => c +> fun (ck : ℂI (nat) unit) => (S (length (val cl)) ^ val ck * c * S (#|val cl| + val ck) ^ c) >|). Abort.

  Lemma fold_combinations_complexity {B} `{Ground B} `{Size B}
    (f : B -> list nat -> B) (cf : ℂI B unit -> ℂO (ℂI (list nat) unit -> ℂO unit)) (g : nat -> nat) (d : nat) :
    Time.ComplexityBound f cf ->
    (forall a t, cost (cf (a ⋊ tt)) + cost (res (cf (a ⋊ tt)) (t ⋊ tt)) <= g (#|a| + #|t|)) ->
    (forall a t, #|f a t| <= #|a| + d) -> (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun l k acc prefix => fold_combinations l k f acc prefix)
      (fun (cl : ℂI (list nat) unit) => c +> fun (ck : ℂI nat unit) => c +> fun (cacc : ℂI B unit) => c +>
       fun (cp : ℂI (list nat) unit) =>
         (S (length (val cl)) ^ val ck *
            (g (#|val cacc| + d * S (length (val cl)) ^ val ck + c * S (#|val cl| + val ck + #|val cp|) ^ c)
             + c * S (#|val cl| + val ck + #|val cp|) ^ c)) >|). Abort.

  Lemma fold_sublists_complexity {B} `{Ground B} `{Size B}
    (f : B -> list nat -> B) (cf : ℂI B unit -> ℂO (ℂI (list nat) unit -> ℂO unit)) (g : nat -> nat) (d : nat) :
    Time.ComplexityBound f cf ->
    (forall a t, cost (cf (a ⋊ tt)) + cost (res (cf (a ⋊ tt)) (t ⋊ tt)) <= g (#|a| + #|t|)) ->
    (forall a t, #|f a t| <= #|a| + d) -> (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun l acc prefix => fold_sublists l f acc prefix)
      (fun (cl : ℂI (list nat) unit) => c +> fun (cacc : ℂI B unit) => c +> fun (cp : ℂI (list nat) unit) =>
         (2 ^ length (val cl) *
            (g (#|val cacc| + d * 2 ^ length (val cl) + c * S (#|val cl| + #|val cp|) ^ c)
             + c * S (#|val cl| + #|val cp|) ^ c)) >|). Abort.

  Lemma embed_polynomial : Time.PolynomialBound embed. Abort.

  (** *** 2. Formulas *)

  (** The [2 ^ n] assignments. *)
  Lemma count_bruteforce_complexity : exists c, Time.ComplexityBound count_bruteforce
    (fun (cn : ℂI (nat) unit) => c +> fun (cF : ℂI (ncnf) unit) => (2 ^ val cn * c * S (val cn + #|val cF|) ^ c) >|). Abort.
  Lemma antichain_polynomial : Time.PolynomialBound antichain. Abort.
  Lemma normalize_polynomial : Time.PolynomialBound normalize. Abort.

  (** *** 3. Disjoint sparsification *)

  (** Unary powers of the arguments. *)
  Lemma spar_Gamma_complexity : exists c, Time.ComplexityBound spar_Gamma
    (fun (ck : ℂI (nat) unit) => (3 ^ val ck * c * S (val ck) ^ c) >|). Abort.
  Lemma spar_C_complexity : exists c, Time.ComplexityBound spar_C
    (fun (ck : ℂI (nat) unit) => c +> fun (cM : ℂI (nat) unit) => (c * S (val ck + 3 * val cM) ^ (c * S (val ck))) >|). Abort.
  Lemma spar_B_complexity : exists c, Time.ComplexityBound spar_B
    (fun (ck : ℂI (nat) unit) => c +> fun (cM : ℂI (nat) unit) => (c * S (val ck + val cM) ^ (c * S (val ck))) >|). Abort.
  (** [M] doubles at most [fuel] times. *)
  Lemma spar_M_search_complexity : exists c, Time.ComplexityBound spar_M_search
    (fun (cf : ℂI (nat) unit) => c +> fun (ck : ℂI (nat) unit) => c +> fun (cs : ℂI (nat) unit) => c +> fun (cM : ℂI (nat) unit) =>
       (c * S (val cf + val ck + val cs + 2 ^ val cf * val cM + 3 ^ val ck) ^ (c * S (val ck))) >|). Abort.
  Lemma spar_M_complexity : exists c, Time.ComplexityBound spar_M
    (fun (ck : ℂI (nat) unit) => c +> fun (cs : ℂI (nat) unit) => (c * 2 ^ (c * S (val ck) * (val cs + 3 ^ val ck))) >|). Abort.
  Lemma deg_c_polynomial : Time.PolynomialBound deg_c. Abort.
  (** The subsets of the clauses of width at most [k], and [M ^ k]. *)
  Lemma find_branch_complexity : exists c, Time.ComplexityBound find_branch
    (fun (ck : ℂI (nat) unit) => c +> fun (cM : ℂI (nat) unit) => c +> fun (cF : ℂI (ncnf) unit) =>
       (c * S (val ck + val cM + #|val cF|) ^ (c * S (val ck))) >|). Abort.
  Lemma branch_children_polynomial : Time.PolynomialBound branch_children. Abort.
  (** The sparsification tree has at most [2 ^ fuel] nodes, whose formulas
      are of size polynomial in that of [F] and in [fuel] (to check); the
      leaves cost what [leaf] and [fallback] cost. *)
  Lemma sparsify_fold_complexity (k M : nat) (leaf fallback : ncnf -> Z)
    (cl cb : ℂI ncnf unit -> ℂO unit) (g : nat -> nat) :
    Time.ComplexityBound leaf cl -> Time.ComplexityBound fallback cb ->
    (forall F, cost (cl (F ⋊ tt)) <= g #|F| /\ cost (cb (F ⋊ tt)) <= g #|F|) ->
    (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun fuel F => sparsify_fold fuel k M leaf fallback F)
      (fun (cfuel : ℂI nat unit) => c +> fun (cF : ℂI ncnf unit) =>
         (2 ^ val cfuel *
            (g (c * S (#|val cF| + val cfuel) ^ c)
             + c * S (#|val cF| + val cfuel + M + k) ^ (c * S k))) >|). Abort.

  (** *** 4. Polynomials over F_2 *)

  Lemma insert_mono_polynomial : Time.PolynomialBound insert_mono. Abort.
  Lemma f2_normalize_polynomial : Time.PolynomialBound f2_normalize. Abort.
  Lemma is_zero_poly_polynomial : Time.PolynomialBound is_zero_poly. Abort.
  Lemma is_one_poly_polynomial : Time.PolynomialBound is_one_poly. Abort.
  Lemma mono_eval_polynomial : Time.PolynomialBound mono_eval. Abort.
  Lemma f2_eval_polynomial : Time.PolynomialBound f2_eval. Abort.
  Lemma count_zeros_bruteforce_complexity : exists c, Time.ComplexityBound count_zeros_bruteforce
    (fun (cn : ℂI (nat) unit) => c +> fun (ce : ℂI (list f2poly) unit) => (2 ^ val cn * c * S (val cn + #|val ce|) ^ c) >|). Abort.
  (** The subsets of the positive literals of the clause. *)
  Lemma violation_poly_complexity : exists c, Time.ComplexityBound violation_poly
    (fun (cC : ℂI (nclause) unit) => (2 ^ length (val cC) * c * S #|val cC| ^ c) >|). Abort.
  Lemma restrict_poly_polynomial : Time.PolynomialBound restrict_poly. Abort.
  Lemma eq_scope_polynomial : Time.PolynomialBound eq_scope. Abort.
  Lemma occurrences_polynomial : Time.PolynomialBound occurrences. Abort.
  Lemma max_degree_polynomial : Time.PolynomialBound max_degree. Abort.

  (** *** 5. Rationals and truncated polynomials (in the bit sizes) *)

  Lemma qadd_polynomial : Time.PolynomialBound qadd. Abort.
  Lemma qsub_polynomial : Time.PolynomialBound qsub. Abort.
  Lemma qmul_polynomial : Time.PolynomialBound qmul. Abort.
  Lemma qdiv_polynomial : Time.PolynomialBound qdiv. Abort.
  Lemma qneg_polynomial : Time.PolynomialBound qneg. Abort.
  Lemma qofZ_polynomial : Time.PolynomialBound qofZ. Abort.
  Lemma qofN_polynomial : Time.PolynomialBound qofN. Abort.
  Lemma qeqb_polynomial : Time.PolynomialBound qeqb. Abort.
  Lemma qltb_polynomial : Time.PolynomialBound qltb. Abort.
  Lemma qsum_polynomial : Time.PolynomialBound qsum. Abort.
  Lemma vzero_polynomial : Time.PolynomialBound vzero. Abort.
  Lemma vunit_polynomial : Time.PolynomialBound vunit. Abort.
  Lemma vadd_polynomial : Time.PolynomialBound vadd. Abort.
  Lemma vsub_polynomial : Time.PolynomialBound vsub. Abort.
  Lemma vscale_polynomial : Time.PolynomialBound vscale. Abort.
  Lemma dotQ_polynomial : Time.PolynomialBound dotQ. Abort.
  Lemma dotZ_polynomial : Time.PolynomialBound dotZ. Abort.
  Lemma padd_polynomial : Time.PolynomialBound padd. Abort.
  Lemma pscale_polynomial : Time.PolynomialBound pscale. Abort.
  Lemma psub_polynomial : Time.PolynomialBound psub. Abort.
  Lemma pmul_polynomial : Time.PolynomialBound pmul. Abort.
  Lemma pmul_trunc_polynomial : Time.PolynomialBound pmul_trunc. Abort.
  Lemma peval_polynomial : Time.PolynomialBound peval. Abort.
  Lemma pshift_polynomial : Time.PolynomialBound pshift. Abort.

  (** *** 6. The parity lift *)

  Lemma zpadd_polynomial : Time.PolynomialBound zpadd. Abort.
  Lemma zpmul_polynomial : Time.PolynomialBound zpmul. Abort.
  Lemma binomZ_polynomial : Time.PolynomialBound binomZ. Abort.
  Lemma parity_poly_polynomial : Time.PolynomialBound parity_poly. Abort.
  Lemma suffix_sums_polynomial : Time.PolynomialBound suffix_sums. Abort.
  Lemma divmod_h_polynomial : Time.PolynomialBound divmod_h. Abort.
  Lemma lift_coeffs_aux_polynomial : Time.PolynomialBound lift_coeffs_aux. Abort.
  Lemma lift_coeffs_polynomial : Time.PolynomialBound lift_coeffs. Abort.

  (** *** 7. The coefficient ring *)

  Lemma rv_add_polynomial : Time.PolynomialBound rv_add. Abort.
  Lemma rv_scale_polynomial : Time.PolynomialBound rv_scale. Abort.
  Lemma rv_mul_aux_polynomial : Time.PolynomialBound rv_mul_aux. Abort.
  Lemma rv_mul_polynomial : Time.PolynomialBound rv_mul. Abort.
  Lemma rv_coeff_polynomial : Time.PolynomialBound rv_coeff. Abort.
  Lemma lifted_factor_polynomial : Time.PolynomialBound lifted_factor. Abort.
  Lemma lift_eval_polynomial (theta : nat -> qpoly) :
    Time.PolynomialBound theta -> Time.PolynomialBound (fun J p => lift_eval J p theta). Abort.

  (** *** 8. The design: powers of [r], up to [K = r ^ pts] and [D = K ^ 2] *)

  Lemma p_K_complexity : exists c, Time.ComplexityBound p_K
    (fun (cpr : ℂI (params) unit) => (c * S (#|val cpr|) ^ c * S (p_r (val cpr)) ^ p_pts (val cpr)) >|). Abort.
  Lemma p_D_complexity : exists c, Time.ComplexityBound p_D
    (fun (cpr : ℂI (params) unit) => (c * S (#|val cpr|) ^ c * S (p_r (val cpr)) ^ (2 * p_pts (val cpr))) >|). Abort.
  Lemma digit_complexity : exists c, Time.ComplexityBound digit
    (fun (cr : ℂI (nat) unit) => c +> fun (ct : ℂI (nat) unit) => c +> fun (ca : ℂI (nat) unit) => (c * S (val cr + val ct + val ca) ^ c * S (val cr) ^ val ct) >|).
  Abort.
  Lemma set_digit_complexity : exists c, Time.ComplexityBound set_digit
    (fun (cr : ℂI (nat) unit) => c +> fun (ct : ℂI (nat) unit) => c +> fun (ca : ℂI (nat) unit) => c +> fun (cg : ℂI (nat) unit) =>
       (c * S (val cr + val ct + val ca + val cg) ^ c * S (val cr) ^ val ct) >|). Abort.
  Lemma lab_a_polynomial : Time.PolynomialBound lab_a. Abort.
  Lemma lab_d_polynomial : Time.PolynomialBound lab_d. Abort.
  Lemma swap_pos_complexity : exists c, Time.ComplexityBound swap_pos
    (fun (cr : ℂI (nat) unit) => c +> fun (cK : ℂI (nat) unit) => c +> fun (cs : ℂI (nat) unit) => c +> fun (cu : ℂI (nat) unit) =>
       (c * S (val cr + val cK + val cs + val cu) ^ c * S (val cr) ^ val cs) >|). Abort.
  Lemma swap_all_polynomial : Time.PolynomialBound swap_all. Abort.
  Lemma eig_entry_polynomial : Time.PolynomialBound eig_entry. Abort.
  Lemma eig_negative_polynomial : Time.PolynomialBound eig_negative. Abort.
  Lemma pair_eigenbasis_polynomial : Time.PolynomialBound pair_eigenbasis. Abort.
  Lemma in_interval_polynomial : Time.PolynomialBound in_interval. Abort.
  (** The products of [pts] factors among the [r ^ 2] pair eigenvectors,
      each a row of length [K ^ 2]. *)
  Lemma aux_measurements_complexity : exists c, Time.ComplexityBound aux_measurements
    (fun (cpr : ℂI (params) unit) => (c * S (#|val cpr|) ^ c * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma times_W0_complexity : exists c, Time.ComplexityBound times_W0
    (fun (cpr : ℂI (params) unit) => c +> fun (cv : ℂI (list Q) unit) => (c * S (#|val cpr| + #|val cv|) ^ c * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|).
  Abort.
  Lemma fW0_row_complexity : exists c, Time.ComplexityBound fW0_row
    (fun (cpr : ℂI (params) unit) => c +> fun (cw : ℂI (nat) unit) => (c * S (#|val cpr| + val cw) ^ c * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|).
  Abort.
  Lemma phi_poly_complexity : exists c, Time.ComplexityBound phi_poly
    (fun (cpr : ℂI (params) unit) => c +> fun (cu : ℂI (nat) unit) => c +> fun (cy : ℂI (nat) unit) =>
       (c * S (#|val cpr| + val cu + val cy) ^ c * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma aux_row_complexity : exists c, Time.ComplexityBound aux_row
    (fun (cpr : ℂI (params) unit) => c +> fun (cu : ℂI (nat) unit) => (c * S (#|val cpr| + val cu) ^ c * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|).
  Abort.
  Lemma incidences_polynomial : Time.PolynomialBound incidences. Abort.
  Lemma prob_same_polynomial : Time.PolynomialBound prob_same. Abort.
  Lemma opt_digit_complexity : exists c, Time.ComplexityBound opt_digit
    (fun (cr : ℂI (nat) unit) => c +> fun (ct : ℂI (nat) unit) => c +> fun (cx : ℂI (option nat) unit) => (c * S (val cr + val ct + #|val cx|) ^ c * S (val cr) ^ val ct) >|).
  Abort.
  Lemma label_potential_complexity : exists c, Time.ComplexityBound label_potential
    (fun (cpr : ℂI (params) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (cb : ℂI (nat) unit) => c +> fun (cw : ℂI (nat) unit) => c +> fun (ci : ℂI (list (nat * nat)) unit) => c +> fun (ca : ℂI (list (option nat)) unit) => c +> fun (cd : ℂI (list (option nat)) unit) =>
       (c * S (#|val cpr| + val cn + val cb + val cw + #|val ci| + #|val ca| + #|val cd|) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma argmin_first_polynomial (cost : nat -> Q) :
    Time.PolynomialBound cost -> Time.PolynomialBound (fun cands => argmin_first cands cost). Abort.
  Lemma unopt_polynomial : Time.PolynomialBound unopt. Abort.
  Lemma choose_labels_complexity : exists c, Time.ComplexityBound choose_labels
    (fun (cpr : ℂI (params) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (cb : ℂI (nat) unit) => c +> fun (cw : ℂI (nat) unit) => c +> fun (cs : ℂI (list (list nat)) unit) =>
       (c * S (#|val cpr| + val cn + val cb + val cw + #|val cs|) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma assign_copies_polynomial : Time.PolynomialBound assign_copies. Abort.
  Lemma design_of_labels_complexity : exists c, Time.ComplexityBound design_of_labels
    (fun (cpr : ℂI (params) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (cs : ℂI (list (list nat)) unit) => c +> fun (ca : ℂI (list nat) unit) => c +> fun (cd : ℂI (list nat) unit) =>
       (c * S (#|val cpr| + val cn + #|val cs| + #|val ca| + #|val cd|) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma build_design_complexity : exists c, Time.ComplexityBound build_design
    (fun (cpr : ℂI (params) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (cb : ℂI (nat) unit) => c +> fun (cw : ℂI (nat) unit) => c +> fun (cs : ℂI (list (list nat)) unit) =>
       (c * S (#|val cpr| + val cn + val cb + val cw + #|val cs|) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.

  (** *** 9. The counting routine *)

  Lemma group_vars_complexity : exists c, Time.ComplexityBound group_vars
    (fun (cpr : ℂI (params) unit) => c +> fun (cd : ℂI (design) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (ct : ℂI (nat) unit) => c +> fun (cg : ℂI (nat) unit) =>
       (c * S (#|val cpr| + #|val cd| + val cn + val ct + val cg) ^ c * S (p_r (val cpr)) ^ val ct) >|). Abort.
  Lemma factor_group_complexity : exists c, Time.ComplexityBound factor_group
    (fun (cpr : ℂI (params) unit) => c +> fun (cd : ℂI (design) unit) => c +> fun (ct : ℂI (nat) unit) => c +> fun (cf : ℂI (nat) unit) =>
       (c * S (#|val cpr| + #|val cd| + val ct + val cf) ^ c * S (p_r (val cpr)) ^ val ct) >|). Abort.
  Lemma find_inc_polynomial : Time.PolynomialBound find_inc. Abort.
  Lemma point_rows_polynomial : Time.PolynomialBound point_rows. Abort.
  Lemma corrections_polynomial : Time.PolynomialBound corrections. Abort.
  Lemma group_value_complexity : exists c, Time.ComplexityBound group_value
    (fun (cJ : ℂI (nat) unit) => c +> fun (cl : ℂI (nat) unit) => c +> fun (ces : ℂI (list (Z * Z)) unit) => c +> fun (ceqs : ℂI (list f2poly) unit) => c +> fun (cpr : ℂI (params) unit) => c +> fun (cd : ℂI (design) unit) =>
       c +> fun (ct : ℂI (nat) unit) => c +> fun (cg : ℂI (nat) unit) => c +> fun (cPt : ℂI (list (list Q)) unit) => c +> fun (cDelta : ℂI (list qpoly) unit) => c +> fun (cx : ℂI (list bool) unit) =>
       (c * S (val cJ + val cl + #|val ces| + #|val ceqs| + #|val cpr| + #|val cd| + val ct + val cg
               + #|val cPt| + #|val cDelta| + #|val cx|) ^ c * S (p_r (val cpr)) ^ val ct) >|). Abort.
  (** The measurement values: [(2 D + 1) ^ (r c)] tuples; for each, the
      assignments of each group, with one application of [A] each. *)
  Lemma separated_sum_complexity (A : nat -> list bool -> rv)
    (cA : ℂI nat unit -> ℂO (ℂI (list bool) unit -> ℂO unit)) (g : nat -> nat) :
    Time.ComplexityBound A cA ->
    (forall a x, cost (cA (a ⋊ tt)) + cost (res (cA (a ⋊ tt)) (x ⋊ tt)) <= g (a + #|x|)) ->
    (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun J l n D r meas groups E => separated_sum J l n D r meas groups E A)
      (fun (cJ : ℂI nat unit) => c +> fun (cl : ℂI nat unit) => c +> fun (cn : ℂI nat unit) => c +>
       fun (cD : ℂI nat unit) => c +> fun (cr : ℂI nat unit) => c +> fun (cm : ℂI (list (list Z)) unit) => c +>
       fun (cg : ℂI (list (list nat)) unit) => c +> fun (cE : ℂI (list nat) unit) =>
         (S (2 * val cD + 1) ^ (val cr * length (val cm)) * S (val cr) * 2 ^ maxN (map (@length nat) (val cg))
            * (g (c * S (val cn + val cr) ^ c)
               + c * S (val cJ + val cl + val cn + val cD + val cr + #|val cm| + #|val cg| + #|val cE|) ^ c)) >|).
  Abort.
  (** The subsets [U ⊆ E] with [|E| <= q], and the separated sums. *)
  Lemma taylor_at_complexity : exists c, Time.ComplexityBound taylor_at
    (fun (cpr : ℂI (params) unit) => c +> fun (cd : ℂI (design) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (cl : ℂI (nat) unit) => c +> fun (cJ : ℂI (nat) unit) => c +> fun (cq : ℂI (nat) unit) => c +> fun (ces : ℂI (list (Z * Z)) unit) =>
       c +> fun (ceqs : ℂI (list f2poly) unit) => c +> fun (ct : ℂI (nat) unit) =>
       (S (val cn) ^ (S (val cq)) * 2 ^ val cq
          * S (2 * p_D (val cpr) + 1) ^ (p_r (val cpr) * length (ds_meas (val cd)))
          * 2 ^ maxN (map (fun g => length (group_vars (val cpr) (val cd) (val cn) (val ct) g))
                          (range (p_r (val cpr))))
          * c * S (#|val cpr| + #|val cd| + val cn + val cl + val cJ + val cq + #|val ces| + #|val ceqs| + val ct) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.

  (** *** 10. Hermite interpolation *)

  Lemma find_pivot_polynomial : Time.PolynomialBound find_pivot. Abort.
  Lemma det_aux_polynomial : Time.PolynomialBound det_aux. Abort.
  Lemma det_polynomial : Time.PolynomialBound det. Abort.
  Lemma hermite_matrix_polynomial : Time.PolynomialBound hermite_matrix. Abort.
  Lemma hermite_value_at_0_polynomial : Time.PolynomialBound hermite_value_at_0. Abort.
  Lemma factor_scopes_polynomial : Time.PolynomialBound factor_scopes. Abort.
  (** [pts] Taylor expansions, with [q = J - 1]. *)
  Lemma count_from_design_complexity : exists c, Time.ComplexityBound count_from_design
    (fun (cpr : ℂI (params) unit) => c +> fun (cd : ℂI (design) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (ck : ℂI (nat) unit) => c +> fun (cl : ℂI (nat) unit) => c +> fun (ces : ℂI (list (Z * Z)) unit) => c +> fun (ceqs : ℂI (list f2poly) unit) =>
       let J := val ck * p_R (val cpr) * (length (val ceqs) + 2 * (val cl - 1)) / p_pts (val cpr) + 1 in
       (S (val cn) ^ (S J) * 2 ^ J
          * S (2 * p_D (val cpr) + 1) ^ (p_r (val cpr) * length (ds_meas (val cd)))
          * 2 ^ maxN (map (fun t => maxN (map (fun g => length (group_vars (val cpr) (val cd) (val cn) t g))
                                               (range (p_r (val cpr)))))
                          (seq 1 (p_pts (val cpr))))
          * c * S (#|val cpr| + #|val cd| + val cn + val ck + val cl + #|val ces| + #|val ceqs|) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.
  Lemma count_with_design_complexity : exists c, Time.ComplexityBound count_with_design
    (fun (cpr : ℂI (params) unit) => c +> fun (cn : ℂI (nat) unit) => c +> fun (ck : ℂI (nat) unit) => c +> fun (cl : ℂI (nat) unit) => c +> fun (ces : ℂI (list (Z * Z)) unit) => c +> fun (ceqs : ℂI (list f2poly) unit) => c +> fun (cb : ℂI (nat) unit) =>
       c +> fun (cw : ℂI (nat) unit) =>
       let d := build_design (val cpr) (val cn) (val cb) (val cw) (factor_scopes (val cn) (val ceqs)) in
       let J := val ck * p_R (val cpr) * (length (val ceqs) + 2 * (val cl - 1)) / p_pts (val cpr) + 1 in
       (S (val cn) ^ (S J) * 2 ^ J
          * S (2 * p_D (val cpr) + 1) ^ (p_r (val cpr) * length (ds_meas d))
          * 2 ^ maxN (map (fun t => maxN (map (fun g => length (group_vars (val cpr) d (val cn) t g))
                                               (range (p_r (val cpr)))))
                          (seq 1 (p_pts (val cpr))))
          * c * S (#|val cpr| + val cn + val ck + val cl + #|val ces| + #|val ceqs| + val cb + val cw) ^ c
          * S (p_r (val cpr)) ^ (c * p_pts (val cpr))) >|). Abort.

  (** *** 11. Common zeros of sparse equations *)

  Lemma find_beta_complexity : exists c, Time.ComplexityBound find_beta
    (fun (cf : ℂI (nat) unit) => c +> fun (cl : ℂI (nat) unit) => c +> fun (cb : ℂI (nat) unit) => c +> fun (cw : ℂI (nat) unit) => c +> fun (cbeta : ℂI (nat) unit) =>
       (c * S (val cf + val cl + val cb + val cw + val cbeta) ^ c * S (val cl) ^ (val cbeta + val cf)) >|).
  Abort.
  (** Polynomial in [n]: the parameters give [D <= n] (Lemma 4.8). *)
  Lemma choose_params_polynomial : Time.PolynomialBound choose_params. Abort.
  (** Theorem 2.2, for each branch and in all: subexponential in [n] for
      sparse equations, whose variables occur in at most [b] scopes; the
      exhaustive fallback is taken only for small [n] (to check). *)
  Lemma count_branch_complexity (k : nat) : exists C : nat -> nat,
    Time.ComplexityBound (count_branch k)
      (fun (cn : ℂI nat unit) => C 0 +> fun (cl : ℂI nat unit) => C 0 +> fun (ces : ℂI (list (Z * Z)) unit) =>
       C 0 +> fun (ch : ℂI (list nat) unit) => C 0 +> fun (ceqs : ℂI (list f2poly) unit) => C 0 +>
       fun (cbits : ℂI (list bool) unit) =>
         let b := maxN (map (fun v => occurrences v (factor_scopes (val cn) (val ceqs))) (range (val cn))) in
         (C b * S (val cn + val cl + #|val ces| + #|val ch| + #|val ceqs| + #|val cbits|) ^ C b
            * 2 ^ (C b * rho (val cn))) >|). Abort.
  Lemma count_zeros_complexity (k : nat) : exists C : nat -> nat,
    Time.ComplexityBound (count_zeros k)
      (fun (cn : ℂI nat unit) => C 0 +> fun (ceqs : ℂI (list f2poly) unit) =>
         let b := maxN (map (fun v => occurrences v (factor_scopes (val cn) (val ceqs))) (range (val cn))) in
         (C b * S (val cn + #|val ceqs|) ^ C b * 2 ^ (C b * rho (val cn))) >|). Abort.

  (** *** 12. From a sparse formula to sparse equations *)

  Lemma log_size_polynomial : Time.PolynomialBound log_size. Abort.
  Lemma eps_inv_polynomial : Time.PolynomialBound eps_inv. Abort.
  Lemma delta_inv_polynomial : Time.PolynomialBound delta_inv. Abort.
  Lemma dist_denom_polynomial : Time.PolynomialBound dist_denom. Abort.
  Lemma degree_bound_polynomial : Time.PolynomialBound degree_bound. Abort.
  Lemma parity_bits_polynomial : Time.PolynomialBound parity_bits. Abort.
  (** The [2 ^ lG] characters. *)
  Lemma walsh_ok_complexity : exists c, Time.ComplexityBound walsh_ok
    (fun (clG : ℂI (nat) unit) => c +> fun (cdG : ℂI (nat) unit) => c +> fun (ce : ℂI (nat) unit) => c +> fun (cs : ℂI (list nat) unit) =>
       (2 ^ val clG * c * S (val clG + val cdG + val ce + #|val cs|) ^ c) >|). Abort.
  (** The words of weight at most [h] among [dG] positions. *)
  Lemma kernel_word_free_complexity : exists c, Time.ComplexityBound kernel_word_free
    (fun (cdG : ℂI (nat) unit) => c +> fun (ch : ℂI (nat) unit) => c +> fun (cA : ℂI (list (list bool)) unit) =>
       (S (val cdG) ^ val ch * c * S (val cdG + val ch + #|val cA|) ^ c) >|). Abort.
  (** The shifts ([qG ^ dG] tuples) and the local codes ([2 ^ (cG dG)]),
      with [dG <= degree_bound m B] and [qG <= 2 m]. *)
  Lemma tanner_rows_complexity : exists c, Time.ComplexityBound tanner_rows
    (fun (cm : ℂI (nat) unit) => c +> fun (cB : ℂI (nat) unit) =>
       (c * S (2 * val cm) ^ (c * S (degree_bound (val cm) (val cB))) * 2 ^ (c * degree_bound (val cm) (val cB) ^ 2)
          * S (val cm + val cB) ^ c) >|). Abort.
  Lemma clause_coeff_polynomial : Time.PolynomialBound clause_coeff. Abort.
  Lemma row_poly_complexity : exists c, Time.ComplexityBound row_poly
    (fun (cF : ℂI (ncnf) unit) => c +> fun (crow : ℂI (hash_row) unit) => (2 ^ max_width (val cF) * c * S (#|val cF| + #|val crow|) ^ c) >|). Abort.
  (** [rounds] rounds of [(2 m) ^ P] candidates, each counted by [count0]. *)
  Lemma greedy_rows_complexity (count0 : list f2poly -> Z) (c0 : ℂI (list f2poly) unit -> ℂO unit)
    (g : nat -> nat) :
    Time.ComplexityBound count0 c0 -> (forall e, cost (c0 (e ⋊ tt)) <= g #|e|) ->
    (forall x y, x <= y -> g x <= g y) ->
    exists c, Time.ComplexityBound (fun F P rounds A => greedy_rows count0 F P rounds A)
      (fun (cF : ℂI ncnf unit) => c +> fun (cP : ℂI nat unit) => c +> fun (cr : ℂI nat unit) => c +>
       fun (cA : ℂI (list hash_row) unit) =>
         (val cr * S (2 * length (val cF)) ^ val cP
            * (g (c * S (#|val cF| + val cP + val cr + #|val cA|) ^ c * 2 ^ max_width (val cF))
               + c * S (#|val cF| + val cP + val cr + #|val cA|) ^ c * 2 ^ max_width (val cF))) >|). Abort.
  Lemma count_sparse_formula_complexity (k B : nat) : exists C,
    Time.ComplexityBound (fun n F => count_sparse_formula k n B F)
      (fun (cn : ℂI nat unit) => C +> fun (cF : ℂI ncnf unit) =>
         (C * S (val cn + #|val cF|) ^ (C * S (dist_denom (length (val cF)) B)) * 2 ^ (C * rho (val cn))) >|).
  Abort.

  (** *** 13. The algorithm (Proposition 6.4) *)

  (** The main result: [(n + m) ^ O_k(1) 2 ^ O_k(rho n)], where the width
      [k'] of the normalised formula is at least [k]. *)
  Theorem count_sat_complexity (k : nat) : exists C : nat -> nat,
    Time.ComplexityBound (count_sat k)
      (fun (cn : ℂI nat unit) => C 0 +> fun (cF : ℂI cnf unit) =>
         let k' := Nat.max 2 (Nat.max k (max_width (normalize (map norm_clause (val cF))))) in
         (C k' * S (val cn + #|val cF|) ^ C k' * 2 ^ (C k' * rho (val cn))) >|). Abort.
End ETHPlan.
