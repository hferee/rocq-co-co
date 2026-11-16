(** * Cost analysis of the ETH algorithm ([ETHAlgorithm])

    The functions are analysed as they are written in [ETHAlgorithm], by
    [cbound] ([TimeFix]): the compiler only replaces terms by
    convertible ones. The constants are the smallest ones
    for the shape of each bound (see [NatComplexity]). This file is the start
    of the analysis; the remarks at the end list what is covered. *)

From Complexity Require Export TimeStdlib ETHAlgorithm.
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
       (28 * list_sum (val ca) + 67 * length (val ca) + 8) >|).
  Proof. cbound. all: unfold list_sum in *; lia. Qed.

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
       (length (val cl) * (14 * (val ca + list_sum (val cl)) + 42) + 6) >|).
  Proof. cbound. all: unfold list_sum in *; nia. Qed.

  Global Instance sumN_complexity : Time.ComplexityBound sumN
    (fun cl =>
       (length (val cl) * (14 * list_sum (val cl) + 42) + 13) >|) := _.
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
      constructors, case analyses ([ETHData] below declares the first two).

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
    The bounds of [memN], [countN], [eqbN], [insert_uniq], [range] and
    [sumN] are proved above ([ETHCost]).

    Prerequisites (not yet in the library):
    - the axioms of the data types of the algorithm, which come with the
      algorithm: [literal], [params], [design] (records) and [pair_eig]
      ([ETHData] below declares their representations and sizes; their
      constructors, case analyses and projections are still to be
      axiomatised);
    - bounds of functions of the standard library (section 0 below);
    - higher-order functions on ground lists ([map], [filter], ...): their
      bounds are in [HOListComplexity], in the model with lists of any data,
      while [ETHCost] is over [TimeStdlib] (ground lists).
    The subexponential bounds of the top layers also need the facts of the
    paper on the parameters: the numerical checks of [choose_params] pass
    for large [n] (otherwise the counts fall back to exhaustive search). *)

(** The data types of the algorithm, with their representations and sizes. *)
Module Type ETHData (Import Time : TimeStdlib).
  #[global] Declare Instance Repr_literal : Ground literal.
  #[global] Declare Instance Size_literal : Size literal.
  #[global] Declare Instance Repr_params : Ground params.
  #[global] Declare Instance Size_params : Size params.
  #[global] Declare Instance Repr_pair_eig : Ground pair_eig.
  #[global] Declare Instance Size_pair_eig : Size pair_eig.
  #[global] Declare Instance Repr_design : Ground design.
  #[global] Declare Instance Size_design : Size design.
End ETHData.

(** The exponent of the paper: rho(n) = n (log log n)^2 / sqrt (log n). *)
Definition rho (n : nat) : nat := n * Nat.log2 (Nat.log2 n) ^ 2 / S (Nat.sqrt (Nat.log2 n)).

Module ETHPlan (Import Time : TimeStdlib) (Import D : ETHData Time).

  (** *** 0. The standard library *)
  Lemma Nat_div_polynomial : Time.PolynomialBound Nat.div. cbound. Abort.
  Lemma Nat_modulo_polynomial : Time.PolynomialBound Nat.modulo. Abort.
  Lemma Nat_div2_polynomial : Time.PolynomialBound Nat.div2. Abort.
  Lemma Nat_odd_polynomial : Time.PolynomialBound Nat.odd. Abort.
  Lemma Nat_even_polynomial : Time.PolynomialBound Nat.even. Abort.
  Lemma Nat_max_polynomial : Time.PolynomialBound Nat.max. Abort.
  Lemma Nat_min_polynomial : Time.PolynomialBound Nat.min. Abort.
  Lemma Nat_log2_polynomial : Time.PolynomialBound Nat.log2. Abort.
  Lemma Nat_sqrt_polynomial : Time.PolynomialBound Nat.sqrt. Abort.
  Lemma Nat_land_polynomial : Time.PolynomialBound Nat.land. Abort.
  Lemma Nat_lxor_polynomial : Time.PolynomialBound Nat.lxor. Abort.
  Lemma Nat_testbit_polynomial : Time.PolynomialBound Nat.testbit. Abort.
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

  Section Lists.
    Context {A B : Type} `{Ground A} `{Size A} `{Ground B} `{Size B}.
    Lemma rev_polynomial : Time.PolynomialBound (@rev A). Abort.
    Lemma nth_polynomial : Time.PolynomialBound (@nth A). Abort.
    Lemma firstn_polynomial : Time.PolynomialBound (@firstn A). Abort.
    Lemma skipn_polynomial : Time.PolynomialBound (@skipn A). Abort.
    Lemma repeat_polynomial : Time.PolynomialBound (@repeat A). Abort.
    Lemma concat_polynomial : Time.PolynomialBound (@concat A). Abort.
    Lemma combine_polynomial : Time.PolynomialBound (@combine A B). Abort.
    Lemma list_prod_polynomial : Time.PolynomialBound (@list_prod A B). Abort.
    Lemma hd_polynomial : Time.PolynomialBound (@hd A). Abort.
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

  Lemma maxN_polynomial : Time.PolynomialBound maxN. Abort.
  Lemma sumZ_polynomial : Time.PolynomialBound sumZ. Abort.
  Lemma zipWith_polynomial {A B C} `{Ground A} `{Size A} `{Ground B} `{Size B} `{Ground C}
    (f : A -> B -> C) : Time.PolynomialBound f -> Time.PolynomialBound (zipWith f). Abort.
  Lemma indexN_polynomial : Time.PolynomialBound indexN. Abort.
  Lemma lexltbN_polynomial : Time.PolynomialBound lexltbN. Abort.
  Lemma subsetN_polynomial : Time.PolynomialBound subsetN. Abort.
  Lemma sort_uniq_polynomial : Time.PolynomialBound sort_uniq. Abort.
  Lemma set_nth_polynomial {A} `{Ground A} `{Size A} : Time.PolynomialBound (@set_nth A). Abort.
  Lemma remove_nth_polynomial {A} `{Ground A} `{Size A} : Time.PolynomialBound (@remove_nth A). Abort.
  Lemma chunks_polynomial {A} `{Ground A} `{Size A} : Time.PolynomialBound (@chunks A). Abort.
  Lemma ceil_div_polynomial : Time.PolynomialBound ceil_div. Abort.
  Lemma clog2_polynomial : Time.PolynomialBound clog2. Abort.
  Lemma csqrt_polynomial : Time.PolynomialBound csqrt. Abort.
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

  Lemma lit_code_polynomial : Time.PolynomialBound lit_code. Abort.
  Lemma code_var_polynomial : Time.PolynomialBound code_var. Abort.
  Lemma code_pos_polynomial : Time.PolynomialBound code_pos. Abort.
  Lemma code_neg_polynomial : Time.PolynomialBound code_neg. Abort.
  Lemma nclause_eval_polynomial : Time.PolynomialBound nclause_eval. Abort.
  Lemma ncnf_eval_polynomial : Time.PolynomialBound ncnf_eval. Abort.
  (** The [2 ^ n] assignments. *)
  Lemma count_bruteforce_complexity : exists c, Time.ComplexityBound count_bruteforce
    (fun (cn : ℂI (nat) unit) => c +> fun (cF : ℂI (ncnf) unit) => (2 ^ val cn * c * S (val cn + #|val cF|) ^ c) >|). Abort.
  Lemma tautological_polynomial : Time.PolynomialBound tautological. Abort.
  Lemma norm_clause_polynomial : Time.PolynomialBound norm_clause. Abort.
  Lemma insert_clause_polynomial : Time.PolynomialBound insert_clause. Abort.
  Lemma sort_clauses_polynomial : Time.PolynomialBound sort_clauses. Abort.
  Lemma strict_subset_polynomial : Time.PolynomialBound strict_subset. Abort.
  Lemma antichain_polynomial : Time.PolynomialBound antichain. Abort.
  Lemma normalize_polynomial : Time.PolynomialBound normalize. Abort.
  Lemma has_empty_clause_polynomial : Time.PolynomialBound has_empty_clause. Abort.
  Lemma max_width_polynomial : Time.PolynomialBound max_width. Abort.

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
