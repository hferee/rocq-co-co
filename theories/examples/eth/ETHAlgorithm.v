(** * The "ETH is false" counting algorithm, as native Rocq code

    Source: OpenAI, "The Exponential Time Hypothesis is False" (preprint dated
    October 25, 2026, https://github.com/openai/math, directory
    [preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026]) and its
    Lean formalization [lean/OAI/Algorithms/SubexponentialSAT].

    The Lean development states its result
    ([SqrtLogSpace.exact_count_and_sat]) for a multi-tape Turing machine
    ([Computation.PrimitiveMachine]). That machine is compiled
    ([GuardedCompiler.primitive]) from a [BitProgram]: a register machine with
    80 one-bit registers and 1220 Boolean stacks, assembled from structured
    commands ([Native.countingProgram cutoff k (NativeLeafProgram.command k)]).

    This file does not transcribe that stack program instruction by
    instruction. It transcribes the algorithm that the program implements, as
    described in the preprint, into plain functional Rocq: the "rational
    interpolation" algorithm of Proposition 6.4, whose exponent
    rho(n) = n (log log n)^2 / sqrt(log n) is the one proved in Lean
    ([SqrtLog.Statement.runtimeScale]). Its layers are:

    - Appendix A: disjoint sparsification ([sparsify_fold]);
    - Section 6: reduction of each sparse formula to sparse polynomial
      equations over F_2, via a Tanner code ([tanner_rows]) and greedy parity
      tests chosen by counting ([greedy_rows]);
    - Section 5: counting common zeros of sparse equations ([count_zeros]),
      via the Beigel-Tarui parity lift ([lift_coeffs]), branching on frequent
      variables and the design of Section 4 ([build_design]);
    - Section 3: the counting routine itself: separation by measurements
      ([separated_sum]), Taylor coefficients by Boolean differences
      ([taylor_at]) and Hermite interpolation ([hermite_value_at_0]).

    Differences with the paper/Lean that do not change the computed values:
    - rationals are [Q] normalised with [Qred], instead of integers over fixed
      common denominators (Appendix B);
    - the value at 0 of the Hermite interpolant is computed by Cramer's rule
      with Gaussian elimination over [Q], instead of fraction-free (Bareiss)
      elimination over [Z];
    - the conditional expectations of Lemma 4.5 are computed from closed-form
      probabilities, instead of by enumerating assignments of each indicator;
    - groups are numbered 0..r-1 instead of 1..r;
    - small inputs use the paper's computable guards (exhaustive search when
      n < 20 or a parameter check fails), whereas the Lean machine takes an
      existentially quantified cutoff.

    Nothing here is proved: neither correctness nor cost. Recursion is
    structural (on lists or [nat]) everywhere. Explicit fuel is used only where
    the paper bounds the number of iterations, as noted at each use.

    Complexity. The enumerations visit the same sets as the paper's, with the
    same nesting: measurement tuples times the assignments of one group
    (Lemma 3.2), pairs U ⊆ E with |E| <= q (C_q in (3.14)), branches on
    frequent variables (Section 5.5), (2m)^P greedy candidates (Lemma 6.2),
    shifts and local codes (Lemma 6.1), and the sparsification tree
    (Appendix A). Product spaces are folded over ([fold_tuples]), not stored.
    Every [nat] value is polynomial in the input size: the largest are
    D = r^(2Q) <= (2n)^(1/128), q_G < 2m and M^(k-1) = polylog(n). Counts and
    coefficients, which can have poly(n) bits, are [Z] and [Q]. So under
    call-by-value, even with unary [nat], the running time is within a
    polynomial factor of the paper's (n+m)^O_k(1) 2^O_k(ρ(n)), provided [Z]
    and [Q] operations cost polynomially in the bit sizes. Appendix B bounds
    those sizes polynomially; reducing with [Qred] can only shrink them, and
    Gaussian elimination over [Q] keeps them polynomial.

    With the paper's parameters, the subexponential path is only taken for
    astronomically large inputs: the top-level schedule s = ⌊√λ/ν²⌋ first
    reaches 2 at λ = ⌈log2 n⌉ = 521284, and the parameter checks of
    Lemma 4.8 need λ above 10^10. Every executable instance therefore takes
    the exhaustive-search fallback. The examples at the end exercise the inner
    components directly on tiny parameters instead. *)

From Stdlib Require Import Arith Bool List ZArith QArith Qreduction Qround.
Import ListNotations.

Local Open Scope nat_scope.

(** ** 1. Generic utilities *)

Definition range (n : nat) : list nat := seq 0 n.

Definition sumN (l : list nat) : nat := fold_left Nat.add l 0.
Definition maxN (l : list nat) : nat := fold_left Nat.max l 0.
Definition sumZ (l : list Z) : Z := fold_left Z.add l 0%Z.

Fixpoint zipWith {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : list C :=
  match l, l' with
  | a :: l, b :: l' => f a b :: zipWith f l l'
  | _, _ => []
  end.

Fixpoint memN (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: l' => (x =? y) || memN x l'
  end.

Fixpoint indexN (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: l' => if x =? y then 0 else S (indexN x l')
  end.

Fixpoint countN (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: l' => (if x =? y then 1 else 0) + countN x l'
  end.

Fixpoint eqbN (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && eqbN a' b'
  | _, _ => false
  end.

(* Lexicographic order on lists of naturals. *)
Fixpoint lexltbN (a b : list nat) : bool :=
  match a, b with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: a', y :: b' => (x <? y) || ((x =? y) && lexltbN a' b')
  end.

Definition subsetN (a b : list nat) : bool := forallb (fun x => memN x b) a.

(* Insertion into a strictly increasing list; duplicates are dropped. *)
Fixpoint insert_uniq (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: l' => if x <? y then x :: l else if x =? y then l else y :: insert_uniq x l'
  end.

Definition sort_uniq (l : list nat) : list nat := fold_right insert_uniq [] l.

Fixpoint set_nth {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => x :: l'
  | y :: l', S i' => y :: set_nth l' i' x
  end.

Fixpoint remove_nth {A} (l : list A) (i : nat) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => l'
  | y :: l', S i' => y :: remove_nth l' i'
  end.

(* [count] consecutive blocks of length [size]. *)
Fixpoint chunks {A} (size count : nat) (l : list A) : list (list A) :=
  match count with
  | 0 => []
  | S c => firstn size l :: chunks size c (skipn size l)
  end.

Definition ceil_div (a b : nat) : nat := (a + b - 1) / b.

(* ⌈log2 n⌉, the least λ with n <= 2^λ. *)
Definition clog2 (n : nat) : nat := if n <=? 1 then 0 else S (Nat.log2 (n - 1)).

(* ⌈√n⌉ *)
Definition csqrt (n : nat) : nat :=
  let s := Nat.sqrt n in if s * s =? n then s else S s.

(* The integers -D, ..., D. *)
Definition zinterval (D : nat) : list Z :=
  map (fun i => (Z.of_nat i - Z.of_nat D)%Z) (seq 0 (2 * D + 1)).

(** Enumeration of product spaces. Tuples are visited in lexicographic order,
    first coordinate slowest, and are never all stored at once. *)
Fixpoint fold_tuples {A B} (len : nat) (alphabet : list A) (f : B -> list A -> B)
  (acc : B) (prefix : list A) : B :=
  match len with
  | 0 => f acc (rev prefix)
  | S len' =>
      fold_left (fun acc a => fold_tuples len' alphabet f acc (a :: prefix)) alphabet acc
  end.

Fixpoint find_first {A B} (f : A -> option B) (l : list A) : option B :=
  match l with
  | [] => None
  | a :: l' => match f a with Some b => Some b | None => find_first f l' end
  end.

(* First tuple, in the order of [fold_tuples], satisfying [p]. *)
Fixpoint find_tuple {A} (len : nat) (alphabet : list A) (p : list A -> bool)
  (prefix : list A) : option (list A) :=
  match len with
  | 0 => let t := rev prefix in if p t then Some t else None
  | S len' => find_first (fun a => find_tuple len' alphabet p (a :: prefix)) alphabet
  end.

(* The sublists of [l] of length [k]. *)
Fixpoint combinations (l : list nat) (k : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k' =>
      match l with
      | [] => []
      | x :: l' => map (cons x) (combinations l' k') ++ combinations l' k
      end
  end.

(* Fold over the sublists of [l] of length [k], without storing them. *)
Fixpoint fold_combinations {B} (l : list nat) (k : nat) (f : B -> list nat -> B)
  (acc : B) (prefix : list nat) : B :=
  match k with
  | 0 => f acc (rev prefix)
  | S k' =>
      match l with
      | [] => acc
      | x :: l' =>
          fold_combinations l' k f (fold_combinations l' k' f acc (x :: prefix)) prefix
      end
  end.

(* Fold over all sublists of [l]. *)
Fixpoint fold_sublists {B} (l : list nat) (f : B -> list nat -> B) (acc : B)
  (prefix : list nat) : B :=
  match l with
  | [] => f acc (rev prefix)
  | x :: l' => fold_sublists l' f (fold_sublists l' f acc prefix) (x :: prefix)
  end.

(* The 0/1 vector of length [n] equal to [bits] on [vars], false elsewhere. *)
Definition embed (n : nat) (vars : list nat) (bits : list bool) : list bool :=
  map (fun v => if memN v vars then nth (indexN v vars) bits false else false) (range n).

(** ** 2. Formulas *)

(* Input formulas, following the Lean statement ([SAT.Literal], [SAT.CNF]). *)
Record literal := mkLit { lvar : nat; lpos : bool }.
Definition clause := list literal.
Definition cnf := list clause.

Definition lit_eval (x : list bool) (l : literal) : bool :=
  Bool.eqb (nth (lvar l) x false) (lpos l).
Definition clause_eval (x : list bool) (C : clause) : bool := existsb (lit_eval x) C.
Definition cnf_eval (x : list bool) (F : cnf) : bool := forallb (clause_eval x) F.

(* The specification: the number of satisfying assignments in {0,1}^n. *)
Definition count_spec (n : nat) (F : cnf) : Z :=
  fold_tuples n [false; true]
    (fun acc x => if cnf_eval x F then (acc + 1)%Z else acc) 0%Z [].

(* Normalised clauses: strictly increasing lists of literal codes
   2 * variable + (1 if positive), as [Encoding.literalCode] in Lean. *)
Definition lit_code (l : literal) : nat := 2 * lvar l + (if lpos l then 1 else 0).
Definition code_var (c : nat) : nat := Nat.div2 c.
Definition code_pos (c : nat) : bool := Nat.odd c.
Definition code_neg (c : nat) : nat := if Nat.odd c then c - 1 else S c.

Definition nclause := list nat.
Definition ncnf := list nclause.

Definition nclause_eval (x : list bool) (C : nclause) : bool :=
  existsb (fun c => Bool.eqb (nth (code_var c) x false) (code_pos c)) C.
Definition ncnf_eval (x : list bool) (F : ncnf) : bool := forallb (nclause_eval x) F.

(* Exhaustive search, the fallback used for small or degenerate inputs. *)
Definition count_bruteforce (n : nat) (F : ncnf) : Z :=
  fold_tuples n [false; true]
    (fun acc x => if ncnf_eval x F then (acc + 1)%Z else acc) 0%Z [].

Definition tautological (C : nclause) : bool := existsb (fun c => memN (code_neg c) C) C.
Definition norm_clause (C : clause) : nclause := sort_uniq (map lit_code C).

Fixpoint insert_clause (C : nclause) (F : ncnf) : ncnf :=
  match F with
  | [] => [C]
  | C' :: F' =>
      if lexltbN C C' then C :: F
      else if eqbN C C' then F
      else C' :: insert_clause C F'
  end.

(* Sorts the clauses and removes duplicates. *)
Definition sort_clauses (F : ncnf) : ncnf := fold_right insert_clause [] F.

Definition strict_subset (a b : nclause) : bool := subsetN a b && negb (subsetN b a).

(* Removes the clauses containing another clause. *)
Definition antichain (F : ncnf) : ncnf :=
  filter (fun C => negb (existsb (fun C' => strict_subset C' C) F)) F.

(* Deletes tautological, repeated and subsumed clauses (Appendix A). *)
Definition normalize (F : ncnf) : ncnf :=
  antichain (sort_clauses (filter (fun C => negb (tautological C)) F)).

Definition has_empty_clause (F : ncnf) : bool :=
  existsb (fun C => match C with [] => true | _ => false end) F.

Definition max_width (F : ncnf) : nat := maxN (map (@length nat) F).

(** ** 3. Disjoint sparsification (Appendix A, Lemma 6.3) *)

(* Γ = 2 (3^(k-1) - 1) *)
Definition spar_Gamma (k : nat) : nat := 2 * (3 ^ (k - 1) - 1).

(* C = 4 Σ_{j=0}^{k-2} (3M)^j bounds the depth of the tree by C n. *)
Definition spar_C (k M : nat) : nat := 4 * sumN (map (fun j => (3 * M) ^ j) (seq 0 (k - 1))).

(* Leaf occurrence bound B = 2 Σ_{j=0}^{k-1} M^j. *)
Definition spar_B (k M : nat) : nat := 2 * sumN (map (fun j => M ^ j) (seq 0 k)).

(* Test powers of two M >= Γ in increasing order until Γ ⌈log2 (4 C M)⌉ <= σ M,
   with σ = 1/s. The fuel is far more than the O(log(sΓk)) doublings needed. *)
Fixpoint spar_M_search (fuel k s M : nat) : nat :=
  match fuel with
  | 0 => M
  | S fuel' =>
      if s * spar_Gamma k * clog2 (4 * spar_C k M * M) <=? M then M
      else spar_M_search fuel' k s (2 * M)
  end.

Definition spar_M (k s : nat) : nat :=
  spar_M_search (s + spar_Gamma k + k + 64) k s (2 ^ clog2 (spar_Gamma k)).

(* deg_c(H) = #{C ∈ F : |C| = c, H ⊆ C} *)
Definition deg_c (F : ncnf) (c : nat) (H : nclause) : nat :=
  length (filter (fun C => (length C =? c) && subsetN H C) F).

(* The branching rule: a nonempty proper subset H of a width-c clause with
   deg_c(H) >= M^(c-|H|), with the smallest c, then the largest |H|, then the
   first clause and subset in enumeration order. *)
Definition find_branch (k M : nat) (F : ncnf) : option (nat * nclause) :=
  find_first (fun c =>
    find_first (fun hs =>
      find_first (fun C =>
        if length C =? c then
          find_first (fun H => if M ^ (c - hs) <=? deg_c F c H then Some (c, H) else None)
            (combinations C hs)
        else None) F)
      (rev (seq 1 (c - 1))))
    (seq 2 (k - 1)).

(* F_A = G ∧ H and F_B = G ∧ ⋀_a P_a ∧ ⋀_{ℓ ∈ H} ¬ℓ, both normalised. *)
Definition branch_children (F : ncnf) (c : nat) (H : nclause) : ncnf * ncnf :=
  let selected := fun C => (length C =? c) && subsetN H C in
  let G := filter (fun C => negb (selected C)) F in
  let petals := map (fun C => filter (fun l => negb (memN l H)) C) (filter selected F) in
  (normalize (H :: G), normalize (petals ++ map (fun l => [code_neg l]) H ++ G)).

(* Depth-first traversal of the sparsification tree, adding the counts of the
   leaves. The fuel is the depth bound C n of Lemma A.3, plus one; if it ever
   ran out, the node would be counted by [fallback]. *)
Fixpoint sparsify_fold (fuel k M : nat) (leaf fallback : ncnf -> Z) (F : ncnf) : Z :=
  match fuel with
  | 0 => fallback F
  | S fuel' =>
      match find_branch k M F with
      | None => leaf F
      | Some (c, H) =>
          let '(FA, FB) := branch_children F c H in
          (sparsify_fold fuel' k M leaf fallback FA
           + sparsify_fold fuel' k M leaf fallback FB)%Z
      end
  end.

(** ** 4. Polynomials over F_2 on Boolean inputs *)

(* A monomial is a strictly increasing list of variables (x^2 = x). *)
Definition monomial := list nat.
(* A polynomial is a list of monomials, summed modulo 2. *)
Definition f2poly := list monomial.

(* Inserts a monomial in a sorted polynomial, cancelling it if present. *)
Fixpoint insert_mono (m : monomial) (p : f2poly) : f2poly :=
  match p with
  | [] => [m]
  | m' :: p' =>
      if eqbN m m' then p'
      else if lexltbN m m' then m :: p
      else m' :: insert_mono m p'
  end.

Definition f2_normalize (p : f2poly) : f2poly := fold_right insert_mono [] (map sort_uniq p).

Definition is_zero_poly (p : f2poly) : bool := match p with [] => true | _ => false end.
Definition is_one_poly (p : f2poly) : bool := match p with [[]] => true | _ => false end.

Definition mono_eval (x : list bool) (m : monomial) : bool := forallb (fun v => nth v x false) m.
Definition f2_eval (x : list bool) (p : f2poly) : bool :=
  fold_left (fun b m => xorb b (mono_eval x m)) p false.

Definition count_zeros_bruteforce (n : nat) (eqs : list f2poly) : Z :=
  fold_tuples n [false; true]
    (fun acc x => if forallb (fun p => negb (f2_eval x p)) eqs then (acc + 1)%Z else acc)
    0%Z [].

(* Violation indicator of a clause:
   v_e = Π_{negative} x_v · Π_{positive} (1 + x_v). *)
Definition violation_poly (C : nclause) : f2poly :=
  let negs := map code_var (filter (fun l => negb (code_pos l)) C) in
  let poss := map code_var (filter code_pos C) in
  f2_normalize (fold_sublists poss (fun acc T => sort_uniq (negs ++ T) :: acc) [] []).

(* Substitutes the bits [bits] for the variables [heavy], reduces modulo 2,
   and renumbers the remaining variables 0, 1, ... (Section 5.5). *)
Definition restrict_poly (n : nat) (heavy : list nat) (bits : list bool) (p : f2poly) : f2poly :=
  let free := filter (fun v => negb (memN v heavy)) (range n) in
  f2_normalize (flat_map (fun m =>
    if existsb (fun v => memN v heavy && negb (nth (indexN v heavy) bits false)) m then []
    else [map (fun v => indexN v free) (filter (fun v => negb (memN v heavy)) m)]) p).

Definition eq_scope (p : f2poly) : list nat := sort_uniq (concat p).

Definition occurrences (v : nat) (scopes : list (list nat)) : nat :=
  length (filter (memN v) scopes).

Definition max_degree (eqs : list f2poly) : nat :=
  maxN (map (fun p => maxN (map (@length nat) p)) eqs).

(** ** 5. Rational arithmetic and truncated polynomials *)

Definition qadd (a b : Q) : Q := Qred (a + b).
Definition qsub (a b : Q) : Q := Qred (a - b).
Definition qmul (a b : Q) : Q := Qred (a * b).
Definition qdiv (a b : Q) : Q := Qred (a / b).
Definition qneg (a : Q) : Q := Qred (- a).
Definition qofZ (z : Z) : Q := inject_Z z.
Definition qofN (n : nat) : Q := inject_Z (Z.of_nat n).
Definition qeqb (a b : Q) : bool := Qeq_bool a b.
Definition qltb (a b : Q) : bool := negb (Qle_bool b a).
Definition qsum (l : list Q) : Q := fold_left qadd l 0%Q.

(* Vectors of rationals. *)
Definition vzero (D : nat) : list Q := repeat 0%Q D.
Definition vunit (D w : nat) : list Q := map (fun y => if y =? w then 1%Q else 0%Q) (range D).
Definition vadd (u v : list Q) : list Q := zipWith qadd u v.
Definition vsub (u v : list Q) : list Q := zipWith qsub u v.
Definition vscale (c : Q) (u : list Q) : list Q := map (qmul c) u.

Definition dotQ (row : list Q) (x : list bool) : Q :=
  qsum (zipWith (fun (c : Q) (b : bool) => if b then c else 0%Q) row x).
Definition dotZ (row : list Z) (x : list bool) : Z :=
  sumZ (zipWith (fun (c : Z) (b : bool) => if b then c else 0%Z) row x).

(* Univariate polynomials over Q, ascending coefficients, implicit zeros. *)
Definition qpoly := list Q.

Fixpoint padd (p q : qpoly) : qpoly :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => qadd a b :: padd p' q'
  end.

Definition pscale (c : Q) (p : qpoly) : qpoly := map (qmul c) p.
Definition psub (p q : qpoly) : qpoly := padd p (pscale (-1)%Q q).

Fixpoint pmul (p q : qpoly) : qpoly :=
  match p with
  | [] => []
  | a :: p' => padd (pscale a q) (0%Q :: pmul p' q)
  end.

(* Multiplication modulo z^J. *)
Definition pmul_trunc (J : nat) (p q : qpoly) : qpoly := firstn J (pmul p q).

Definition peval (p : qpoly) (x : Q) : Q := fold_right (fun a acc => qadd a (qmul x acc)) 0%Q p.

(* p(t + z) modulo z^J, by Horner's rule. *)
Definition pshift (J : nat) (t : Q) (p : qpoly) : qpoly :=
  fold_right (fun a acc => padd [a] (pmul_trunc J [t; 1%Q] acc)) [] p.

(** ** 6. The parity lift (Lemma 5.1) *)

Definition zpoly := list Z.

Fixpoint zpadd (p q : zpoly) : zpoly :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b)%Z :: zpadd p' q'
  end.

Fixpoint zpmul (p q : zpoly) : zpoly :=
  match p with
  | [] => []
  | a :: p' => zpadd (map (Z.mul a) q) (0%Z :: zpmul p' q)
  end.

(* Binomial coefficient, by the exact product formula. *)
Definition binomZ (n k : nat) : Z :=
  if n <? k then 0%Z
  else fold_left (fun acc i => (acc * Z.of_nat (n - k + i) / Z.of_nat i)%Z) (seq 1 k) 1%Z.

(* p_ℓ(Y) = (1 - Y)^ℓ Σ_{j<ℓ} binom(ℓ+j-1, j) Y^j, which is 1 modulo 2^ℓ on
   even integers and 0 on odd ones. *)
Definition parity_poly (l : nat) : zpoly :=
  zpmul (Nat.iter l (zpmul [1%Z; (-1)%Z]) [1%Z])
        (map (fun j => binomZ (l + j - 1) j) (seq 0 l)).

(* Division by the monic h(Y) = Y^2 - Y. With suffix sums t_i = Σ_{i'>=i} c_i',
   the quotient is Σ_i t_{i+2} Y^i and the remainder is c_0 + t_1 Y. *)
Definition suffix_sums (cs : zpoly) : zpoly :=
  fold_right (fun c acc => match acc with [] => [c] | t :: _ => (c + t)%Z :: acc end) [] cs.

Definition divmod_h (cs : zpoly) : zpoly * (Z * Z) :=
  let ts := suffix_sums cs in (skipn 2 ts, (nth 0 cs 0%Z, nth 1 ts 0%Z)).

Fixpoint lift_coeffs_aux (fuel : nat) (p : zpoly) : list (Z * Z) :=
  match fuel with
  | 0 => []
  | S fuel' => let '(q, e) := divmod_h p in e :: lift_coeffs_aux fuel' q
  end.

(* e_0, ..., e_{ℓ-1}, with e_j(Y) = a_j + b_j Y and p_ℓ = Σ_j e_j h^j.
   Since deg p_ℓ < 2ℓ, ℓ successive divisions suffice. *)
Definition lift_coeffs (l : nat) : list (Z * Z) := lift_coeffs_aux l (parity_poly l).

(** ** 7. The coefficient ring Q[z]/(z^J) `V`/(V^ℓ) *)

(* Element Σ_s a_s V^s, stored as the list of the truncated polynomials a_s(z). *)
Definition rv := list qpoly.

Definition rv_zero : rv := [].
Definition rv_one : rv := [[1%Q]].

Fixpoint rv_add (a b : rv) : rv :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: a', y :: b' => padd x y :: rv_add a' b'
  end.

Definition rv_scale (c : Q) (a : rv) : rv := map (pscale c) a.

Fixpoint rv_mul_aux (J : nat) (a b : rv) : rv :=
  match a with
  | [] => []
  | x :: a' => rv_add (map (pmul_trunc J x) b) ([] :: rv_mul_aux J a' b)
  end.

Definition rv_mul (J l : nat) (a b : rv) : rv := firstn l (rv_mul_aux J a b).

Definition rv_coeff (a : rv) (s j : nat) : Q := nth j (nth s a []) 0%Q.

(* The lifted factor B(L) = Σ_{j<ℓ} e_j(L) h(L)^j V^j of equation (5.4). *)
Definition lifted_factor (J : nat) (es : list (Z * Z)) (L : qpoly) : rv :=
  let hL := pmul_trunc J L (psub L [1%Q]) in
  let fix go (es : list (Z * Z)) (hpow : qpoly) : rv :=
    match es with
    | [] => []
    | (a, b) :: es' =>
        pmul_trunc J (padd [qofZ a] (pscale (qofZ b) L)) hpow :: go es' (pmul_trunc J hpow hL)
    end in
  go es [1%Q].

(* Integer lift L(θ) = Σ_{monomials} Π_{v ∈ monomial} θ_v of an equation. *)
Definition lift_eval (J : nat) (p : f2poly) (theta : nat -> qpoly) : qpoly :=
  fold_left padd (map (fun m => fold_left (fun acc v => pmul_trunc J acc (theta v)) m [1%Q]) p) [].

(** ** 8. Low-degree replacement forms (Section 4) *)

Record params := mkParams {
  p_r : nat;    (* number of groups r *)
  p_pts : nat;  (* number of evaluation points Q *)
  p_R : nat;    (* degree parameter R *)
  p_A0 : nat    (* parity interval I = {A0, ..., A0 + R - 1} *)
}.

(* K = r^Q sequences in [r]^Q; labels u = (a_u, d_u) are coded a_u K + d_u. *)
Definition p_K (pr : params) : nat := p_r pr ^ p_pts pr.
Definition p_D (pr : params) : nat := p_K pr * p_K pr.

(* Entry t ∈ {1..Q} of the sequence coded by a. *)
Definition digit (r t a : nat) : nat := (a / r ^ (t - 1)) mod r.
Definition set_digit (r t a g : nat) : nat := a - digit r t a * r ^ (t - 1) + g * r ^ (t - 1).

Definition lab_a (K u : nat) : nat := u / K.
Definition lab_d (K u : nat) : nat := u mod K.

(* ϑ_s exchanges the entries a_u(s) and d_u(s). *)
Definition swap_pos (r K s u : nat) : nat :=
  let a := lab_a K u in
  let d := lab_d K u in
  set_digit r s a (digit r s d) * K + set_digit r s d (digit r s a).

(* The composition of all ϑ_s exchanges a_u and d_u. *)
Definition swap_all (K u : nat) : nat := lab_d K u * K + lab_a K u.

(* Eigenbasis of the exchange of a pair in [r]^2 (proof of Lemma 4.1). *)
Inductive pair_eig := Diag (a : nat) | Sym (a d : nat) | Anti (a d : nat).

Definition eig_entry (e : pair_eig) (x y : nat) : Z :=
  match e with
  | Diag a => if (x =? a) && (y =? a) then 1%Z else 0%Z
  | Sym a d => if ((x =? a) && (y =? d)) || ((x =? d) && (y =? a)) then 1%Z else 0%Z
  | Anti a d => if (x =? a) && (y =? d) then 1%Z else if (x =? d) && (y =? a) then (-1)%Z else 0%Z
  end.

Definition eig_negative (e : pair_eig) : bool := match e with Anti _ _ => true | _ => false end.

Definition pair_eigenbasis (r : nat) : list pair_eig :=
  map Diag (range r)
  ++ flat_map (fun a => map (Sym a) (seq (S a) (r - S a))) (range r)
  ++ flat_map (fun a => map (Anti a) (seq (S a) (r - S a))) (range r).

Definition in_interval (pr : params) (j : nat) : bool :=
  (p_A0 pr <=? j) && (j <? p_A0 pr + p_R pr).

(* Lemma 4.1: the rows of C^B are the product eigenvectors ψ whose number j
   of antisymmetric factors lies outside I. *)
Definition aux_measurements (pr : params) : list (list Z) :=
  let r := p_r pr in
  let pts := p_pts pr in
  let K := p_K pr in
  rev (fold_tuples pts (pair_eigenbasis r) (fun rows es =>
    if in_interval pr (length (filter eig_negative es)) then rows
    else map (fun u => fold_left Z.mul
                 (zipWith (fun s e => eig_entry e (digit r s (lab_a K u)) (digit r s (lab_d K u)))
                    (seq 1 pts) es) 1%Z)
             (range (K * K)) :: rows) [] []).

(* Row vector times W_0 = 1/2 Σ_s (I - Π_s), using (v Π_s)[y] = v[ϑ_s y]. *)
Definition times_W0 (pr : params) (v : list Q) : list Q :=
  let r := p_r pr in
  let K := p_K pr in
  map (fun y => qmul (1 # 2) (qsum (map (fun s => qsub (nth y v 0%Q) (nth (swap_pos r K s y) v 0%Q))
                                       (seq 1 (p_pts pr)))))
      (range (K * K)).

(* Row w of f_I(W_0), where
   f_I(z) = (-1)^A0 Σ_{j<R} (-2)^j binom(z - A0, j) (equation (4.7)),
   using binom(W - A0, j+1) = binom(W - A0, j) (W - A0 - j) / (j+1). *)
Definition fW0_row (pr : params) (w : nat) : list Q :=
  let D := p_D pr in
  let A0 := p_A0 pr in
  let step := fun (st : list Q * list Q) (j : nat) =>
    let '(rho, acc) := st in
    (vscale (1 # Pos.of_nat (S j)) (vsub (times_W0 pr rho) (vscale (qofN (A0 + j)) rho)),
     vadd acc (vscale (qofZ ((-2) ^ Z.of_nat j)%Z) rho)) in
  vscale (qofZ ((-1) ^ Z.of_nat A0)%Z) (snd (fold_left step (seq 0 (p_R pr)) (vunit D w, vzero D))).

(* φ_{u,y}(T) = Π_{s ∈ E_{u,y}} (1 - T/s), E_{u,y} = {s : a_y(s) ≠ d_u(s)}. *)
Definition phi_poly (pr : params) (u y : nat) : qpoly :=
  let r := p_r pr in
  let K := p_K pr in
  fold_left (fun acc s =>
      if digit r s (lab_a K y) =? digit r s (lab_d K u) then acc
      else pmul acc [1%Q; Qmake (-1) (Pos.of_nat s)])
    (seq 1 (p_pts pr)) [1%Q].

(* The auxiliary row P_u(T) = δ_u (I - M_0) + Σ_y M_0[u,y] φ_{u,y}(T) δ_y
   (equation (4.10)), with M_0 = V_0 f_I(W_0), so that row u of M_0 is row
   ϑ(u) of f_I(W_0). One polynomial in T per auxiliary coordinate. *)
Definition aux_row (pr : params) (u : nat) : list qpoly :=
  let K := p_K pr in
  let m0 := fW0_row pr (swap_all K u) in
  map (fun y =>
      let m := nth y m0 0%Q in
      let base := if y =? u then qsub 1%Q m else qneg m in
      if qeqb m 0%Q then [base] else padd [base] (pscale m (phi_poly pr u y)))
    (range (K * K)).

(* The incidences (f, v), v ∈ I_f, in factor order. *)
Definition incidences (scopes : list (list nat)) : list (nat * nat) :=
  flat_map (fun '(f, scope) => map (fun v => (f, v)) scope) (combine (range (length scopes)) scopes).

(* Probability that two labels agree, when unfixed ones are uniform on K values. *)
Definition prob_same (K : nat) (same : bool) (x y : option nat) : Q :=
  if same then 1%Q
  else match x, y with
       | Some a, Some b => if a =? b then 1%Q else 0%Q
       | _, _ => Qmake 1 (Pos.of_nat K)
       end.

Definition opt_digit (r t : nat) (x : option nat) : option nat :=
  match x with Some a => Some (digit r t a) | None => None end.

(* Conditional expectation of Φ/(M(b+w)) + Ξ/(Q n) (proof of Lemma 4.5). *)
Definition label_potential (pr : params) (n b w : nat) (inc : list (nat * nat))
  (aopt dopt : list (option nat)) : Q :=
  let r := p_r pr in
  let pts := p_pts pr in
  let K := p_K pr in
  let M := length inc in
  let Phi := qsub (qsum (flat_map (fun '(f, v) => map (fun '(f', v') =>
                   qmul (prob_same K (v =? v') (nth v aopt None) (nth v' aopt None))
                        (prob_same K (f =? f') (nth f dopt None) (nth f' dopt None))) inc) inc))
                  (Qmake (Z.of_nat (M * M)) (Pos.of_nat (p_D pr))) in
  let Xi := qsub (qsum (flat_map (fun t => flat_map (fun v => map (fun v' =>
                   prob_same r (v =? v') (opt_digit r t (nth v aopt None))
                                         (opt_digit r t (nth v' aopt None)))
                   (range n)) (range n)) (seq 1 pts)))
                 (Qmake (Z.of_nat (pts * n * n)) (Pos.of_nat r)) in
  qadd (qdiv Phi (qofN (M * (b + w)))) (qdiv Xi (qofN (pts * n))).

(* First candidate minimising [cost]. *)
Definition argmin_first (cands : list nat) (cost : nat -> Q) : nat :=
  match cands with
  | [] => 0
  | c0 :: cs =>
      fst (fold_left (fun (best : nat * Q) c =>
             let cc := cost c in if qltb cc (snd best) then (c, cc) else best)
             cs (c0, cost c0))
  end.

Definition unopt (x : option nat) : nat := match x with Some a => a | None => 0 end.

(* Lemma 4.5: fix a_v for every variable, then d_f for every factor with
   nonempty scope, each time choosing a value that minimises the conditional
   expectation. Factors with empty scope get the constant sequence 0. *)
Definition choose_labels (pr : params) (n b w : nat) (scopes : list (list nat))
  : list nat * list nat :=
  let K := p_K pr in
  let inc := incidences scopes in
  let a0 := repeat (@None nat) n in
  let d0 := map (fun scope => match scope with [] => Some 0 | _ => None end) scopes in
  let afin := fold_left (fun aopt v =>
      set_nth aopt v (Some (argmin_first (range K)
        (fun c => label_potential pr n b w inc (set_nth aopt v (Some c)) d0))))
      (range n) a0 in
  let dfin := fold_left (fun dopt f =>
      match nth f dopt None with
      | Some _ => dopt
      | None => set_nth dopt f (Some (argmin_first (range K)
                  (fun c => label_potential pr n b w inc afin (set_nth dopt f (Some c)))))
      end) (range (length scopes)) d0 in
  (map unopt afin, map unopt dfin).

(* c(f,v): the number of earlier incidences with the same label. *)
Definition assign_copies (labels : list nat) : list nat :=
  rev (fst (fold_left (fun (st : list nat * list nat) u =>
                         let '(acc, seen) := st in (countN u seen :: acc, u :: seen))
                      labels ([], []))).

Record design := mkDesign {
  ds_avar : list nat;           (* a_v, coded in [0, K) *)
  ds_dfac : list nat;           (* d_f, coded in [0, K) *)
  ds_inc : list (nat * nat);    (* the incidences (f, v) *)
  ds_rows : list (list qpoly);  (* P_{f,v}(T) for each incidence, as rows over [n] *)
  ds_meas : list (list Z)       (* the matrix Ĉ, as rows over [n] *)
}.

(* Section 4.5: transfer of the auxiliary rows and measurements to the actual
   variables, using h copies of the auxiliary coordinates (equations (4.14) and
   (4.15)). Then S_{t,g} = {v : a_v(t) = g} and σ_f(t) = d_f(t). *)
Definition design_of_labels (pr : params) (n : nat) (scopes : list (list nat))
  (avar dfac : list nat) : design :=
  let K := p_K pr in
  let inc := incidences scopes in
  let labels := map (fun '(f, v) => nth v avar 0 * K + nth f dfac 0) inc in
  let copies := assign_copies labels in
  let h := S (maxN copies) in
  let idx := range (length inc) in
  let same_slot := fun c v' i => (nth i copies 0 =? c) && (snd (nth i inc (0, 0)) =? v') in
  let rows := map (fun i =>
      let aux := aux_row pr (nth i labels 0) in
      let c := nth i copies 0 in
      map (fun v' => fold_left padd (map (fun i' => nth (nth i' labels 0) aux [])
                                         (filter (same_slot c v') idx)) [])
          (range n)) idx in
  let CB := aux_measurements pr in
  let meas := flat_map (fun c => map (fun row =>
      map (fun v' => sumZ (map (fun i' => nth (nth i' labels 0) row 0%Z) (filter (same_slot c v') idx)))
          (range n)) CB) (range h) in
  mkDesign avar dfac inc rows meas.

(* Lemma 4.7: the design for the given scopes. *)
Definition build_design (pr : params) (n b w : nat) (scopes : list (list nat)) : design :=
  let '(avar, dfac) := choose_labels pr n b w scopes in
  design_of_labels pr n scopes avar dfac.

(** ** 9. The counting routine (Section 3) *)

Definition group_vars (pr : params) (d : design) (n t g : nat) : list nat :=
  filter (fun v => digit (p_r pr) t (nth v (ds_avar d) 0) =? g) (range n).

Definition factor_group (pr : params) (d : design) (t f : nat) : nat :=
  digit (p_r pr) t (nth f (ds_dfac d) 0).

Fixpoint find_inc (inc : list (nat * nat)) (f v : nat) : nat :=
  match inc with
  | [] => 0
  | (f', v') :: inc' => if (f =? f') && (v =? v') then 0 else S (find_inc inc' f v)
  end.

(* For each incidence: P_{f,v}(t) and P_{f,v}(t + z) modulo z^J. *)
Definition point_rows (J t : nat) (d : design) : list (list Q) * list (list qpoly) :=
  (map (map (fun p => peval p (qofN t))) (ds_rows d),
   map (map (pshift J (qofN t))) (ds_rows d)).

(* The fixed corrections ⟨P_{f,v}(t+z) - P_{f,v}(t), 1_U⟩, one per incidence. *)
Definition corrections (U : list nat) (Pt : list (list Q)) (Pz : list (list qpoly)) : list qpoly :=
  zipWith (fun pt pz => fold_left padd (map (fun v => psub (nth v pz []) [nth v pt 0%Q]) U) [])
          Pt Pz.

(* A_{g,U}(x; z): product of the factors assigned to group g at point t, with
   inputs ⟨P_{f,v}(t), x⟩ + correction (equation (3.11)). The factors with
   index >= length eqs are the neutral ones, equal to 1. *)
Definition group_value (J l : nat) (es : list (Z * Z)) (eqs : list f2poly) (pr : params)
  (d : design) (t g : nat) (Pt : list (list Q)) (Delta : list qpoly) (x : list bool) : rv :=
  let inc := ds_inc d in
  fold_left (fun acc f =>
      if negb (factor_group pr d t f =? g) then acc
      else if length eqs <=? f then acc
      else
        let theta := fun v => let i := find_inc inc f v in
                              padd [dotQ (nth i Pt []) x] (nth i Delta []) in
        rv_mul J l acc (lifted_factor J es (lift_eval J (nth f eqs []) theta)))
    (range (length (ds_dfac d))) rv_one.

(* Lemma 3.2: Σ_{x ∈ {0,1}^n, x_i = 1 (i ∈ E)} Π_g A_g(x), by enumerating all
   measurement tuples y ∈ Π_g {-D..D}^(c_g), finding representatives x̄_g with
   C_g x̄_g = y_g, and summing each group separately. Group assignments are
   stored as vectors over [n], zero outside the group, so that C_g u = Ĉ u. *)
Definition separated_sum (J l n D r : nat) (meas : list (list Z)) (groups : list (list nat))
  (E : list nat) (A : nat -> list bool -> rv) : rv :=
  let c := length meas in
  let measure := fun x => map (fun row => dotZ row x) meas in
  let eqZ := fun (a b : list Z) => forallb (fun '(p, q) => Z.eqb p q) (combine a b) in
  let gs := combine (range r) groups in
  fold_tuples (r * c) (zinterval D) (fun acc ys =>
    let yv := chunks c r ys in
    let reps := map (fun '(g, Sg) =>
        find_tuple (length Sg) [false; true]
          (fun bits => eqZ (measure (embed n Sg bits)) (nth g yv [])) []) gs in
    if existsb (fun o => match o with None => true | Some _ => false end) reps then acc
    else
      let xbars := zipWith (fun Sg o => embed n Sg (match o with Some bits => bits | None => [] end))
                           groups reps in
      let prod := fold_left (fun p '(g, Sg) =>
          let others := fold_left (fun x '(h, xh) => if h =? g then x else zipWith orb x xh)
                                  (combine (range r) xbars) (repeat false n) in
          let s := fold_tuples (length Sg) [false; true] (fun s bits =>
              let u := embed n Sg bits in
              if eqZ (measure u) (nth g yv [])
                 && forallb (fun i => negb (memN i Sg) || nth i u false) E
              then rv_add s (A g (zipWith orb u others)) else s) rv_zero [] in
          rv_mul J l p s) gs rv_one in
      rv_add acc prod) rv_zero [].

(* Equation (3.13): H(t + z) modulo z^J, as the signed sum over U ⊆ E ⊆ [n],
   |E| <= q, of the restricted sums with fixed substitution X = 1_U. *)
Definition taylor_at (pr : params) (d : design) (n l J q : nat) (es : list (Z * Z))
  (eqs : list f2poly) (t : nat) : rv :=
  let r := p_r pr in
  let '(Pt, Pz) := point_rows J t d in
  let groups := map (group_vars pr d n t) (range r) in
  fold_left (fun acc s =>
      fold_combinations (range n) s (fun acc E =>
        fold_sublists E (fun acc U =>
          let Delta := corrections U Pt Pz in
          let A := fun g x => group_value J l es eqs pr d t g Pt Delta x in
          let sign := if Nat.even (length E - length U) then 1%Q else (-1)%Q in
          rv_add acc (rv_scale sign (separated_sum J l n (p_D pr) r (ds_meas d) groups E A)))
          acc [])
        acc [])
    (seq 0 (S (Nat.min q n))) rv_zero.

(** ** 10. Hermite interpolation (Appendix B.3) *)

Fixpoint find_pivot (m : list (list Q)) (i : nat) : option nat :=
  match m with
  | [] => None
  | row :: m' => if qeqb (hd 0%Q row) 0%Q then find_pivot m' (S i) else Some i
  end.

(* Determinant by Gaussian elimination; the fuel is the dimension. *)
Fixpoint det_aux (fuel : nat) (m : list (list Q)) : Q :=
  match fuel with
  | 0 => 1%Q
  | S fuel' =>
      match m with
      | [] => 1%Q
      | _ =>
          match find_pivot m 0 with
          | None => 0%Q
          | Some i =>
              let prow := nth i m [] in
              let p := hd 0%Q prow in
              let reduced := map (fun row => tl (vsub row (vscale (qdiv (hd 0%Q row) p) prow)))
                                 (remove_nth m i) in
              qmul (qmul (if Nat.even i then 1%Q else (-1)%Q) p) (det_aux fuel' reduced)
          end
      end
  end.

Definition det (m : list (list Q)) : Q := det_aux (length m) m.

(* Rows (t, j), t ∈ [Q], j < J; columns u < QJ: binom(u, j) t^(u-j). *)
Definition hermite_matrix (pts J : nat) : list (list Q) :=
  flat_map (fun t => map (fun j => map (fun u =>
      if j <=? u then qofZ (binomZ u j * Z.of_nat t ^ Z.of_nat (u - j))%Z else 0%Q)
      (range (pts * J))) (range J)) (seq 1 pts).

(* The constant coefficient of the interpolant, by Cramer's rule (eq. (B.1)),
   given the Hermite matrix V and its determinant. *)
Definition hermite_value_at_0 (V : list (list Q)) (detV : Q) (data : list Q) : Q :=
  qdiv (det (zipWith (fun row y => y :: tl row) V data)) detV.

(* The factor scopes: one per equation, then a neutral factor {v} per variable. *)
Definition factor_scopes (n : nat) (eqs : list f2poly) : list (list nat) :=
  map eq_scope eqs ++ map (fun v => [v]) (range n).

(* Proposition 5.3 with a supplied design: computes H(t + z) mod z^J at every
   point, interpolates each V-coefficient at 0, adds them, and reduces modulo
   2^ℓ (equation (5.5)). *)
Definition count_from_design (pr : params) (d : design) (n k l : nat) (es : list (Z * Z))
  (eqs : list f2poly) : Z :=
  let pts := p_pts pr in
  let dH := k * p_R pr * (length eqs + 2 * (l - 1)) in
  let J := dH / pts + 1 in
  let H := map (taylor_at pr d n l J (J - 1) es eqs) (seq 1 pts) in
  (* The same Hermite matrix serves the ℓ coordinates (Appendix B.3). *)
  let V := hermite_matrix pts J in
  let detV := det V in
  let u := qsum (map (fun s => hermite_value_at_0 V detV
                         (flat_map (fun Ht => map (rv_coeff Ht s) (range J)) H))
                     (range l)) in
  Z.modulo (Qfloor u) (2 ^ Z.of_nat l).

Definition count_with_design (pr : params) (n k l : nat) (es : list (Z * Z))
  (eqs : list f2poly) (b w : nat) : Z :=
  count_from_design pr (build_design pr n b w (factor_scopes n eqs)) n k l es eqs.

(** ** 11. Counting common zeros of sparse equations (Section 5) *)

(* Smallest β >= 1 with b, w <= λ^β (the fuel bounds β). *)
Fixpoint find_beta (fuel lam b w beta : nat) : nat :=
  match fuel with
  | 0 => beta
  | S fuel' =>
      if (b <=? lam ^ beta) && (w <=? lam ^ beta) then beta
      else find_beta fuel' lam b w (S beta)
  end.

(* Lemma 4.8, with all its numerical checks performed exactly. *)
Definition choose_params (n M b w : nat) : option params :=
  let lam := clog2 n in
  let nu := clog2 lam in
  let beta := find_beta (b + w + 1) lam b w 1 in
  let r := Nat.sqrt lam / nu ^ 2 in
  let pts := lam / (128 * nu) in
  let R := (beta + 3) * csqrt lam in
  if (r <? 2) || (pts <=? R) then None
  else
    let D := r ^ (2 * pts) in
    let A0 := ((Z.of_nat (pts * (r - 1)) - Z.of_nat (r * (R - 1))) / Z.of_nat (2 * r))%Z in
    (* (2r)^Q Pr[Bin(Q, (r-1)/(2r)) ∉ I] *)
    let tail := sumZ (map (fun j =>
        if (A0 <=? Z.of_nat j)%Z && (Z.of_nat j <? A0 + Z.of_nat R)%Z then 0%Z
        else (binomZ pts j * Z.of_nat (r - 1) ^ Z.of_nat j * Z.of_nat (r + 1) ^ Z.of_nat (pts - j))%Z)
        (seq 0 (S pts))) in
    if (0 <=? A0)%Z && (A0 + Z.of_nat R - 1 <=? Z.of_nat pts)%Z
       && (2 * (b + w) * D * D <=? M) && (2 * pts * r * r <=? n)
       && (32 <=? R) && (6 * R <=? pts)
       && (tail * Z.of_nat (b * r * r * lam) <=? Z.of_nat (2 * r) ^ Z.of_nat pts)%Z
    then Some (mkParams r pts R (Z.to_nat A0))
    else None.

(* One branch of the proof of Theorem 2.2: fixes the heavy variables, then
   counts the completions with the design of Section 4. [None] means that a
   numerical check failed. *)
Definition count_branch (k n l : nat) (es : list (Z * Z)) (heavy : list nat)
  (eqs : list f2poly) (bits : list bool) : option Z :=
  let n' := n - length heavy in
  let eqs' := map (restrict_poly n heavy bits) eqs in
  if existsb is_one_poly eqs' then Some 0%Z
  else
    match filter (fun p => negb (is_zero_poly p)) eqs' with
    | [] => Some (2 ^ Z.of_nat n')%Z
    | eqs'' =>
        let scopes := factor_scopes n' eqs'' in
        let M := sumN (map (@length nat) scopes) in
        let b := maxN (map (fun v => occurrences v scopes) (range n')) in
        let w := maxN (map (@length nat) scopes) in
        match choose_params n' M b w with
        | None => None
        | Some pr => Some (count_with_design pr n' k l es eqs'' b w)
        end
    end.

(* Theorem 2.2: the number of common zeros in {0,1}^n of equations of degree at
   most k. Variables in more than b_0 scopes are branched on; if a check fails
   on some branch, the original system is checked on all 2^n assignments. *)
Definition count_zeros (k n : nat) (eqs0 : list f2poly) : Z :=
  let eqs1 := map f2_normalize eqs0 in
  if existsb is_one_poly eqs1 then 0%Z
  else
    match filter (fun p => negb (is_zero_poly p)) eqs1 with
    | [] => (2 ^ Z.of_nat n)%Z
    | eqs =>
        if n <? 20 then count_zeros_bruteforce n eqs
        else
          let l := S n in
          let es := lift_coeffs l in
          let scopes := factor_scopes n eqs in
          let M := sumN (map (@length nat) scopes) in
          let b0 := ceil_div M n * csqrt (clog2 n) in
          let heavy := filter (fun v => b0 <? occurrences v scopes) (range n) in
          let kdeg := Nat.max k (max_degree eqs) in
          match fold_tuples (length heavy) [false; true] (fun acc bits =>
                  match acc with
                  | None => None
                  | Some z =>
                      match count_branch kdeg n l es heavy eqs bits with
                      | None => None
                      | Some c => Some (z + c)%Z
                      end
                  end) (Some 0%Z) [] with
          | Some z => z
          | None => count_zeros_bruteforce n eqs
          end
    end.

(** ** 12. From a sparse formula to sparse equations (Section 6) *)

(* The parameters of Lemma 6.1: μ = ⌊log2 m⌋ + 1, the bias ε = 1/(200 B μ) of
   the shifts and the relative distance δ = 1/(100 B μ) of the local code,
   represented by their inverses. *)
Definition log_size (m : nat) : nat := S (Nat.log2 m).
Definition eps_inv (m B : nat) : nat := 200 * B * log_size m.
Definition delta_inv (m B : nat) : nat := 100 * B * log_size m.

(* P = 1/(δ(δ - ε)) = 20000 B^2 μ^2, since δ - ε = ε: every nonzero word
   accepted by the checks has weight at least m/P. *)
Definition dist_denom (m B : nat) : nat := delta_inv m B * eps_inv m B.

(* D_0 = 8 μ / ε^2 = 320000 B^2 μ^3, the degree making random shifts ε-biased
   with positive probability (as [SparseCode.degreeBound] in Lean). *)
Definition degree_bound (m B : nat) : nat := 8 * eps_inv m B ^ 2 * log_size m.

Lemma dist_denom_eq (m B : nat) :
  dist_denom m B = (100 * 200) * (B * B) * (log_size m * log_size m).
Proof. unfold dist_denom, delta_inv, eps_inv. ring. Qed.

Lemma degree_bound_eq (m B : nat) :
  degree_bound m B = (8 * 200 * 200) * (B * B) * (log_size m * log_size m * log_size m).
Proof. unfold degree_bound, eps_inv. cbn [Nat.pow]. ring. Qed.

Definition parity_bits (len x : nat) : bool :=
  fold_left xorb (map (Nat.testbit x) (range len)) false.

(* ε-bias: |Σ_j (-1)^(b·s_j)| <= ε d_G for every b ≠ 0. *)
Definition walsh_ok (lG dG epsinv : nat) (shifts : list nat) : bool :=
  forallb (fun b =>
      let sum := sumZ (map (fun s => if parity_bits lG (Nat.land b s) then (-1)%Z else 1%Z) shifts) in
      (Z.of_nat epsinv * Z.abs sum <=? Z.of_nat dG)%Z)
    (seq 1 (2 ^ lG - 1)).

(* No nonzero word of weight <= h lies in the kernel of A modulo 2. The words
   are enumerated one at a time, as in the paper's polynomial-space search. *)
Definition kernel_word_free (dG h : nat) (A : list (list bool)) : bool :=
  forallb (fun s =>
      fold_combinations (range dG) s (fun (ok : bool) (wd : list nat) =>
          if ok then existsb (fun row => fold_left xorb (map (fun j => nth j row false) wd) false) A
          else false)
        true [])
    (seq 1 h).

(* Lemma 6.1: parity checks of a shortened Tanner code on a d_G-regular
   bipartite Cayley graph of {0,1}^(ℓ_G). Each row is the list of clause
   indices it contains. The shifts and the local code are found by exhaustive
   search, in enumeration order. *)
Definition tanner_rows (m B : nat) : list (list nat) :=
  let dG := Nat.min m (degree_bound m B) in
  let lG := clog2 (ceil_div m dG) in
  let qG := 2 ^ lG in
  let shifts :=
    if qG =? 1 then repeat 0 dG
    else match find_tuple dG (range qG) (walsh_ok lG dG (eps_inv m B)) [] with
         | Some s => s
         | None => repeat 0 dG
         end in
  let cG := ceil_div dG (8 * B) in
  (* words of weight < δ d_G, i.e. at most ⌈δ d_G⌉ - 1 *)
  let hloc := ceil_div dG (delta_inv m B) - 1 in
  let Aloc :=
    match find_tuple (cG * dG) [false; true] (fun bits => kernel_word_free dG hloc (chunks dG cG bits)) [] with
    | Some bits => chunks dG cG bits
    | None => repeat (repeat false dG) cG
    end in
  let keep := filter (fun e => e <? m) in
  let ports := fun row => filter (fun j => nth j row false) (range dG) in
  flat_map (fun u => map (fun row => keep (map (fun j => u * dG + j) (ports row))) Aloc) (range qG)
  ++ flat_map (fun v => map (fun row =>
         keep (map (fun j => Nat.lxor v (nth j shifts 0) * dG + j) (ports row))) Aloc) (range qG).

(* A test row is a list of pairs (clause index, coefficient bit). *)
Definition hash_row := list (nat * bool).

Definition clause_coeff (row : hash_row) (e : nat) : bool :=
  fold_left (fun acc '(e', c) => if e' =? e then xorb acc c else acc) row false.

(* The equation Σ_{e : (h)_e = 1} v_e(x) = 0 over F_2 (equation (6.1)). *)
Definition row_poly (F : ncnf) (row : hash_row) : f2poly :=
  f2_normalize (flat_map (fun e => if clause_coeff row e then violation_poly (nth e F []) else [])
                         (range (length F))).

(* Lemma 6.2: [rounds] times, append the candidate γ ∈ ([m] × {0,1})^P whose
   system has the fewest common zeros, ties broken by enumeration order. *)
Definition greedy_rows (count0 : list f2poly -> Z) (F : ncnf) (P rounds : nat)
  (A : list hash_row) : list hash_row :=
  let cands := list_prod (range (length F)) [false; true] in
  Nat.iter rounds (fun A =>
      let best := fold_tuples P cands (fun (best : option (hash_row * Z)) gamma =>
          let N := count0 (map (row_poly F) (A ++ [gamma])) in
          match best with
          | None => Some (gamma, N)
          | Some (_, Nb) => if (N <? Nb)%Z then Some (gamma, N) else best
          end) None [] in
      match best with Some (g, _) => A ++ [g] | None => A end) A.

(* Section 6.3: counts one sparse formula whose variables occur at most B
   times, using 3n greedy rows on top of the Tanner checks. *)
Definition count_sparse_formula (k n B : nat) (F : ncnf) : Z :=
  match F with
  | [] => (2 ^ Z.of_nat n)%Z
  | _ =>
      if has_empty_clause F then 0%Z
      else
        let m := length F in
        let A0 := map (map (fun e => (e, true))) (tanner_rows m B) in
        let A := greedy_rows (count_zeros k n) F (dist_denom m B) (3 * n) A0 in
        count_zeros k n (map (row_poly F) A)
  end.

(** ** 13. The algorithm (Proposition 6.4) *)

(* The number of satisfying assignments in {0,1}^n of a k-CNF on the
   variables 0, ..., n-1. *)
Definition count_sat (k n : nat) (F0 : cnf) : Z :=
  let F := normalize (map norm_clause F0) in
  if has_empty_clause F then 0%Z
  else
    match F with
    | [] => (2 ^ Z.of_nat n)%Z
    | _ =>
        if n <? 20 then count_bruteforce n F
        else
          let lam := clog2 n in
          let nu := clog2 lam in
          let s := Nat.sqrt lam / nu ^ 2 in
          if s <? 2 then count_bruteforce n F
          else
            let k' := Nat.max 2 (Nat.max k (max_width F)) in
            let M := spar_M k' s in
            let B := spar_B k' M in
            sparsify_fold (spar_C k' M * n + 1) k' M (count_sparse_formula k' n B)
              (count_bruteforce n) F
    end.

Definition sat (k n : nat) (F : cnf) : bool := (0 <? count_sat k n F)%Z.

(** ** 14. Sanity checks on tiny instances *)

(* The example after Lemma 5.2: p_2(Y) = (1 - Y) + (2Y - 1) h(Y). *)
Example lift_coeffs_2 : lift_coeffs 2 = [(1, -1); (-1, 2)]%Z.
Proof. vm_compute. reflexivity. Qed.

(* p_ℓ(y) ≡ [y even] (mod 2^ℓ), here for ℓ = 4 and y = 0..15. *)
Example parity_lift_4 :
  map (fun y : Z => Z.modulo (sumZ (zipWith (fun (e : Z * Z) (j : nat) =>
                                         ((fst e + snd e * y) * (y * (y - 1)) ^ Z.of_nat j)%Z)
                                      (lift_coeffs 4) (range 4))) 16)
      (map Z.of_nat (range 16))
  = [1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0]%Z.
Proof. vm_compute. reflexivity. Qed.

(* Remark 4.4 (r = Q = R = 2, I = {0, 1}): for u = (00, 11),
   ⟨P_u(T), ζ⟩ = ζ_(00,11) - T/2 ζ_(10,01) - T ζ_(01,10). With digit 1 least
   significant, these labels are 3, 6 and 9, and (11, 00) is 12. *)
Example remark_row :
  let row := aux_row (mkParams 2 2 2 0) 3 in
  map (fun T => map (fun p => Qred (peval p T)) row) [0; 1; 2]%Q
  = [ map (fun y => if y =? 3 then 1%Q else 0%Q) (range 16);
      map (fun y => if y =? 3 then 1%Q else if y =? 6 then (-1#2)%Q
                    else if y =? 9 then (-1)%Q else 0%Q) (range 16);
      map (fun y => if y =? 3 then 1%Q else if y =? 6 then (-1)%Q
                    else if y =? 9 then (-2)%Q else 0%Q) (range 16) ].
Proof. vm_compute. reflexivity. Qed.

(* ... and the measurement ζ_(00,11) - ζ_(10,01) - ζ_(01,10) + ζ_(11,00) is
   the only row of C^B. *)
Example remark_measurement :
  aux_measurements (mkParams 2 2 2 0)
  = [map (fun y => if (y =? 3) || (y =? 12) then 1%Z
                   else if (y =? 6) || (y =? 9) then (-1)%Z else 0%Z) (range 16)].
Proof. vm_compute. reflexivity. Qed.

(* With the same parameters, hand-picked labels a_0 = (0,0), a_1 = (1,0),
   d = (1,1), (0,0), (0,1) for the factors x0 + x1, {x0}, {x1} put the
   incidence (x0 + x1, x0) at the label u = (00, 11) of Remark 4.4, and the
   incidence ({x1}, x1) at (10, 01). The replacement of x0 in x0 + x1 is then
   x0 - T/2 x1, and the only measurement is x0 - x1. *)
Definition forced_design (n : nat) (eqs : list f2poly) (avar dfac : list nat) : design :=
  design_of_labels (mkParams 2 2 2 0) n (factor_scopes n eqs) avar dfac.

Example forced_design_rows :
  let d := forced_design 2 [[[0]; [1]]] [0; 1] [3; 0; 2] in
  ds_meas d = [[1; -1]]%Z
  /\ map (fun T => map (fun p => Qred (peval p T)) (nth 0 (ds_rows d) [])) [0; 1; 2]%Q
     = [[1; 0]; [1; -1#2]; [1; -1]]%Q.
Proof. vm_compute. split; reflexivity. Qed.

(* The whole counting routine of Sections 3-5 against exhaustive search, on
   such designs: x0 + x1 = 0; x0 x1 + 1 = 0; and x0 + x1 = 0, x1 x2 = 0. *)
Example count_from_forced_designs :
  map (fun '(n, k, eqs, avar, dfac) =>
         (count_from_design (mkParams 2 2 2 0) (forced_design n eqs avar dfac) n k (S n)
            (lift_coeffs (S n)) eqs,
          count_zeros_bruteforce n eqs))
      [(2, 1, [[[0]; [1]]], [0; 1], [3; 0; 2]);
       (2, 2, [[[]; [0; 1]]], [0; 1], [3; 0; 2]);
       (3, 2, [[[0]; [1]]; [[1; 2]]], [0; 1; 2], [3; 1; 0; 2; 3])]
  = [(2, 2); (1, 1); (3, 3)]%Z.
Proof. vm_compute. reflexivity. Qed.

(* The same routine with the derandomised labels of Lemma 4.5. *)
Example count_with_design_x0 :
  count_with_design (mkParams 2 2 2 0) 1 1 2 (lift_coeffs 2) [[[0]]] 2 1
  = count_zeros_bruteforce 1 [[[0]]].
Proof. vm_compute. reflexivity. Qed.

Example count_with_design_xor :
  count_with_design (mkParams 2 1 1 0) 2 1 3 (lift_coeffs 3) [[[0]; [1]]] 2 2
  = count_zeros_bruteforce 2 [[[0]; [1]]].
Proof. vm_compute. reflexivity. Qed.

Example count_with_design_and :
  count_with_design (mkParams 2 1 1 0) 2 2 3 (lift_coeffs 3) [[[]; [0; 1]]] 2 2
  = count_zeros_bruteforce 2 [[[]; [0; 1]]].
Proof. vm_compute. reflexivity. Qed.

(* Greedy parity tests (Lemma 6.2) with list length P = 2 instead of
   20000 B^2 μ^2, and exhaustive zero counting: after 3n rounds, the common
   zeros are exactly the satisfying assignments. *)
Example greedy_rows_small :
  let F := normalize [[1; 3]; [0; 5]; [2; 4]] in
  let A := greedy_rows (count_zeros_bruteforce 3) F 2 9
             (map (map (fun e => (e, true))) (tanner_rows (length F) 1)) in
  count_zeros_bruteforce 3 (map (row_poly F) A) = count_bruteforce 3 F.
Proof. vm_compute. reflexivity. Qed.

(* A small 3-CNF on 6 variables. *)
Definition example_cnf : cnf :=
  map (map (fun '(v, p) => mkLit v p))
    [[(0, true); (1, true); (2, false)]; [(0, true); (1, true); (3, true)];
     [(0, true); (1, true); (4, false)]; [(0, true); (2, true); (5, true)];
     [(1, false); (3, false); (5, true)]; [(2, true); (4, true); (5, false)]].

(* Sparsification with M = 2 partitions the satisfying assignments, and it
   does branch on this formula. *)
Example sparsify_partition :
  let F := normalize (map norm_clause example_cnf) in
  sparsify_fold (spar_C 3 2 * 6 + 1) 3 2 (count_bruteforce 6) (count_bruteforce 6) F
  = count_spec 6 example_cnf
  /\ find_branch 3 2 F <> None.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(* Below the cutoff the algorithm is exhaustive search. *)
Example count_sat_small : count_sat 3 6 example_cnf = count_spec 6 example_cnf.
Proof. vm_compute. reflexivity. Qed.
