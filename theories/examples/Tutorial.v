(** * Tutorial: proving complexity bounds

    This file is a set of exercises. Each one states a complexity bound for
    a function, with 0 in place of its constants, and ends with [Abort]. To
    do an exercise, replace the 0s by constants for which the bound holds,
    and [Abort] by a proof that ends with [Qed]. The comments explain the
    method and the tactics. The sections get harder as they go: functions without
    recursion, recursive functions, mutually recursive functions, then
    bounds in the sizes of the arguments.

    ** The cost model

    The functions are analysed in the standard time cost model
    ([TimeCostModel]). A function is compiled to combinators, and each
    application of a combinator, a constructor or a case analysis costs one
    step. This file is a module over [TimeStdlib]: the time cost model with
    the bounds of the standard library ([Nat.add], [Nat.mul], [length], ...),
    which are used when your functions call them.

    ** Reading a bound

    [Time.ComplexityBound f c] says that [c] bounds the cost of [f]. For a
    function of one argument, [c] is a function [fun cn => k ⋉ r]: applying
    [f] to the argument [n] costs at most [k] steps, and [r] bounds the
    result. In [k], [val cn] is the value of the argument [n]. A result that
    is a number (or a boolean, a list, ...) has nothing more to bound: [r]
    is [tt]. For example,
<<
      Time.ComplexityBound Nat.add (fun cn => 4 ⋉ fun cm => (22 * val cn + 6) ⋉ tt)
>>
    says that applying [Nat.add] to [n] costs 4 steps (it builds the closure
    [Nat.add n]), and that applying [Nat.add n] to [m] costs at most
    [22 n + 6] steps. A function of two arguments has a bound of the form
    [fun cn => k1 ⋉ fun cm => k2 ⋉ tt].

    ** The method

    1. Start from the bound with 0s.
    2. Run [cbound]. It compiles the function, computes its cost in the
       model, and compares it with your bound: it reduces the bound to
       inequalities [cost found <= claimed bound], one for each case of the
       arguments, and proves those it can with [lia] and [nia].
    3. If inequalities are left, read the messages of [cbound]:
       - "The inequality ... is false for cn = 0: the cost found is 8, the
         claimed bound 6": your bound is too small for these values.
         Increase its constants, or change its shape (linear, quadratic,
         ...). With 0s, the inequalities show the cost found in each case:
         choose the constants from them.
       - Without a message, the inequality may be true but need facts that
         [lia] and [nia] do not know. [cexplain] suggests some. Then prove
         it: with [lia] or [nia] after the facts, or by hand.
    4. If [cbound] fails with "no complexity bound is known for g", your
       function calls a function [g] whose bound is unknown: one of yours
       that you have not proved yet, or one of the library that nobody has
       studied. Prove a bound for [g] first, and declare it as an instance
       ([Global Instance], or [Existing Instance] after a [Lemma]), so that
       [cbound] finds it.

    In a recursive case, the variables are those of the case: in the case
    [S n'] of an argument [n], the inequality is written with [n'].

    The tactics:
    - [cbound]: steps 2 and 3, for [ComplexityBound], [LinearBound],
      [PolynomialBound] and [ConstantBound];
    - [cexplain]: hints on an inequality left by [cbound];
    - [cproject H b]: the bound of one of two mutually recursive functions,
      from their bound [H] (section 3);
    - [csize]: a bound in the sizes of the arguments, from a bound in their
      values (section 4). *)

From Complexity Require Import TimeStdlib.
From Stdlib Require Import List.
Import ListNotations.

Module Tutorial (Import Time : TimeStdlib).

  (** ** 1. Functions without recursion *)

  Definition is_zero (n : nat) : bool := match n with O => true | S _ => false end.

  (** A case analysis on [n], and a constant in each branch. *)
  (* Replace 0 with the right bound *)
  Lemma is_zero_complexity : Time.ComplexityBound is_zero (fun cn => 0 ⋉ tt).
  (* cbound will show what inequalities should be satisfied *)
  Abort.

  (** A constant bound does not depend on the argument: [cbound] proves it,
      and finds the constant itself. *)
  Instance is_zero_constant : Time.ConstantBound is_zero.
  Abort.

  Definition pred2 (n : nat) : nat := match n with S (S k) => k | _ => 0 end.

  (** Two nested case analyses. Find the right constant *)
  Lemma pred2_complexity : Time.ComplexityBound pred2 (fun cn => 0 ⋉ tt).
  Abort.

  Definition choose (b : bool) (n m : nat) : nat := if b then n else m.

  (** Three arguments: one cost for each application. The first two only
      build closures. *)
  Lemma choose_complexity : Time.ComplexityBound choose
    (fun cb => 0 ⋉ fun cn => 0 ⋉ fun cm => 0 ⋉ tt).
  Abort.

  (** A function that calls a function of the library: [cbound] uses the
      bound of [Nat.add], an instance of [TimeStdlib]. The cost depends on
      the value of the first argument of [Nat.add]. *)
  Definition twice (n : nat) : nat := n + n.

  Lemma twice_complexity : Time.ComplexityBound twice
    (fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  (** ** 2. Recursive functions

      For a recursive function, [cbound] uses your bound for the recursive
      calls: it checks that the cost of one step, plus your bound at the
      recursive call, is within your bound. Unfolding the definition costs
      one step ([c_fix]). *)

  Fixpoint double (n : nat) : nat := match n with O => O | S k => S (S (double k)) end.

  (** Each step costs a constant: the bound is linear. Find the smallest
      constants for which [cbound] succeeds: with constants that are too
      small, [cbound] prints the case that fails, with the cost found. *)
  Lemma double_complexity : Time.ComplexityBound double
    (fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  (** [quad] calls [double]. As long as [double_complexity] is not proved
      and declared as an instance, [cbound] fails with "no complexity bound
      is known for double". So prove [double_complexity] first (with
      [Qed]), and add [Existing Instance double_complexity.] after it.

      The second call of [double] is on [double n], so its cost depends on
      the value of [double n]: the inequality left mentions it. Prove
      [double n = 2 * n] first (by induction), and rewrite with it before
      [lia]. *)
  Definition quad (n : nat) : nat := double (double n).

  Lemma quad_complexity : Time.ComplexityBound quad
    (fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  (** A function of the library that nobody has studied: [TimeStdlib]
      records no bound for [Nat.max], so [cbound] fails on [max3] with "no
      complexity bound is known for: Nat.max", whatever the constants.
      Study [Nat.max] first: write a lemma that states its bound, before
      [max3_complexity], prove it, and declare it as an instance. [Nat.max n
      m] recurses on both arguments and stops at the smaller one, so a
      bound in [n] alone is enough:
<<
      Global Instance Nat_max_complexity : Time.ComplexityBound Nat.max
        (fun cn => 0 ⋉ fun cm => (0 * val cn + 0) ⋉ tt).
>>
      Then [cbound] proves the bound of [max3]: the cost of the outer call
      only depends on [a], its first argument, and the cost of the inner one
      on [b]. *)
  Definition max3 (a b c : nat) : nat := Nat.max a (Nat.max b c).

  Lemma max3_complexity : Time.ComplexityBound max3
    (fun ca => 0 ⋉ fun cb => 0 ⋉ fun cc => (0 * val ca + 0 * val cb + 0) ⋉ tt).
  Abort.

  (** A recursion on a list. The cost of a step depends on the head of the
      list (the cost of [Nat.add] depends on its first argument), so the
      bound is in the sum of the elements, [list_sum]. The inequality left
      writes the sum of the tail as [fold_right Nat.add 0 cl], which is the
      definition of [list_sum cl]: [lia] proves it after
      [unfold list_sum in *]. *)
  Fixpoint sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + sum t end.

  Lemma sum_complexity : Time.ComplexityBound sum
    (fun cl => (0 * list_sum (val cl) + 0 * length (val cl) + 0) ⋉ tt).
  Abort.

  (** A recursion with an accumulator: the second argument changes at each
      call, but the cost only depends on the first. *)
  Fixpoint rev_acc (l acc : list nat) : list nat :=
    match l with [] => acc | x :: t => rev_acc t (x :: acc) end.

  Lemma rev_acc_complexity : Time.ComplexityBound rev_acc
    (fun cl => 0 ⋉ fun cacc => (0 * length (val cl) + 0) ⋉ tt).
  Abort.

  (** ** 3. Mutually recursive functions

      [even] and [odd] call each other, so their bounds are proved together:
      [cbound] analyses the function [fun b => if b then even else odd],
      which chooses one of them. The bound of each one then follows:
      [cproject H true] proves the bound of [even] from the bound [H] of
      the pair ([even] is the pair applied to [true]), and
      [cproject H false] the bound of [odd]. *)
  Fixpoint even (n : nat) : bool := match n with O => true | S k => odd k end
  with odd (n : nat) : bool := match n with O => false | S k => even k end.

  Lemma even_odd_complexity :
    Time.ComplexityBound (fun b : bool => if b then even else odd)
      (fun cb => 0 ⋉ fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  (** These need [even_odd_complexity], proved with [Qed]. *)
  Lemma even_complexity : Time.ComplexityBound even (fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  Lemma odd_complexity : Time.ComplexityBound odd (fun cn => (0 * val cn + 0) ⋉ tt).
  Abort.

  (** ** 4. Bounds in the sizes of the arguments

      The bounds above are in the values of the arguments ([val cn]). In
      the model, each value has a size, [#|x|] (class [Size]), at least its
      value for a natural number ([n < #|n|]) and its length for a list.

      [LinearBound f] says that the cost of [f] is at most a linear function
      of the sizes of its arguments. [cbound] proves it from a
      [ComplexityBound] instance of [f], if there is one, and otherwise
      from the definition of [f]. For a recursive function, prove the
      [ComplexityBound] first: [cbound] says so when it is missing. *)
  Lemma double_linear : Time.LinearBound double.
  Abort.

  (** [mul2] adds [m] to itself [n] times: its cost is about [n * m], which
      is not linear. Try [LinearBound mul2] to see [cbound] fail, then
      prove the polynomial bound. *)
  Fixpoint mul2 (n m : nat) : nat := match n with O => O | S k => m + mul2 k m end.

  Lemma mul2_linear : Time.LinearBound mul2.
  Abort.

  Lemma mul2_polynomial : Time.PolynomialBound mul2.
  cbound.
  Abort.

  (** From [quad_complexity] (an instance). *)
  Lemma quad_linear : Time.LinearBound quad.
  Abort.

  (** A bound in the sizes, with its constants. The type of the argument is
      written ([cn : ℂI nat _]): its size alone does not tell it.

      [cbound] does not prove it: [double] is recursive, and the recurrence
      in the sizes would need [#|n| + 1 <= #|S n|], which the model does
      not give (it only gives [n < #|n|]). It follows from the bound in the
      values instead: with [double_complexity] proved and declared as an
      instance, [csize] proves it. It takes that bound, [a * n + b], and
      checks that [a * n + b <= 20 * #|n| + 10] with [n < #|n|]. *)
  Lemma double_size : Time.ComplexityBound double
    (fun (cn : ℂI nat _) => (20 * #|val cn| + 10) ⋉ tt).
  Abort.
End Tutorial.
