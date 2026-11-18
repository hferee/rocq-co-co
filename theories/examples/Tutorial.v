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
    function of one argument, [c] is a function [fun cn => k +> r]: applying
    [f] to the argument [n] costs at most [k] steps, and [r] bounds the
    result. In [k], [val cn] is the value of the argument [n]. A result that
    is a number (or a boolean, a list, ...) has nothing more to bound: the
    bound is then [fun cn => k >|], and [k >|] reads: the cost [k], and
    nothing after it. For example,
<<
      Time.ComplexityBound Nat.add (fun cn => 1 +> fun cm => 14 * val cn + 10 >|)
>>
    says that applying [Nat.add] to [n] costs 1 step (it builds the closure
    [Nat.add n]), and that applying [Nat.add n] to [m] costs at most
    [14 n + 10] steps. A function of two arguments has a bound of the form
    [fun cn => k1 +> fun cm => k2 >|]. [k +> r] reads: the cost [k],
    then the costs of [r], when the result is used. [+>] and [>|] bind less
    tightly than [+] and [*], so [14 * val cn + 10 >|] needs no parentheses.

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
         [lia] and [nia] do not know (see the facts below). [cexplain]
         suggests some. Then register them, or prove the inequality: with
         [lia] or [nia] after the facts, or by hand.
    4. If [cbound] fails with "no complexity bound is known for g", your
       function calls a function [g] whose bound is unknown: one of yours
       that you have not proved yet, or one of the library that nobody has
       studied. Prove a bound for [g] first, and declare it as an instance
       ([Global Instance], or [Existing Instance] after a [Lemma]), so that
       [cbound] finds it. If it fails with "unknown complexity bound for
       the local fixpoint", your function contains a [fix] (a [let fix],
       say): prove its bound first, as a hypothesis ([assert (H :
       Time.ComplexityBound (fix ...) ...) by cbound]) or an instance, and
       [cbound] reads it from the context (see the local fixpoints of
       [Examples]).

    ** The facts

    [lia] and [nia] only know arithmetic: the values of the functions, the
    sizes, and the booleans are unknowns for them. Before [lia] and [nia],
    [cbound] adds to each inequality the facts that it knows on what the
    inequality mentions:
    - the tests of its case: in the branch where [n <? 10] is [true], the
      fact [n < 10]; where [10 <? n] is [false], [n <= 10] ([cbool_facts]).
      A cost in [n] may then be bounded by a constant (section 2, [small]);
    - the facts on the values of functions ([ValueFact]): a lemma on the
      value [f x] of a function, declared as an instance, is added to every
      inequality that mentions a value of [f]. For [double] (section 2):
<<
      Instance double_value_fact n : ValueFact (double n) (fun y => y = 2 * n) := double_spec n.
>>
      The fact is a predicate on the value ([fun y => ...]), applied to the
      value as the inequality writes it. The library registers some
      ([length (filter p l) <= length l], [HOListComplexity]); register
      those of your functions where they are defined. One instance per
      value: a conjunction for several facts;
    - the facts on the sizes ([SizeFact]), for the bounds in the sizes of
      the arguments (section 4): [n < #|n|] for a number, [length l < #|l|]
      for a list. The model registers them with its data types
      ([NatComplexity], [ListComplexity]); a new data type registers its own
      ([literal_size_fact], in [ETHCost]).
    A fact that is not registered can be added by hand, with [pose proof],
    before [lia] or [nia]: for an inequality that [cbound] leaves.

    ** Finding the constants

    Instead of 0s, you can make the constants unknowns. In the proof
    (before [Abort], or in a [Goal True]), introduce temporary constants
    with [evar], state the bound with them, and run [cbound] on it. The
    constants are opaque: [lia] proves nothing about them, so every
    inequality is left, in terms of them. For [length]:
<<
      evar (a : nat). evar (b : nat).
      assert (Time.ComplexityBound (@length nat) (fun cl => (a * length (val cl) + b) >|)).
      { cbound. }
>>
    leaves two inequalities, one for each case of the list:
    - [6 <= b], for the empty list;
    - [a * length cl + b + 16 <= a * length cl + a + b], for a list whose
      tail is [cl] (the cost of the recursive call is the bound itself).
    That is, [b >= 6] and [a >= 16]: the bound is [16 * length (val cl) + 6].
    Put the values in the bound, in place of its 0s. To check them first,
    give them to the unknowns, and finish the proof:
<<
      instantiate (a := 16). instantiate (b := 6). all: subst a b; lia.
>>

    In a recursive case, the variables are those of the case: in the case
    [S n'] of an argument [n], the inequality is written with [n'].

    The tactics stop after 2 seconds, with a message, if they have not
    finished: [lia] and [nia] may search in vain on an inequality that does
    not hold. For a larger function, increase the timeout (in seconds; [0]
    for none):
<<
      Ltac2 Set ctimeout := 10.
>>

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
  Lemma is_zero_complexity : Time.ComplexityBound is_zero (fun cn => 0 >|).
  (* cbound will show what inequalities should be satisfied *)
  Abort.

  (** A constant bound does not depend on the argument: [cbound] proves it,
      and finds the constant itself. *)
  Instance is_zero_constant : Time.ConstantBound is_zero.
  Abort.

  Definition pred2 (n : nat) : nat := match n with S (S k) => k | _ => 0 end.

  (** Two nested case analyses. Find the right constant *)
  Lemma pred2_complexity : Time.ComplexityBound pred2 (fun cn => 0 >|).
  Abort.

  Definition choose (b : bool) (n m : nat) : nat := if b then n else m.

  (** Three arguments: one cost for each application. The first two only
      build closures. *)
  Lemma choose_complexity : Time.ComplexityBound choose
    (fun cb => 0 +> fun cn => 0 +> fun cm => 0 >|).
  Abort.

  (** A function that calls a function of the library: [cbound] uses the
      bound of [Nat.add], an instance of [TimeStdlib]. The cost depends on
      the value of the first argument of [Nat.add]. *)
  Definition twice (n : nat) : nat := n + n.

  Lemma twice_complexity : Time.ComplexityBound twice
    (fun cn => (0 * val cn + 0) >|).
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
    (fun cn => (0 * val cn + 0) >|).
  Abort.

  (** [quad] calls [double]. As long as [double_complexity] is not proved
      and declared as an instance, [cbound] fails with "no complexity bound
      is known for double". So prove [double_complexity] first (with
      [Qed]), and add [Existing Instance double_complexity.] after it.

      The second call of [double] is on [double n], so its cost depends on
      the value of [double n]: the inequality left mentions it, and [lia]
      knows nothing about it. Prove [double n = 2 * n] first (by
      induction), and register it as a fact on the values of [double]
      (see the facts, at the top):
<<
      Lemma double_spec n : double n = 2 * n.
      Instance double_value_fact n : ValueFact (double n) (fun y => y = 2 * n) := double_spec n.
>>
      Then [cbound] adds [double n = 2 * n] to the inequalities that mention
      [double n], and proves the bound. *)
  Definition quad (n : nat) : nat := double (double n).

  Lemma quad_complexity : Time.ComplexityBound quad
    (fun cn => (0 * val cn + 0) >|).
  Abort.

  (** A test of the argument is a fact too: in the branch where [10 <? n]
      is [false], [cbound] knows that [n <= 10], so the cost of [double n]
      is at most a constant, and so is the cost of [small]. (The cost of
      [10 <? n] is constant: [Nat.ltb] recurses on its first argument.) *)
  Definition small (n : nat) : nat := if 10 <? n then 0 else double n.

  Lemma small_complexity : Time.ComplexityBound small (fun cn => 0 >|).
  Abort.

  (** The constant of a [ConstantBound] is found from the shape of the cost
      (its degree), which does not see the tests: from the definition of
      [small], [cbound] leaves the case [n <= 10], and says why. Declare
      [small_complexity] as an instance: [cbound] then proves this one from
      it. *)
  Lemma small_constant : Time.ConstantBound small.
  Abort.

  (** A function of the library that nobody has studied: [TimeStdlib]
      records no bound for [Nat.compare], so [cbound] fails on [lt3] with
      "no complexity bound is known for: Nat.compare", whatever the
      constants. Study [Nat.compare] first: write a lemma that states its
      bound, before [lt3_complexity], prove it, and declare it as an
      instance. [Nat.compare n m] recurses on both arguments and stops at
      the smaller one, so a bound in [n] alone is enough:
<<
      Global Instance Nat_compare_complexity : Time.ComplexityBound Nat.compare
        (fun cn => 0 +> fun cm => (0 * val cn + 0) >|).
>>
      Then [cbound] proves the bound of [lt3]: the cost of the first
      comparison only depends on [a], its first argument, and the cost of
      the second one on [b]. *)
  Definition lt3 (a b c : nat) : bool :=
    match Nat.compare a b with
    | Lt => match Nat.compare b c with Lt => true | _ => false end
    | _ => false
    end.

  Lemma lt3_complexity : Time.ComplexityBound lt3
    (fun ca => 0 +> fun cb => 0 +> fun cc => (0 * val ca + 0 * val cb + 0) >|).
  Abort.

  (** A recursion on a list. The cost of a step depends on the head of the
      list (the cost of [Nat.add] depends on its first argument), so the
      bound is in the sum of the elements, [list_sum], and in the length
      of the list. *)
  Fixpoint sum (l : list nat) : nat := match l with [] => 0 | x :: t => x + sum t end.

  Lemma sum_complexity : Time.ComplexityBound sum
    (fun cl => (0 * list_sum (val cl) + 0 * length (val cl) + 0) >|).
  Abort.

  (** A recursion with an accumulator: the second argument changes at each
      call, but the cost only depends on the first. *)
  Fixpoint rev_acc (l acc : list nat) : list nat :=
    match l with [] => acc | x :: t => rev_acc t (x :: acc) end.

  Lemma rev_acc_complexity : Time.ComplexityBound rev_acc
    (fun cl => 0 +> fun cacc => (0 * length (val cl) + 0) >|).
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
      (fun cb => 0 +> fun cn => (0 * val cn + 0) >|).
  Abort.

  (** These need [even_odd_complexity], proved with [Qed]. *)
  Lemma even_complexity : Time.ComplexityBound even (fun cn => (0 * val cn + 0) >|).
  Abort.

  Lemma odd_complexity : Time.ComplexityBound odd (fun cn => (0 * val cn + 0) >|).
  Abort.

  (** ** 4. Bounds in the sizes of the arguments

      The bounds above are in the values of the arguments ([val cn]). In
      the model, each value has a size, [#|x|] (class [Size]), at least its
      value for a natural number ([n < #|n|]) and its length for a list.
      These are the facts on the sizes ([SizeFact], see the facts, at the
      top): [cbound] and [csize] add them to the inequalities that mention
      the sizes.

      [LinearBound f] says that the cost of [f] is at most a linear function
      of the sizes of its arguments. [cbound] proves it from a
      [ComplexityBound] instance of [f], if there is one, and otherwise
      from the definition of [f]. For a recursive function, prove the
      [ComplexityBound] first: [cbound] says so when it is missing. *)
  Lemma double_linear : Time.LinearBound double.
  Abort.

  (** [mul2] adds [m] to itself [n] times: its cost is about [n * m], which
      is not linear, so [mul2_linear] cannot be proved. [cbound] shows the
      inequality that cannot hold, and says why: the cost found has degree
      2 in the arguments, a linear bound degree 1. Then prove the polynomial
      bound. *)
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
      not give (it only gives [n < #|n|], its fact on the sizes). It follows
      from the bound in the values instead: with [double_complexity] proved
      and declared as an instance, [csize] proves it. It takes that bound,
      [a * n + b], and checks that [a * n + b <= 20 * #|n| + 10] with the
      fact [n < #|n|]. *)
  Lemma double_size : Time.ComplexityBound double
    (fun (cn : ℂI nat _) => (20 * #|val cn| + 10) >|).
  Abort.
End Tutorial.
