(** * Tutorial: proving complexity bounds

    A set of exercises. Each one states a complexity bound for a function,
    with [0] in place of its constants, and ends with [Abort]: replace the
    [0]s by constants for which the bound holds, and [Abort] by a proof
    that ends with [Qed]. The sections get harder as they go. *)

From Complexity Require Import TimeStdlib.
From Stdlib Require Import List.
Import ListNotations.

(** The functions are analysed in the time cost model ([TimeCostModel]):
    a function is compiled to combinators, and each application of a
    combinator, a constructor or a case analysis costs one step. [TimeStdlib]
    adds the bounds of the standard library ([Nat.add], [length], ...),
    used when your functions call them. *)
Module Tutorial (Import Time : TimeStdlib).

  (** ** 1. Functions without recursion

      [Time.ComplexityBound f c] says that [c] bounds the cost of [f]. For a
      function of one argument, [c] is [fun cn => k +> r]: applying [f] to
      [n] costs at most [k] steps, and [r] bounds the result; [val cn] is
      the value of [n]. A result that is a number (or a boolean, a list,
      ...) has nothing more to bound: [k >|] reads "the cost [k], and
      nothing after it". For example,
<<
      Time.ComplexityBound Nat.add (fun cn => 1 +> fun cm => 14 * val cn + 10 >|)
>>
      says that applying [Nat.add] to [n] costs 1 step (it builds the
      closure [Nat.add n]), and applying [Nat.add n] to [m] at most
      [14 n + 10] steps. [+>] and [>|] bind less tightly than [+] and [*].

      The method:
      1. Start from the bound with 0s.
      2. Run [cbound]. It compiles the function, computes its cost, and
         reduces the bound to inequalities [cost found <= claimed bound],
         one for each case of the arguments, which it proves with [lia]
         and [nia] when it can. It stops after 2 seconds
         ([Ltac2 Set ctimeout := 10.] for more, [0] for no limit).
      3. Read the messages on the inequalities left. "The inequality ...
         is false for cn = 0: the cost found is 8, the claimed bound 6":
         the bound is too small; with 0s, the inequalities show the cost
         found in each case. Without a message, the inequality may hold
         but need facts that [lia] and [nia] do not know: [cexplain]
         suggests some (section 2). *)

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
      one step ([c_fix]). In a recursive case, the variables are those of
      the case: in the case [S n'] of [n], the inequality is written with
      [n']. A [fix] inside a definition needs its bound first, as a
      hypothesis or an instance ([Examples]).

      The constants can be found as unknowns. Introduce them with [evar],
      and run [cbound] on the bound with them: [lia] proves nothing about
      them, so every inequality is left, in terms of them. For [length],
<<
      evar (a : nat). evar (b : nat).
      assert (Time.ComplexityBound (@length nat) (fun cl => (a * length (val cl) + b) >|)).
      { cbound. }
>>
      leaves [6 <= b] for the empty list, and
      [a * length cl + b + 16 <= a * length cl + a + b] for a list whose
      tail is [cl]: the bound is [16 * length (val cl) + 6]. To check the
      values, give them to the unknowns:
      [instantiate (a := 16). instantiate (b := 6). all: subst a b; lia.] *)

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
      the value of [double n]: the inequality left mentions it, and [lia],
      which only knows arithmetic, knows nothing about it. Prove
      [double n = 2 * n] first (by induction), and register it as a fact on
      the values of [double] ([ValueFact]): [cbound] adds the registered
      facts on the values that an inequality mentions. The fact is a
      predicate on the value, applied to the value as the inequality writes
      it; one instance per value (a conjunction for several facts). The
      library registers some ([length (filter p l) <= length l]). A fact
      that is not registered can be added by hand, with [pose proof],
      before [lia].
<<
      Lemma double_spec n : double n = 2 * n.
      Instance double_value_fact n : ValueFact (double n) (fun y => y = 2 * n) := double_spec n.
>>
      Then [cbound] proves the bound. *)
  Definition quad (n : nat) : nat := double (double n).

  Lemma quad_complexity : Time.ComplexityBound quad
    (fun cn => (0 * val cn + 0) >|).
  Abort.

  (** The tests of a case are facts too ([cbool_facts]): in the branch
      where [10 <? n] is [false], [cbound] knows that [n <= 10], so the
      cost of [double n] is at most a constant, and so is the cost of
      [small]. (The cost of [10 <? n] is constant: [Nat.ltb] recurses on
      its first argument.) *)
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
      These are the facts on the sizes ([SizeFact]), registered with the
      data types ([NatComplexity], [ListComplexity]; a new type registers
      its own, as [literal_size_fact] in [ETHCost]): [cbound] and [csize]
      add them to the inequalities that mention the sizes.

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
