(* An attempt at working with natural numbers where all functions are fully
applied ; no higher-order functions required. *)

From Complexity Require Import CostModel.
(* In particular, we don't rely on HOCostModel. *)
From Stdlib Require Import Program.Basics Lia.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel).

(*   Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat. *)
  
  (* Constructors *)
  (* TODO: This is used in Nat.mul for instance. *)
  Parameter O_complexity : ComplexityBound O 1.
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : nat) => 1).
  Global Existing Instance S_complexity.

  (** ** Destructor *)
  (* It seems that one could derive this bound from nat_fix1_complexity,
    but that would require an extentional notion of complexity. *)
(*   Parameter nat_match_complexity: forall {A} (v : A) (f : nat -> A) (cv : nat) cf,
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun n => match n with
                | O => v
                | S k => f k
                end)
      (fun (n : nat) => 1 + (* 1 for the match *)
                match n with
                | O => cv
                | S k => cf k
                end).
  Existing Instance nat_match_complexity. *)
  (* A slightly stronger version, where the matched integer is still bound in 
    the subcases. Required for pred. *)
  Parameter nat_match_complexity': forall {A} (v : nat -> A) (f : nat -> nat -> A)
    (cv : nat -> nat) cf,
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun n => match n with
                | O => v n
                | S k => f n k
                end)
      (fun (n : nat) => 1 + (* 1 for the match *)
                match n with
                | O => cv n
                | S k => cf n k
                end).
  Existing Instance nat_match_complexity'.

 (* TODO: are there (structural) fixpoints on nat that are not expressible this way?
  And can we write a tactic to turn most such functions into a nat_rect?
  And can we automatically prove they are extensionally equal? *)

  (* Simple recursion with no additional argument *)
  Definition nat_fix0 (B : Type) (v : B) (F : nat -> B -> B) :=
    fix f (n : nat) : B := match n with O => v | S k => F k (f k) end.

  Parameter nat_fix0_complexity : forall {B : Type}
  (v : B) (F : nat -> B -> B) (cv : nat) cF,
  let f := nat_fix0 B v F in
    ComplexityBound v cv ->
    ComplexityBound F (cF : nat -> B -> nat) ->
    ComplexityBound (f : nat -> B)
      (fix cfix n acc : nat := 1 +
        match n with
      | O => cv
      | S k => (* the recursive call *)
              cfix k (cF k)
      end).

  (* A quite general complexity bound for fixpoints over nat with 1 additional
    argument. Hopefully I got it right. *)
  (* fixpoint over nat with 1 additional argument *)
  Definition nat_fix1 (A B : Type) (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) :=
    fix f (n : nat) (x : A) : B := match n with O => v x | S k => F k x (f k (g k x)) end.
  Parameter nat_fix1_complexity : forall {A B : Type}
  (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) (cv : A -> nat)
  (cg : nat -> A -> nat) (cF : nat -> A -> B -> nat),
  let f := nat_fix1 A B v g F in
    ComplexityBound v cv ->
    ComplexityBound g (cg : nat -> A -> nat) ->
    ComplexityBound F (cF : nat -> A -> B -> nat) ->
    ComplexityBound (f : nat -> A -> B)
      (fix cf (n : nat) (a : A) : nat := 1 + match n with
        | O => cv a
        | S k => cg k a + cf k (g k a) + cF k a (f k (g k a))
        end).
  Global Existing Instance nat_fix1_complexity.
  
  (* TODO: add a sort of eta expansion rule to use nat_fix0 for nat_fix1 *)
  (*   ComplexityBound (fix f n => match | O => fun a | _ => fun a ...) cf
    -> ComplexityBound (fix f n a => cf)
  *)
  (* ComplexityBound (fix f n => | O => v | S p => g p (f p) ... ) cf
  
    whenever bound_order (1 ⋉ v) (cf 0)
    and      forall p, bound_order "eval g p (cf p)" (cf (S p))
   *)

(* TODO: is there a better way to express this bound ; more extensionally using
  recursion equations? *)
(* TODO: define binary and ternary applications *)

  Parameter bound_order_nat : forall (n m : nat),
    bound_order n m <-> n <= m.

(* First-order composition *)
Parameter fo_compose_complexity : forall {A B C}
  (f : B -> C) (cf : B -> nat) (g : A -> B) (cg : A -> nat),
  ComplexityBound f cf ->
  ComplexityBound g cg ->
  ComplexityBound (compose f g : A -> C)
                  (fun a => cg a + cf (g a)) (* Looks like a derivation *).
  Global Existing Instance fo_compose_complexity.

  (* Variant with 2 arguments. TODO: generalize *)
  Parameter fo_compose_complexity2 : forall {A B B' C}
  (f : B -> B' -> C) (cf : B -> B' -> nat) (g : A -> B) (g' : A -> B') (cg : A -> nat)
  (cg' : A -> nat),
  ComplexityBound f cf ->
  ComplexityBound g cg ->
  ComplexityBound g' cg' ->
  ComplexityBound (fun n => f (g n) (g' n) : C)
                  (fun a => cg a + cg' a + cf (g a) (g' a)).
  Global Existing Instance fo_compose_complexity2.

  Parameter constant_complexity : forall {A B CB} b {cb},
  ComplexityBound (b : B) (cb : CB) ->
  ComplexityBound (fun (_ : A) => b) (fun (_ : A) => cb).
  Global Existing Instance constant_complexity.
  
  (* TODO: we need all of Corelib.Program.Basics. flip ; apply *)

  Parameter id_complexity : ComplexityBound (fun (x : nat) => x) (fun (_ : nat) => 1).
  Global Existing Instance id_complexity.

  (* More general than id, necessary for flip: return the first argument. *)
  (* TODO: generalise with arbitrarily many arguments. *)
  Parameter first_arg_complexity: forall {A B : Type},
    ComplexityBound (fun (a : A) (b : B) => a) (fun  (_ : A) => 1).
  Global Existing Instance first_arg_complexity.

  (* Experimental *)
  (* Curryfication may be necessary to handle arbitrarily many arguments
    and ignore arguments order *)
  Parameter curry_complexity: forall {A B C A' B' C'} (f : A * B -> C)
    (cf : A' * B' -> C'),
    ComplexityBound f cf -> ComplexityBound (curry f) (curry cf).
  Global Existing Instance curry_complexity.

  Parameter curry_complexity': forall {A B C A' B' C'} (f : A * B -> C)
    (cf : A' * B' -> C'),
    ComplexityBound (curry f) (curry cf) -> ComplexityBound f cf.
  Global Existing Instance curry_complexity'.
  
  Parameter fst_complexity: forall {A B},
    ComplexityBound (@fst A B) (fun (_ : A * B) => 1).
  Global Existing Instance fst_complexity.

  Parameter snd_complexity: forall {A B},
    ComplexityBound (@snd A B) (fun (_ : A * B) => 1).
  Global Existing Instance snd_complexity.
End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel) (Import B: NatTimeCostModel CM).

  Ltac ctac := typeclasses eauto.

  Example plus2 (n : nat) := S (S n).

  Example plus2_complexity: ComplexityBound plus2 (fun (n : nat) => 2).
  Proof.
  (* Another try, simpler, without extensionality *)
  capply. (* why does typeclasses eauto fail here? *)
  (* TODO: explicit type annotations are annoying *)
  apply fo_compose_complexity; apply S_complexity.
  Unshelve. apply bound_order_ext_eq. intros. reflexivity.
  Qed.

(* Tactic for bounds *)
Ltac btac cf:= 
  match goal with |- bound_order ?f _ => remember f as cf;
    repeat (apply bound_order_ext_eq; intro); try apply bound_order_nat
  end.

  Example plus_complexity:
    ComplexityBound Nat.add (fun (n m : nat) => 3 * n + 2).
  Proof.
  capply. ctac.
  (* Now check the complexity bound. *)
  Unshelve. btac cplus.
  induction x as [|n].
  + subst cplus. reflexivity.
  + subst cplus. (* the remember in btac followed by a subst sounds silly, but
    inbetween, one can more easily inspect the goal to find the right bound *)
    lia.
  Qed.
  Existing Instance plus_complexity.

  Example mult_complexity:
    ComplexityBound Nat.mul (fun (n m : nat) => n * (4 + 3 * m) + 2).
  Proof.
  capply. (* ctac. *)
  apply nat_fix1_complexity; ctac.
  (* Now check the complexity bound. *)
  Unshelve. btac cmul.
  + induction x as [|n].
    * simpl. subst; lia.
    * subst; lia. (* trivial once you have the right bound *)
  Qed.
  Existing Instance mult_complexity.

  Example pred_complexity:
    ComplexityBound Nat.pred (fun (n : nat) => 2).
  Proof.
  unfold pred. capply.
  (* Difficulty: for some reason, pred is n, not O, when n matches O *)
  ctac.
  Unshelve. simpl. btac cpred. destruct x; subst; lia.
  Qed.

  Example double_complexity:
    ComplexityBound Nat.double (fun n => n * 3 + 4).
  Proof.
  unfold Nat.double. capply. ctac.
  Unshelve. simpl. btac cpred. subst. lia.
  Qed.

Definition mysub :=
(fix sub (n m : nat) {struct n} : nat :=
     match n with
     | 0 => 0
     | S k => match m with
              | 0 => (S k)
              | S l => sub k l
              end
     end).

  Example sub_complexity:
    ComplexityBound mysub (fun n => n * 3 + 4).
  Proof.
  unfold mysub. capply.
  (* Difficulties: as for pred, sub still binds n after matching over it.
    Furthermore, it doesn't always make a recursive call when n = S k *)
  Abort.
  
  Example eqb_complexity:
    ComplexityBound Nat.eqb (fun n m => n + m).
  Proof.
  unfold Nat.eqb. capply.
  (* Similar to sub. leb ltb, max, min compare will be similar *)
  Abort.

  (* TODO: with this approach, we can't have general enough axioms as we can't
  reason about arbitrary fixpoints or match. *)
(*   Goal(exists (f : bool -> (bool -> nat) -> nat), S = fun n => 
    (fix g n x := match n with |O => O | S k => f x (g k) end) n true). *)

  Example even_complexity:
    ComplexityBound Nat.even (fun n => S n).
  Proof. unfold Nat.even. capply. Abort.

(* TODO: flipping arguments will not work under fix. *)  
(* Goal ((fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) =
  (fix add (m n : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add m p)
  end)).
 *)
  (* Difficulty : match is not standard (base case 1).
    Recursive call is made on "n - 2". *)

  (* Flip *)
(*   Definition add_flip n m := Nat.add m n. *)
  Example flip_complexity {A B C A' B' C'} (f : A -> B -> C) (cf: A' -> B' -> C'):
    ComplexityBound (flip f) (flip cf) -> ComplexityBound f cf.
  Proof.
  (* TODO: We might need match on pairs for this.*)
  (* This will add a constant cost, to lookup subterms *)
(*   replace (flip f) with (curry (fun ab => f (snd ab) (fst ab))) by reflexivity.
  replace (flip cf) with (curry (fun ab => cf (snd ab) (fst ab))) by reflexivity.
  intros Hc%curry_complexity'.
  apply (curry_complexity (uncurry f) (uncurry cf)). *)
  replace (uncurry f) with (fun p => (flip f) (snd p) (fst p)) .
  Abort.

  Example pow_complexity:
    ComplexityBound Nat.pow (fun n m => n * m + 1).
  Proof.
  capply.
   Abort.
  (* Difficulty: recursion is made on the second argument.
    Similar to Nat.div. *)

  (* Tail add has the same time complexity as add. Space complexity should be
    different though. *)
  Example tail_add_complexity:
    ComplexityBound Nat.tail_add (fun n (m : nat) => 3 * n + 2).
  Proof.
  unfold Nat.tail_add. capply.
  (* TODO: ctac fails here *)
  apply (nat_fix1_complexity
    (@id nat)
    (fun (k x : nat) => S x)
    (fun (k x : nat) r => r)).
  - apply id_complexity. (* TODO: this should be automated by ctac *)
  - ctac.
  - ctac.
  Unshelve. simpl. btac ctail.
  + revert x0. induction x as [|n]; intro x0.
  * simpl. subst; lia.
  * simpl. specialize (IHn (S x0)). subst. lia.
  Qed.
  
  Example square_complexity:
    ComplexityBound Nat.square (fun n => 4 + n * (4 + 3 * n)).
  Proof. unfold Nat.square. capply. ctac.
  Unshelve.
  simpl. apply bound_order_ext_eq; intro n. apply bound_order_nat.
  remember ((fix cf (n0 a : nat) {struct n0} : nat :=
         S
           match n0 with
           | 0 => 1
           | S k => S (cf k a + (a + (a + (a + 0)) + 2))
           end)) as cf.
  do 2 apply le_n_S.
  (* Difficulty: a bit of generalisation is necessary. *)
  enough (Hnm: forall n m, cf n m <= n * (3 * m + 4) + 2).
  { specialize (Hnm n n). lia. }
  clear n. intros n m. induction n as [|n]; subst; lia.
  Qed.


  


  (* TODO: Nat.sqrt_iter is a fixpoint with 4 arguments *)
(* Nat.sqrt_iter
     Definition divmod : nat -> nat -> nat -> nat -> nat * nat.
     Definition div : nat -> nat -> nat.
     Definition modulo : nat -> nat -> nat.
     Definition gcd : nat -> nat -> nat.
     Definition sqrt_iter : nat -> nat -> nat -> nat -> nat.
     Definition sqrt : nat -> nat.
     Definition log2_iter : nat -> nat -> nat -> nat -> nat.
     Definition log2 : nat -> nat.
     Definition iter : nat -> forall A : Type, (A -> A) -> A -> A.
     Definition div2 : nat -> nat.
     Definition testbit : nat -> nat -> bool.
     Definition shiftl :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition shiftr :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat.
     Definition land : nat -> nat -> nat.
     Definition lor : nat -> nat -> nat.
     Definition ldiff : nat -> nat -> nat.
     Definition lxor : nat -> nat -> nat.
     *)
End NatTimeExamples.