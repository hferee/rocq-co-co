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
  (* TODO: is this useful? One could even have forall n, ComplexityBound n tt*)
  Parameter O_complexity : ComplexityBound O 1.
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : nat) => 1).
  Global Existing Instance S_complexity.

  (** ** Destructor *)
  (* It seems that one could derive this bound from nat_fix1_complexity,
    but that would require an extentional notion of complexity. *)
  Parameter nat_match_complexity: forall {A} (v : A) (f : nat -> A) (cv : nat) cf,
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
  Existing Instance nat_match_complexity.

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

  Parameter constant_complexity : forall {A B CB} b {cb},
  ComplexityBound (b : B) (cb : CB) ->
  ComplexityBound (fun (_ : A) => b) (fun (_ : A) => cb).
  Global Existing Instance constant_complexity.

  Parameter id_complexity : ComplexityBound (fun (x : nat) => x) (fun (_ : nat) => 1).
  Global Existing Instance id_complexity.

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
  

  Example plus_complexity:
    ComplexityBound Nat.add (fun (n m : nat) => 3 * n + 2).
  Proof.
  capply. ctac.
  (* Now check the complexity bound. *)
  Unshelve. 
  (* TODO: automate this *)
  apply bound_order_ext_eq; intro cn.
  apply bound_order_ext_eq; intro cm.
  apply bound_order_nat.
  induction cn as [|n].
  + reflexivity.
  + (* this could be automated for readability:
    remember (fix cf (n0 a : nat) {struct n0} : nat :=
            1 +  match n0 with
              | 0 => 1
              | S k => 1 + cf k a + 1
              end) as foo. *)
    lia.
  Qed.
  Existing Instance plus_complexity.

  Example mult_complexity:
    ComplexityBound Nat.mul (fun (n m : nat) => n * (4 + 3 * m) + 2).
  Proof.
  capply. (* ctac. *)
  apply nat_fix1_complexity; ctac.
  (* Now check the complexity bound. *)
  Unshelve. 
  (* TODO: automate this *)
  apply bound_order_ext_eq; intro n.
  apply bound_order_ext_eq; intro m.
  apply bound_order_nat.
  + induction n as [|n].
    * simpl. lia.
    * lia. (* trivial once you have the right bound *)
  Qed.
End NatTimeExamples.