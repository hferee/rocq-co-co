From Complexity Require Import SimpleCostModel.
From Stdlib Require Import Program.Basics Lia.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat.
  
  (* Constructors *)
  Parameter O_complexity : ComplexityBound O tt. (* TODO: is this useful? *)
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : ℂI nat) => 1 ⋉ tt).
  Existing Instance S_complexity.

  (* Destructor *)
  Parameter nat_match_complexity: forall {A CA} `{CT A CA} (v : A) (f : nat -> A)
    (cv : CA) cf,
    let T := fun_CT nat A in
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun n => match n with
                | O => v
                | S k => f k
                end)
      (fun n => 1 ⊕ (* 1 for the match *)
                match ival n with
                | O => ret cv
                | S k => cf (k ⋊ tt)
                end).
  Existing Instance nat_match_complexity.

  (* Induction principle on nat, first for unary functions *)
  Parameter nat_complexity_rect1: forall {A CA} `{CT A CA} (v : A) (f : nat -> A -> A)
    (cv : CA) (cf: ℂI nat -> ℂO (ℂI A -> ℂO CA)),
    let T := fun_CT nat A in
    let T := fun_CT nat (A -> A) in
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    let g := nat_rect _ v f in
    ComplexityBound g
      (fun cn => (nat_rect (fun n => ℂO (ℂI A)) (ret (v ⋊ cv))
                  (fun k gk =>
                    gk O>>=O (((k ⋊ tt) I>>=I (f ⋊ cf)))) (ival cn)) >>|).

 (* TODO: are there (structural) fixpoints on nat that are not expressible this way?
  And can we write a tactic to turn most such functions into a nat_rect?
  And can we automatically prove they are extensionally equal? *)

  (* A quite general complexity bound for fixpoints over nat with 1 additional
    argument. Hopefully I got it right. *)
  (* fixpoint over nat with 1 additional argument *)
  Definition nat_fix1 (A B : Type) (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) :=
    fix f (n : nat) (x : A) : B := match n with O => v x | S k => F k x (f k (g k x)) end.

  Parameter nat_fix1_complexity : forall (A B CA CB : Type) `{CT A CA} `{CT B CB}
  (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) (cv : ℂI A -> ℂO CB) cg cF,
  let f := nat_fix1 A B v g F in
    ComplexityBound v cv ->
    ComplexityBound g (cg : ℂI nat -> ℂO (ℂI A -> ℂO CA)) ->
    ComplexityBound F (cF : ℂI nat -> ℂO (ℂI A -> ℂO (ℂI B -> ℂO CB))) ->
    ComplexityBound (f : nat -> A -> B)
      (fun (cn : ℂI nat) => 1 ⋉ fun (cx : ℂI A) => 
      ((fix cfix n (cx : ℂO (ℂI A)) : ℂO (ℂI B) := 1 ⊕
        match n with
      | O => cx O>>=I (v ⋊ cv)
      | S k => (cfix k (cx O>>=O ((k ⋊ tt) I>>=I (g ⋊ cg))))
               O>>=O (cx O>>=O ((k ⋊ tt) I>>=I (F ⋊ cF)))
      end) (ival cn) (ret cx) >>|) : ℂO CB).

End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel)
  (Import BT : BasicTimeCostModel CM) (Import B: NatTimeCostModel CM BT).

  Example plus2 (n : nat) := S (S n).
  (* TODO: here *)

  Example plus2_complexity: ComplexityBound plus2 (fun n => 2 ⋉ tt).
  Proof.
  (* We get 4 and not 2, as we go through compose S S  *)
  change plus2 with (compose S S).
  capply. (* replace the complexity bound with evars *)
  eapply apply_complexity; [apply S_complexity|].
  (* annoying : need to type annotate with simple types *)
  eapply apply_complexity; [apply S_complexity|].
  apply comp1_complexity.
  Unshelve. unfold ObindI, IbindI. simpl.
  apply bound_order_ext_eq. intros. unfold OIbindO. simpl.
  reflexivity.
  Qed.
  
  (* TODO: we will need axioms for bound_order and nat *)

  (* Better? *)
  Example plus2_complexity': ComplexityBound plus2 (fun n => 2 ⋉ tt).
  Proof.
  change plus2 with (compose S S).
  (* Let's have another go *)
  capply.
  (* TODO: explicit type annotations are annoying *)
  eapply compose_complexity; apply S_complexity.
  Unshelve. apply bound_order_ext_eq. intros. unfold OIbindO. reflexivity.
  Qed.
(* TODO: annoying: doesn't work without the type annotation. *)
  Example plus_complexity:
    ComplexityBound plus ((fun cn => (ival cn + 1) ⋉ fun cm => (1 + 3 * ival cm) ⋉ tt) :
      ℂI nat -> ℂO (ℂI nat -> ℂO unit)).
  (* TODO: I can't really explain the 3 * n  there *)
  Proof.
  change_fun_with (nat_rect _ id (fun k nk m => S (nk m))).
  capply.
  (* TODO: a tactic should handle this *)
  eapply nat_complexity_rect1.
  - apply id_complexity.
  - apply @constant_complexity. (* TODO: why is this only working with @? *)
    unshelve change_fun_with (fun (nk : nat -> nat) => compose S nk).
    eapply apply_complexity.
    + apply S_complexity.
    + apply comp1_complexity.
  Unshelve.
  * apply ext_eq_fun. intro n. apply ext_eq_fun. intros m. apply  ext_eq_eq.
    induction n; simpl; auto with*.
  * (* TODO: ugly *)
    apply bound_order_ext_eq. intros. unfold ret, OIbindO, IbindI. simpl.
(*     intro m. split; trivial. induction n; trivial. simpl. lia. *)
    admit.
  Admitted.

  Example plus_complexity':
    ComplexityBound plus
                    ((fun n => 1 ⋉ fun m => (2 + 3 * ival n) ⋉ tt)
                    : ℂI nat -> ℂO (ℂI nat -> ℂO unit)).
  Proof.
  fold ℂT.
  capply. apply nat_fix1_complexity.
  - apply id_complexity. 
  - eapply constant_complexity. (* the type annotation is necessary *)
    apply id_complexity.
  - eapply constant_complexity.
    eapply constant_complexity.
    apply S_complexity.
  (* Now check the complexity bound. *)
  Unshelve. apply bound_order_ext_eq.
  intros [n ()]. simpl. repeat split; trivial.
  induction n as [|n].
  + simpl. admit.
  + admit. (* destruct ca as [a ()]; simpl.
    repeat apply le_n_S. lia. *)
  Admitted.

End NatTimeExamples.