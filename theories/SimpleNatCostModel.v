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
  Program Parameter nat_complexity_rect1: forall {A CA} `{CT A CA} (v : A) (f : nat -> A -> A)
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
  let T := fun_CT nat (A -> B -> B) in
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

  Parameter constant_complexity : forall {A B CA CB} `{CT A CA}`{CT B CB} {b cb},
    ComplexityBound (b : B) (cb : CB) ->
    ComplexityBound (fun (_ : A) => b) (fun (_ : ℂI A) => 1 ⋉ cb).
(* TODO HERE *)
  (* Replaces the complexity bound with an evar.
     The complexity bound goal will eventually need to be taken from the shelf. *)
  Ltac capply := eapply (fun f => ComplexityBound_proper f f (ltac:(reflexivity))); [shelve|].

  (* Tactic to replace the function with an extensionally equivalent one in
    a [ComplexityBound] goal *)
  Ltac change_fun_with f' := match goal with
  | |- ComplexityBound ?a ?f ?c => 
      eapply (@ComplexityBound_proper a f' f _ c c (ltac:(reflexivity)))
  end.
End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel)
  (Import BT : BasicTimeCostModel CM) (Import B: NatTimeCostModel CM BT).

  Example plus2 (n : nat) := S (S n).
  Example plus2_complexity: ComplexityBound $(nat -> nat) plus2 (fun n => 4).
  Proof.
  (* We get 4 and not 2, as we go through compose S S  *)
  change plus2 with (compose S S).
  capply. (* replace the complexity bound with evars *)
  eapply (apply_complexity (v := S : $(nat -> nat))); [apply S_complexity|].
  (* annoying : need to type annotate with simple types *)
  eapply (apply_complexity (v := S : $(nat -> nat))); [apply S_complexity|].
  apply comp1_complexity.
  Unshelve. reflexivity.
  Qed.

  (* Better *)
  Example plus2_complexity': ComplexityBound $(nat -> nat) plus2 (fun n => 2).
  Proof.
  change plus2 with (compose S S).
  (* Let's have another go *)
  capply.
  (* TODO: explicit type annotations are annoying *)
  eapply (compose_complexity (S : $(nat -> nat)) _ (S : $(nat -> nat))).
  - apply S_complexity.
  - apply S_complexity.
  Unshelve. simpl. auto.
  Qed.

  Example plus_complexity:
    ComplexityBound $(nat -> nat -> nat) plus (fun n => (val n + 1, fun m => 1 + 3 * val n)).
  (* TODO: I can't really explain the 3 * n  there *)
  Proof.
  change_fun_with (nat_rect _ id (fun k nk m => S (nk m))). Unshelve.
  capply.
  (* TODO: a tactic should handle this *)
  eapply (nat_complexity_rect1 (id : $(nat -> nat)) (fun _ => compose S)).
  - apply id0_complexity.
  - apply @constant_complexity. (* TODO: why is this only working with @? *)
    eapply (apply_complexity (v := S : $(nat -> nat))).
    + apply S_complexity.
    + apply comp1_complexity.
  - intro n. induction n; simpl; auto with *.
  Unshelve. simpl. unfold compose.
  unfold ℂT_order.
  
  intros [n ()]. simpl. split.
  * induction n; simpl; lia.
  * intro m. split; trivial. induction n; trivial. simpl. lia.
  Qed.

  Example plus_complexity':
    ComplexityBound $(nat -> nat -> nat) plus (fun n => (1, fun m => 2 + 3 * val n)).
  Proof.
  fold ℂT.
  capply. apply nat_fix1_complexity.
  - apply id0_complexity. 
  - apply (@constant_complexity $nat). (* the type annotation is necessary *)
    apply id0_complexity.
  - apply (@constant_complexity $nat).
    apply (@constant_complexity $nat).
    apply S_complexity.
  (* Now check the complexity bound. *)
  Unshelve.
  intros [n ()]. simpl. repeat split; trivial.
  induction n as [|n].
  + trivial.
  + destruct ca as [a ()]; simpl.
    repeat apply le_n_S. lia.
  Qed.

End NatTimeExamples.