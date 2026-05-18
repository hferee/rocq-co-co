(* From Complexity Require Import CostModel.
From Stdlib Require Import Program.Basics Lia.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).
  Parameter GTnat : GroundType nat.
  Existing Instance GTnat. (* assume nat has ground Type *)

  (* Constructors *)
  Parameter O_complexity : ComplexityBound $nat O tt. (* TODO: is this useful? *)
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound $(nat -> nat) S (fun x => 1).
  Existing Instance S_complexity.

  (* Destructor *)
  Parameter nat_match_complexity: forall {A : SimpleType} v f cv cf,
    ComplexityBound A v cv ->
    ComplexityBound $(nat -> A) f cf ->
    ComplexityBound $(nat -> A)
      (fun n => match n with
                | O => v
                | S k => f k
                end)
      (fun n => 1 ⊕ (* 1 for the match *)
                match val n with
                | O => ovalue cv
                | S k => cf (k ⋊ tt)
                end).
  Existing Instance nat_match_complexity.

  (* Induction principle on nat, first for unary functions *)
  Parameter nat_complexity_rect1: forall {A : SimpleType} (v : A) f cv cf,
    ComplexityBound $A v cv ->
    ComplexityBound $(nat -> A -> A) f cf ->
    let g := nat_rect _ v f in
    ComplexityBound $(nat -> A) g
      (compose (nat_rect (fun n => ℂO A(ℂT A)) (ovalue cv)
                         (fun k gk => (cost gk + cost (cf (k ⋊ tt)) ⊕ (* TODO not sure *)
                                       ocomp (cf (k ⋊ tt))
                         (nat_rect _ v f k ⋊ ocomp gk)))) val).
  (* TODO: define more elegantly?... *)
 
 (* TODO: are there (structural) fixpoints on nat that are not expressible this way?
  And can we write a tactic to turn most such functions into a nat_rect?
  And can we automatically prove they are extensionally equal? *)

  (* A quite general complexity bound for fixpoints over nat with 1 additional
    argument. Hopefully I got it right. *)
  (* fixpoint over nat with 1 additional argument *)
  Definition nat_fix1 (A B : Type) (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) :=
    fix f (n : nat) (x : A) : B := match n with O => v x | S k => F k x (f k (g k x)) end.

  Parameter nat_fix1_complexity : forall (A B : SimpleType) v g F cv cg cF,
  let f := nat_fix1 A B v g F in
    ComplexityBound $(A -> B) v cv ->
    ComplexityBound $(nat -> A -> A) g cg ->
    ComplexityBound $(nat -> A -> B -> B) F cF ->
    ComplexityBound ($(nat -> A -> B)) f
      (fun cn => (1, fun cx => 
      (fix cfix n (cx : ℂI A (ℂT A)) := 1 ⊕
      match n with
      | O => cv cx
      | S k => let ck := k ⋊ tt in
               let gkx := g k (val cx) in
               let cgkx := ocomp (cg ck) cx in
               let cx' := (gkx ⋊ ocomp cgkx) in
               let fkg := f k gkx in
               let cfkg := cfix k cx' in
               (* TODO: streamline the cost of applying a function with multiple arguments *)
               (cost (cg ck) + cost cgkx + cost cfkg + cost (cF ck) + cost (ocomp (cF ck) cx)) ⊕ 
               ocomp (ocomp (cF ck) cx) (fkg ⋊ ocomp (cfix k cx'))
      end) (val cn) cx)).

  Parameter constant_complexity : forall {A B: SimpleType} {b cb},
    ComplexityBound B b cb ->
    ComplexityBound $(A -> B) (fun _ => b) (fun _ => 0 ⋉ cb).

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

End NatTimeExamples. *)