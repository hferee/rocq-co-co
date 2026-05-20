From Complexity Require Import SimpleCostModel.
From Stdlib Require Import Program.Basics Lia.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

(*   Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat. *)
  
  (* Constructors *)
  Parameter O_complexity : ComplexityBound O tt. (* TODO: is this useful? *)
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : ℂI nat unit) => 1 ⋉ tt).
  Existing Instance S_complexity.

  (* Destructor *)
  Parameter nat_match_complexity: forall {A CA} (v : A) (f : nat -> A) (cv : CA) cf,
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    ComplexityBound 
      (fun n => match n with
                | O => v
                | S k => f k
                end)
      (fun (n : ℂI nat unit) => 1 ⊕ (* 1 for the match *)
                match ival n with
                | O => ret cv
                | S k => cf (k ⋊ tt)
                end).
  Existing Instance nat_match_complexity.

  Definition ℂI_nat_inj (n : nat) := n ⋊ tt.
  Coercion ℂI_nat_inj : nat >-> ℂI.

  (* Induction principle on nat, first for unary functions *)
  (* TODO: this should be derivable from nat_fix1_complexity below *)
  Parameter nat_complexity_rect1: forall {A CA} (v : A) (f : nat -> A -> A)
    (cv : CA) (cf: ℂI nat unit -> ℂO (ℂI A CA -> ℂO CA)),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    let g := nat_rect _ v f in
    ComplexityBound g
      (fun (cn : ℂI nat unit) => (nat_rect (fun n => ℂO (ℂI A CA)) (ret (v ⋊ cv))
                  (fun k gk =>
                    gk O>>=O ((k ⋊ tt I>>=I (f ⋊ cf)))) (ival cn)) >>|).

 (* TODO: are there (structural) fixpoints on nat that are not expressible this way?
  And can we write a tactic to turn most such functions into a nat_rect?
  And can we automatically prove they are extensionally equal? *)

  (* A quite general complexity bound for fixpoints over nat with 1 additional
    argument. Hopefully I got it right. *)
  (* fixpoint over nat with 1 additional argument *)
  Definition nat_fix1 (A B : Type) (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) :=
    fix f (n : nat) (x : A) : B := match n with O => v x | S k => F k x (f k (g k x)) end.

  Parameter nat_fix1_complexity : forall {A B CA CB : Type}
  (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) (cv : ℂI A CA -> ℂO CB) cg cF,
  let f := nat_fix1 A B v g F in
    ComplexityBound v cv ->
    ComplexityBound g (cg : ℂI nat unit -> ℂO (ℂI A CA -> ℂO CA)) ->
    ComplexityBound F (cF : ℂI nat unit -> ℂO (ℂI A CA -> ℂO (ℂI B CB -> ℂO CB))) ->
    ComplexityBound (f : nat -> A -> B)
      (fun (cn : ℂI nat unit) => 1 ⋉ fun (cx : ℂI A CA) =>
      (* The cost is accumumated in the output. This might not be the most convenient
      for later proofs *)
      ((fix cfix n (cx : ℂI A CA) : ℂO (ℂI B CB) := 1 ⊕
        match n with
      | O => cx I>>=I (v ⋊ cv)
      | S k => (* F k x (f k (g k x))*)
              (* the recursive call *)
              match (cx I>>=O (k I>>=I (g ⋊ cg))) with
              | {| ocost := cc; ocomp := call|} =>
              cc ⊕ (cfix k call)
               O>>=O (cx I>>=O (k ⋊ tt I>>=I (F ⋊ cF)))
              end
      end) (ival cn) cx >>|) : ℂO CB).

(* TODO check the costs above. *)
(* TODO: define binary and ternary applications *)

  Parameter bound_order_nat : forall (n m : nat),
    bound_order n m <-> n <= m.

End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel)
  (Import BT : BasicTimeCostModel CM) (Import B: NatTimeCostModel CM BT).

  Example plus2 (n : nat) := S (S n).
  (* TODO: here *)

  Example plus2_complexity: ComplexityBound plus2 (fun (n : ℂI nat unit) => 3 ⋉ tt).
  Proof.
  (* We get 4 and not 2, as we go through compose S S  *)
  change plus2 with (compose S S). (* NOTE: extensionality used here *)
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
  Example plus2_complexity': ComplexityBound plus2 (fun (n : ℂI nat unit) => 2 ⋉ tt).
  Proof.
  (* Another try, simpler, without extensionality *)
  capply.
  (* TODO: explicit type annotations are annoying *)
  eapply compose_complexity; apply S_complexity.
  Unshelve. apply bound_order_ext_eq. intros. unfold OIbindO. reflexivity.
  Qed.

   Example plus_complexity:
    ComplexityBound plus (fun (n : ℂI nat unit) => 2 * ival n ⋉
                          fun (m : ℂI nat unit) => (1 + 2 * ival n) ⋉ tt).
  (* TODO: Weirdly, n appears in both bounds (should only appear on the first? *)
  Proof.
  change_fun_with (nat_rect _ id (fun k => compose S)).
  capply.
  (* TODO: a tactic should handle this *)
  apply nat_complexity_rect1.
  - eapply id_complexity.
  - eapply constant_complexity.
    eapply apply_complexity.
    + apply S_complexity.
    + apply comp1_complexity.
  Unshelve.
  * apply ext_eq_dep_fun. intro n. apply ext_eq_dep_fun.
    intros m. apply ext_eq_eq. revert m; induction n; 
    unfold compose; simpl; auto with *.
  * (* TODO: automate this *)
    apply bound_order_ext_eq. intros. apply bound_order_output; split.
    -- simpl. induction (ival x); simpl; lia.
    -- simpl. apply bound_order_ext_eq. intro. 
       apply bound_order_output. split.
       ++ simpl. induction (ival x); simpl; lia.
       ++ apply bound_order_unit.
  Qed.

  Example plus_complexity':
    ComplexityBound plus (fun (n : ℂI nat unit) => 1 ⋉
                          fun (m : ℂI nat unit) => (6 * ival n + 2) ⋉ tt).
  Proof.
  unfold Nat.add.
  capply. apply nat_fix1_complexity.
  - apply id_complexity. 
  - apply (@constant_complexity). (* @ is necessary *)
    apply id_complexity.
  - apply (@constant_complexity).
    apply (@constant_complexity).
    apply S_complexity.
  (* Now check the complexity bound. *)
  Unshelve. 
  (* TODO: automate this *)
  apply bound_order_ext_eq; intro cn.
  apply bound_order_output; split; simpl; [trivial|].
  apply bound_order_ext_eq; intro cm.
  apply bound_order_output; split; simpl.
  + (* TODO: make this readable. *)
    destruct cn as [n ()]. simpl.
    destruct cm as [m ()]. simpl. fold plus.
    induction n as [|n]; simpl; lia.
  + apply bound_order_unit.
  Qed.
End NatTimeExamples.