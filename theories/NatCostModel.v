From Complexity Require Import CostModel HOCostModel.
From Stdlib Require Import Program.Basics Lia.

(* An example of a cost model for time complexity  *)
(* It's a call-by-value time cost model *)
Module Type NatTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

(*   Parameter CT_nat: CT nat unit.
  Existing Instance CT_nat. *)
  
  (* Constructors *)
  (* TODO: is this useful? One could even have forall n, ComplexityBound n tt*)
  Parameter O_complexity : ComplexityBound O tt.
  Existing Instance O_complexity.

  Parameter S_complexity : ComplexityBound S (fun (x : ℂI nat unit) => 1 ⋉ tt).
  Existing Instance S_complexity.

  (** ** Destructor *)
  (* It seems that one could derive this bound from nat_fix1_complexity,
    but that would require an extentional notion of complexity. *)
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

 (* TODO: are there (structural) fixpoints on nat that are not expressible this way?
  And can we write a tactic to turn most such functions into a nat_rect?
  And can we automatically prove they are extensionally equal? *)

  (* Simple recursion with no additional argument *)
  Definition nat_fix0 (B : Type) (v : B) (F : nat -> B -> B) :=
    fix f (n : nat) : B := match n with O => v | S k => F k (f k) end.

  Parameter nat_fix0_complexity : forall {B CB : Type}
  (v : B) (F : nat -> B -> B) (cv : CB) cF,
  let f := nat_fix0 B v F in
    ComplexityBound v cv ->
    ComplexityBound F (cF : ℂI nat unit -> ℂO (ℂI B CB -> ℂO CB)) ->
    ComplexityBound (f : nat -> B)
      (fun (cn : ℂI nat unit) =>
      ((fix cfix n : ℂO (ℂI B CB) := 1 ⊕
        match n with
      | O => ret (v ⋊ cv)
      | S k => (* the recursive call *)
              cfix k O>>=O (k ⋊ tt I>>=I (F ⋊ cF))
      end) (ival cn) >>|) : ℂO CB).

  (* Induction principle on nat, first for unary functions *)
  (* TODO: this should be derivable from nat_fix0_complexity *)
  Lemma nat_complexity_rect1: forall {A CA} (v : A) (f : nat -> A -> A)
    (cv : CA) (cf: ℂI nat unit -> ℂO (ℂI A CA -> ℂO CA)),
    ComplexityBound v cv ->
    ComplexityBound f cf ->
    let g := nat_rect _ v f in
    ComplexityBound g
      (fun (cn : ℂI nat unit) => (nat_rect (fun n => ℂO (ℂI A CA)) (1 ⊕ ret (v ⋊ cv))
                  (fun k gk =>
                    gk O>>=O ((k ⋊ tt I>>=I (f ⋊ cf)))) (ival cn)) >>|).
  Proof. Abort.

  (* A quite general complexity bound for fixpoints over nat with 1 additional
    argument. Hopefully I got it right. *)
  (* fixpoint over nat with 1 additional argument *)
  Definition nat_fix1 (A B : Type) (v : A -> B) (g : nat -> A -> A) (F : nat -> A -> B -> B) :=
    fix f (n : nat) (x : A) : B := match n with O => v x | S k => F k x (f k (g k x)) end.

  Fixpoint nat_fix1_bound {A B CA CB : Type} v cv g cg F cF n (cx : ℂI A CA) :
    ℂO (ℂI B CB) := 1 ⊕
        match n with
      | O => cx I>>=I (v ⋊ cv)
      | S k => (* F k x (f k (g k x))*)
              (* the recursive call *)
              match (cx I>>=O (k I>>=I (g ⋊ cg))) with
              | {| ocost := cc; ocomp := call|} =>
              cc ⊕ (nat_fix1_bound v cv g cg F cF k call)
               O>>=O (cx I>>=O (k ⋊ tt I>>=I (F ⋊ cF)))
              end
      end.
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
      (nat_fix1_bound v cv g cg F cF (ival cn) cx >>|) : ℂO CB).
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

End NatTimeCostModel.

Module NatTimeExamples (Import CM : CostModel)
  (Import BT : BasicTimeCostModel CM) (Import B: NatTimeCostModel CM BT).

  Example plus2 (n : nat) := S (S n).

  Example plus2_complexity: ComplexityBound plus2 (fun (n : ℂI nat unit) => 2 ⋉ tt).
  Proof.
  (* Another try, simpler, without extensionality *)
  capply.
  (* TODO: explicit type annotations are annoying *)
  eapply compose_complexity; apply S_complexity.
  Unshelve. apply bound_order_ext_eq. intros. unfold OIbindO. reflexivity.
  Qed.

  Example plus_complexity:
    ComplexityBound Nat.add (fun (n : ℂI nat unit) => 1 ⋉
                          fun (m : ℂI nat unit) => (6 * ival n + 2) ⋉ tt).
  Proof.
  capply.
  ctac. (* applies nat_fix1_complexity,constant_complexity, id_complexity, S_complexity *)
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
  
  Existing Instance plus_complexity.
(* Axiom a_n a_m c_m: nat.
  Example mult_complexity:
    ComplexityBound Nat.mul (fun (n : ℂI nat unit) => 1 ⋉
                             fun (m : ℂI nat unit) => (ival n * (ival m + 3) + 2) ⋉ tt).
  Proof.
  capply. (* ctac. *)
  apply nat_fix1_complexity; [ctac| ctac | apply constant_complexity, plus_complexity].
  (* ,constant_complexity, id_complexity, plus_complexity *)
  (* Now check the complexity bound. *)
  Unshelve. 
  (* TODO: automate this *)
  apply bound_order_ext_eq; intro cn.
  apply bound_order_output; split; [trivial|].
  apply bound_order_ext_eq; intro cm.
  apply bound_order_output; split.
  + (* TODO: make this readable. *)
(*     match goal with | |- context[ocomp ?f] => remember f as foo end. *)
    destruct cn as [n ()].
    destruct cm as [m ()].
    induction n as [|n].
    * simpl. lia.
    * simpl. simpl in IHn. lia. firstorder. rewrite <- Heqfoo. simpl.
      fold (Nat.mul m 6). lia. rewrite Heqfoo; simpl; rewrite <- Heqfoo. lia.
  + apply bound_order_unit.
  Qed. *)
End NatTimeExamples.