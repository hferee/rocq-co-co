From Complexity Require Import SimpleTypes ExecutionModel.
From Stdlib Require Import Classes.Morphisms Program.Basics Lia.
From Equations Require Import Equations.

(* Type of the complexity bounds for elements of a simple type. *)
(* This is inspired by Forster & Künze with two main changed:
   - the cost of a term of ground type is the cost of normalizing it,
     while they only consider the cost of normal forms ;
   - Every element is packaged with a normalisation cost and the
     complexity of its normal form. *)

(* Monad(?) to annotate inputs (in normal form) with their complexity bounds *)
(* In theory, cost could be something else than nat. *)
Record ℂI (A : Type) (CA : Type) := { val : A; icomp : CA }.
(* TODO: find better names, especially icomp *)
(* TODO: Not sure that the use of a record improves things, especially for
  ground types. Maybe do something like ℂO *)

Infix "⋊" := (Build_ℂI _ _) (at level 40).

Global Arguments val {_} {_}.
Global Arguments icomp {_} {_}.

(* Type builder meant to group the normalisation cost of a term together
  with its complexity bound. *)
Definition ℂO (t : SimpleType) (CA : Type) : Type :=
match t with
| SGround A => nat
| SFun A B => nat * CA
| SProd A B => nat * CA
end.

(* Annotate a complexity bound with a cost *)
Definition ℂO_pair {t : SimpleType} {CA : Type} (n : nat) (c : CA) : ℂO t CA.
Proof. destruct t; [exact n| |]; exact (n, c). Defined.
Infix "⋉" := ℂO_pair (at level 40).

(* The type of complexity bounds for normal forms of a given simple type *)
Fixpoint ℂT (t : SimpleType) : Type := match t with
| SGround A => unit
| SProd A B => ℂT A * ℂT B
| SFun A B => ℂI A (ℂT A) -> ℂO B (ℂT B)
end.

(* Immediate/ normalisation cost of an output *)
Definition cost {t CA} (b : ℂO t CA) : nat.
Proof. destruct t; [exact b| |]; exact (fst b). Defined.

(* Complexity of an output *)
Definition ocomp {t} (b : ℂO t (ℂT t)) : ℂT t.
Proof. destruct t; [exact tt| |]; exact (snd b). Defined.


Global Arguments ℂT !t : simpl nomatch. (* TODO: this doesn't work, it's still unfolded *)

(* Ordering on complexity bounds *)
Equations ℂT_order t (b1 b2 : ℂT t) : Prop :=
ℂT_order (SGround A) _ _ => True;
ℂT_order (SProd A B) b1 b2 =>
  ℂT_order A (fst b1) (fst b2) /\ ℂT_order B (snd b1) (snd b2);
ℂT_order (SFun A B) b1 b2 => forall ca, let b1' := b1 ca in let b2' := b2 ca in
  cost b1' <= cost b2' /\ ℂT_order B (ocomp b1') (ocomp b2').

Global Arguments ℂT_order {t} b1 b2.
Transparent ℂT_order.

(* TODO: all this mess is to hopefully obtain nice complexity bounds
  - that are what we hope for first order functions ;
  - that handle multiple arguments ;
  - more generally handle higher-order functions ;
  - The complexity of polymorphic functions can be expressed polymorphically. *)


Global Instance ℂT_order_refl t : Reflexive (@ℂT_order t).
Proof. induction t; intro x; autorewrite with ℂT_order; auto with *. Qed.

Global Instance ℂT_order_trans t : Transitive (@ℂT_order t).
Proof.
induction t as [A| A HA B HB | A HA B HB];
intros x y z.
- trivial.
- split; auto with *.
- autorewrite with ℂT_order.
  fold ℂT. (* TODO: how do I prevent the unfolding of ℂT? *)
  split; auto with *.
  transitivity (cost (y ca)); auto with *.
Qed.

(* Some execution models can be equipped with a notion of complexity *)
Module Type CostModel.

  (* An abstract notion of cost. This allows for multiple notions of cost
    (time, space, function calls, etc. *)

  (* I'm fixing the type of complexity measures to nat here for now. *)

  (* The complexity of an abstract term defined as a relation. *)
  (* We may require that it is monotone in the future *)
  Parameter has_complexity: forall {A : SimpleType}, A -> ℂT A -> Prop.

 (* Complexity is a monotone property *)
  Parameter has_complexity_ext_eq: forall {A},
    Proper ((ext_eq) ==> (ℂT_order) ==> impl) (@has_complexity A).
  Global Existing Instance has_complexity_ext_eq.

  Infix "has_complexity!" := has_complexity (at level 40).

  (* As Forster & Künze, we record complexity results using typeclasses. *)
  Class ComplexityBound A (f : Type_of_SimpleType A) c := {CB : has_complexity f c}.

  Global Instance ComplexityBound_proper {A}:
    Proper ((ext_eq) ==> (ℂT_order) ==> (impl)) (ComplexityBound A).
  Proof. intros ??????[?]. constructor. eapply has_complexity_ext_eq; eauto. Qed.

  (* Useful functions to express complexity bounds *)
  (* Cost of applying a function of (input) complexity cg to an argument
    of (input) complexity ca. *)
  Definition cost_apply {A B} (cg : @ℂI (SFun A B) (ℂT (SFun A B)))
    (ca : @ℂI A (ℂT A)) : nat := cost (icomp cg ca).

  (* Input complexity of an application. *)
  (* TODO: find better name *)
  Definition ℂI_apply {A B} (cg : @ℂI (SFun A B) (ℂT (SFun A B))) (ca : @ℂI A (ℂT A))
    : ℂI B (ℂT B) :=
    val cg (val ca) ⋊ ocomp (icomp cg ca).

  (* Adds a normalisation cost to a complexity bound *)
  Definition cost_add {t} (n : nat) (b : ℂO t (ℂT t)) : ℂO t (ℂT t).
  Proof. destruct t; [exact (n + b)| |]; exact (n + fst b, snd b). Defined.

  Global Infix "⊕" := cost_add (at level 60, right associativity).

  (* Complexity of producing a value *)
  Definition ovalue {t} (v : ℂT t) : ℂO t (ℂT t).
  Proof. destruct t; [exact (1)| |]; exact (1, v). (* 1? could be 0 *) Defined.
End CostModel.

(* A basic example of a cost model ; here, time complexity on base type nat. *)
(* It's a call-by-value time cost model *)
Module Type BasicTimeCostModel (Export CM : CostModel).

  (* Assume we know the cost of some basic functions *)
  (* General idea: we define a (complete) set of primitives and axiomatize their
  cost. These axioms are now the trust base, and users may not cheat, 
  or make mistakes anymore *)

  (* Identity on ground types *)
  (* TODO: compare with from coq-library-complexity. *)
  Parameter id0_complexity : forall {A} `{GroundType A},
    ComplexityBound $(A -> A) (@id A) (fun a => 1).
  Existing Instance id0_complexity.

  (* The complexity of the application function, i.e. identity on function types. *)
  (* We can give a general, polymorphic bound!
    A priori, this is not the case for coq-library-complexity. *)
  (* Note that the complexity of the identity is roughly the identity *)
  Parameter id_complexity : forall {A B},
    ComplexityBound $(SFun (SFun A B) (SFun A B)) (@id (A -> B))
      (fun cf => (1, icomp cf)).
  Existing Instance id_complexity.

  (* Complexity of the application of a function to an argument *)
  Parameter apply_complexity : forall {A B : SimpleType} {v : A} {f cv cf},
    ComplexityBound A v cv ->
    ComplexityBound $(A -> B) f cf ->
    ComplexityBound B (f v) (ocomp (cf (v ⋊ cv))).

    (* TODO : notation for putting back v and cv together *)

  (* Unary composition *)
  (* It produces a value whose complexity is obtained by composing the complexity
     of the three inputs ; the normalisation cost is obtained by two successive
     applications. *)
  Parameter comp1_complexity : forall {A B C : SimpleType},
  ComplexityBound $((B -> C) -> (A -> B) -> (A -> C)) compose
    (fun cf => (1, fun cg => (1, fun ca =>
      1 + cost_apply cg ca + cost_apply cf (ℂI_apply cg ca)
      ⊕ icomp cf (ℂI_apply cg ca)))).
  Existing Instance comp1_complexity.

  (* More convenient: the instantiation direct application of compose.
    TODO: do we need both? *)
  Parameter compose_complexity : forall {A B C : SimpleType} f cf g cg,
  ComplexityBound $(B -> C) f cf ->
  ComplexityBound $(A -> B) g cg ->
  ComplexityBound $(A -> C) (compose f g)
    (fun ca =>
      cost (cg ca) ⊕ cf (ℂI_apply (g ⋊ cg) ca)).
  Existing Instance compose_complexity.

  (* Axioms that are more specific to nat *)

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
End BasicTimeCostModel.

Module BasicTimeExamples (CM : CostModel) (Import B: BasicTimeCostModel CM).

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
  Unshelve.
  fold ℂT. (* TODO: annoying *)
  (* also, explicit type annotations are annoying *)
  constructor; simpl; trivial.
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
  Unshelve.
  constructor; simpl; trivial.
  Qed.

  Program Example plus_complexity:
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
  Unshelve. unfold compose. simpl. intros [n ()]. simpl. split.
  * induction n; simpl; lia.
  * intro m. split; trivial. induction n; trivial. simpl. lia.
  Qed.

  Program Example plus_complexity':
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

End BasicTimeExamples.
