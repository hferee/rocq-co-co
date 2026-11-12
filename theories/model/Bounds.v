(** * Linear and polynomial bounds

    [ComplexityBound f c] bounds the costs of [f] by any function [c] of its
    inputs. The usual classes of complexity bound them by a function of the
    sizes of the inputs only. [FirstOrderBound f g] states it for a first-order
    function [f], with any number of arguments: each application of [f] to
    its next argument costs at most [g ss], where [ss] are the sizes of the
    arguments given so far. [PolynomialBound f], [LinearBound f] and
    [ConstantBound f] state that [g] is a polynomial in these sizes ([poly],
    from [Poly], where they are shown to be higher-order polynomials), of
    degree at most [1] for [LinearBound], and [0] for [ConstantBound], as
    classes.

    The sizes are those of the cost model ([Size], whose instances are
    given by the models of the datatypes), so that the bounds speak of the
    sizes of the representations of the arguments.

    [Bounds] is included in the module type [CostModel], so that its classes
    are shared by all the analyses over a cost model. *)

From Complexity Require Import CostModelCore Poly.
From Complexity Require Export Advice.
From Stdlib Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** ** Facts on sizes

    [SizeFact x P]: [P] is a fact on the size of [x], typically a lower
    bound by the measure of [x] that costs use ([x < size x] for [nat],
    [length l < size l] for lists). The facts are derived from the axioms
    on sizes of the models, where they are needed (for example in
    [NatComplexity]), and [add_size_facts] adds the facts on the values whose
    sizes appear in the goal. *)
Class SizeFact {A} (x : A) (P : Prop) := size_fact : P.

Ltac add_size_facts :=
  repeat match goal with
  | |- context [@size _ _ ?x] =>
      lazymatch goal with
      | _ : context [@size _ _ x] |- _ => fail
      | _ => pose proof (size_fact (x := x))
      end
  end.

(** ** Choice of the constants

    The costs of a bound of [ComplexityBound] are polynomials in measures of
    the arguments ([n], [length l], [Pos.size_nat p], ...), each bounded by
    the size of the argument. [poly_of t] bounds the polynomial [t] by the
    sum [k] of its coefficients and its degree [d], its atoms being the
    measures. The polynomial of a bound is then [k * (1 + s_0 + .. +
    s_(n-1)) ^ d] in the sizes [s_i] of the [n] arguments ([k + k * (s_0 +
    .. + s_(n-1))] for a linear bound), and checked by [lia] or [nia]: the
    proofs do not depend on the constants of the bounds of
    [ComplexityBound]. *)

Ltac2 rec nat_value (t : constr) : int option :=
  lazy_match! t with
  | O => Some 0
  | S ?u => match nat_value u with Some n => Some (Int.add n 1) | None => None end
  | _ => None
  end.

Ltac2 imax (a : int) (b : int) : int := if Int.lt a b then b else a.

Ltac2 rec ipow (a : int) (e : int) : int :=
  if Int.equal e 0 then 1 else Int.mul a (ipow a (Int.sub e 1)).

Ltac2 not_polynomial (t : constr) :=
  Control.zero (Tactic_failure (Some (Message.concat
    (Message.of_string "not a polynomial: ") (Message.of_constr t)))).

Ltac2 rec poly_of (t : constr) : int * int :=
  match nat_value t with
  | Some n => (n, 0)
  | None =>
      lazy_match! t with
      | ?a + ?b => let (ka, da) := poly_of a in let (kb, db) := poly_of b in (Int.add ka kb, imax da db)
      | ?a * ?b => let (ka, da) := poly_of a in let (kb, db) := poly_of b in (Int.mul ka kb, Int.add da db)
      | ?a - _ => poly_of a
      | S ?a => let (ka, da) := poly_of a in (Int.add ka 1, da)
      | ?a ^ ?b =>
          match nat_value b with
          | Some e => let (ka, da) := poly_of a in (ipow ka e, Int.mul da e)
          | None => not_polynomial t
          end
      | _ => (1, 1)
      end
  end.

(** The largest sum of coefficients and degree of the costs of the goals
    [cost <= bound]. *)
Ltac2 cost_constants () : int * int :=
  let k := Ref.ref 0 in
  let d := Ref.ref 0 in
  Control.enter (fun () =>
    lazy_match! goal with
    | [ |- ?l <= _ ] =>
        let (kl, dl) := poly_of l in
        Ref.set k (imax (Ref.get k) kl); Ref.set d (imax (Ref.get d) dl)
    end);
  (Ref.get k, Ref.get d).

(** The numeral [n] (in the focused goal). *)
Ltac2 rec nat_constr (n : int) : constr :=
  if Int.equal n 0 then constr:(O) else let t := nat_constr (Int.sub n 1) in constr:(S $t).

(** The number of arguments: the length of the longest list of sizes. *)
Ltac2 rec list_length (t : constr) : int :=
  lazy_match! t with
  | cons _ ?u => Int.add 1 (list_length u)
  | _ => 0
  end.

Ltac2 arity () : int :=
  let n := Ref.ref 0 in
  Control.enter (fun () =>
    match! goal with
    | [ |- context [peval _ ?ss] ] => Ref.set n (imax (Ref.get n) (list_length ss))
    | [ |- _ ] => ()
    end);
  Ref.get n.

(** [s_i + .. + s_(n-1)] (in the focused goal). *)
Ltac2 rec psum (i : int) (n : int) : constr :=
  if Int.le n i then constr:(pconst 0)
  else
    let v := nat_constr i in
    let rest := psum (Int.add i 1) n in
    constr:(padd (pvar $v) $rest).

(** Instantiates the polynomial [?p] of the goals [cost <= peval ?p ss]. *)
Ltac2 instantiate_poly (mk : int -> int -> int -> constr) :=
  let (k, d) := cost_constants () in
  let n := arity () in
  Control.focus 1 1 (fun () =>
    lazy_match! goal with
    | [ |- _ <= peval ?p _ ] => Std.unify p (mk k d n)
    end).

Ltac2 linear_constants () :=
  instantiate_poly (fun k d n =>
    (if Int.lt 1 d then
       Control.zero (Tactic_failure (Some (Message.of_string "the costs are not linear")))
     else ());
    let k := nat_constr k in
    let s := psum 0 n in
    constr:(padd (pconst $k) (pmul (pconst $k) $s))).

Ltac2 constant_constants () :=
  instantiate_poly (fun k d _ =>
    (if Int.lt 0 d then
       Control.zero (Tactic_failure (Some (Message.of_string "the costs are not constant")))
     else ());
    let k := nat_constr k in
    constr:(pconst $k)).

(** The same as [linear_constants] and [constant_constants], but the
    polynomial is instantiated whatever the degree of the costs: the
    inequalities that cannot hold are left, and explained
    ([csolve_degree]). For the tactics used by hand; the hints, which try
    bounds that may not hold, use the failing versions. *)
Ltac2 linear_constants_any () :=
  instantiate_poly (fun k _ n =>
    let k := nat_constr k in
    let s := psum 0 n in
    constr:(padd (pconst $k) (pmul (pconst $k) $s))).

Ltac2 constant_constants_any () :=
  instantiate_poly (fun k _ _ => let k := nat_constr k in constr:(pconst $k)).

(** For each goal [cost <= bound]: if the degree of its cost is larger
    than [deg], the degree of the bound, it cannot hold for large values of
    the arguments, whatever the constants: it is left, and explained (and
    not given to [nia], which would search for a proof forever); otherwise
    [lia] or [nia] try to prove it. *)
Ltac2 degree_message (g : constr) (d : int) (deg : int) (kind : string) : unit :=
  Message.print (Advice.cat
    [Message.of_string "The inequality "; Message.of_constr g; Message.of_string " cannot hold:";
     Advice.nl (); Message.of_string "its left side, the cost found, has degree "; Message.of_int d;
     Message.of_string " in the arguments, and its right side, a "; Message.of_string kind;
     Message.of_string " bound, has degree "; Message.of_int deg; Message.of_string ".";
     Advice.nl (); Message.of_string "For large arguments the left side is the larger, whatever the constants: the function has no ";
     Message.of_string kind; Message.of_string " bound. Try a bound of a higher degree (PolynomialBound)."]).

Ltac2 csolve_degree (deg : int) (kind : string) : unit :=
  Control.enter (fun () =>
    let high :=
      match! goal with
      | [ |- ?l <= _ ] =>
          match Control.case (fun () => poly_of l) with
          | Val ((_, d), _) => if Int.lt deg d then Some d else None
          | Err _ => None
          end
      | [ |- _ ] => None
      end in
    match high with
    | Some d => degree_message (Control.goal ()) d deg kind
    | None => ltac1:(try solve [lia | nia])
    end).

Ltac2 polynomial_constants () :=
  instantiate_poly (fun k d n =>
    let k := nat_constr k in
    let d := nat_constr d in
    let s := psum 0 n in
    constr:(pmul (pconst $k) (ppow (padd (pconst 1) $s) $d))).

Module Bounds (Import CM : CostModelCore).

  (** ** First-order functions

      [FirstOrder A CA]: [A] is a type of functions whose arguments and
      result are ground data, with sizes for the arguments, and [CA] the type
      of their complexities. *)
  Inductive FirstOrder : Type -> Type -> Type :=
  | fo_res {B} : Ground B -> FirstOrder B unit
  | fo_arg {A B CB} : Ground A -> Size A -> FirstOrder B CB ->
      FirstOrder (A -> B) (ℂI A unit -> ℂO CB).
  Existing Class FirstOrder.
  Global Existing Instances fo_res fo_arg.

  (** The representation of a first-order type, the one found by typeclass
      search. *)
  Fixpoint fo_repr {A CA} (fo : FirstOrder A CA) : Repr A CA :=
    match fo in FirstOrder A CA return Repr A CA with
    | fo_res RB => RB
    | fo_arg RA _ fo => Repr_arr RA (fo_repr fo)
    end.

  (** [size_bound g ss]: the complexity in which each application to an
      argument costs [g] of the sizes of the arguments, [ss] being the sizes
      of those already given. *)
  Fixpoint size_bound {A CA} (fo : FirstOrder A CA) (g : list nat -> nat) (ss : list nat) : CA :=
    match fo in FirstOrder A CA return CA with
    | fo_res _ => tt
    | fo_arg _ SA fo => fun ca =>
        g (ss ++ [size (Size := SA) (val ca)]) +>
        size_bound fo g (ss ++ [size (Size := SA) (val ca)])
    end.

  (** ** Bounds *)

  Definition FirstOrderBound {A CA} `{fo : FirstOrder A CA} (f : A) (g : list nat -> nat) : Prop :=
    @ComplexityBound A (repr_ctype (H := fo_repr fo)) (fo_repr fo) f (size_bound fo g []).

  Class PolynomialBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    polynomial_bound : exists p, FirstOrderBound f (peval p).

  Class LinearBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    linear_bound : exists p, pdeg p <= 1 /\ FirstOrderBound f (peval p).

  Class ConstantBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    constant_bound : exists p, pdeg p = 0 /\ FirstOrderBound f (peval p).

  Lemma size_bound_mono {A CA} (fo : FirstOrder A CA) (g g' : list nat -> nat) s :
    (forall ss, g ss <= g' ss) ->
    bound_order (H := fo_repr fo) (size_bound fo g s) (size_bound fo g' s).
  Proof.
    intro Hg. revert s. induction fo as [B RB | A B CB RA SA fo IH]; intro s; cbn.
    - apply bound_order_ground.
    - apply bound_order_arr. intro ca. cbn. split; [apply Hg | apply IH].
  Qed.

  Lemma FirstOrderBound_mono {A CA} `{FirstOrder A CA} (f : A) (g g' : list nat -> nat) :
    (forall ss, g ss <= g' ss) -> FirstOrderBound f g -> FirstOrderBound f g'.
  Proof.
    intros Hg Hf. exact (ComplexityBound_mono _ _ _ (size_bound_mono _ _ _ [] Hg) Hf).
  Qed.

  (** A linear bound is a polynomial bound. *)
  Global Instance LinearBound_PolynomialBound {A CA} `{FirstOrder A CA} (f : A)
    {Hf : LinearBound f} : PolynomialBound f.
  Proof. destruct Hf as (p & _ & Hf). exists p. exact Hf. Qed.

  (** A constant bound is a linear bound. *)
  Global Instance ConstantBound_LinearBound {A CA} `{FirstOrder A CA} (f : A)
    {Hf : ConstantBound f} : LinearBound f.
  Proof. destruct Hf as (p & Hp & Hf). exists p. split; [lia | exact Hf]. Qed.

  (** ** Proofs of bounds

      [cost_split_by tac] reduces [FirstOrderBound f g] to inequalities
      between the costs of the bound of [f] given by [tac] (typeclass search
      in [cost_split]) and [g], with the facts on the sizes of the arguments
      ([add_size_facts]) and the constants of the model unfolded ([costs]).
      [cost_bound] proves them with [lia] or [nia].

      [cconstant], [clinear] and [cpolynomial] prove [ConstantBound f],
      [LinearBound f] and [PolynomialBound f] from the bound of [f] found by
      typeclass search, choosing the constants ([linear_constants]);
      [cconstant_using H], [clinear_using H] and [cpolynomial_using H] from
      the bound [H]. The inequalities that [lia]
      and [nia] do not prove are left, for example when they need facts on
      the measures of the arguments. *)
  Ltac cost_split_by tac :=
    unfold FirstOrderBound; cbn [fo_repr size_bound];
    eapply ComplexityBound_mono; [idtac | tac];
    bo_split; destr_inputs;
    cbv beta iota zeta delta [cost res val pot]; autounfold with costs;
    cbn -[Nat.mul size]; add_size_facts.
  Ltac cost_split := cost_split_by ltac:(typeclasses eauto).

  (** The bound of [f] found by typeclass search, or a message. *)
  Ltac cinstance :=
    first [typeclasses eauto
          | lazymatch goal with
            | |- ComplexityBound ?f _ =>
                fail 1 "no ComplexityBound instance is known for" f
                       ": prove one first (Global Instance ..., or Existing Instance after a Lemma),"
                       "or prove this bound with cbound, which analyses" f "itself"
            end].
  Ltac cost_bound := cost_split; try solve [lia | nia].

  Ltac clinear_by tac :=
    unfold LinearBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; linear_constants ()) in
      split tac; cbn [peval nth]; try solve [lia | nia]
    | cbn; lia ].
  Ltac clinear_core := clinear_by ltac:(typeclasses eauto).

  (** [clinear], [cconstant]: the same, but the polynomial is chosen
      whatever the costs, so that the inequalities that cannot hold are
      shown, and explained ([csolve_degree]). *)
  Ltac clinear_untimed :=
    unfold LinearBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; linear_constants_any ()) in
      split ltac:(cinstance); cbn [peval nth]; ltac2:(csolve_degree 1 "linear"); cadvice
    | cbn; lia ].
  Ltac clinear_using H := clinear_by ltac:(exact H).

  Ltac cconstant_by tac :=
    unfold ConstantBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; constant_constants ()) in
      split tac; cbn [peval nth]; try solve [lia | nia]
    | reflexivity ].
  Ltac cconstant_core := cconstant_by ltac:(typeclasses eauto).
  Ltac cconstant_untimed :=
    unfold ConstantBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; constant_constants_any ()) in
      split ltac:(cinstance); cbn [peval nth]; ltac2:(csolve_degree 0 "constant"); cadvice
    | reflexivity ].
  Ltac cconstant_using H := cconstant_by ltac:(exact H).

  Ltac cpolynomial_by tac :=
    unfold PolynomialBound; eexists;
    let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; polynomial_constants ()) in
    split tac;
    cbn [peval nth Nat.pow]; try solve [lia | nia].
  Ltac cpolynomial_core := cpolynomial_by ltac:(typeclasses eauto).
  Ltac cpolynomial_untimed := cpolynomial_by ltac:(cinstance); cadvice.
  Ltac cpolynomial_using H := cpolynomial_by ltac:(exact H).

  (** Bounds without an instance are derived from the bounds of
      [ComplexityBound] found by typeclass search, when [cconstant],
      [clinear] or [cpolynomial] proves them. *)
  (** The same within the timeout ([ctimeout], [Advice]). *)
  Ltac clinear := let f := ltac2:(t |- ctimed "clinear" t) in f ltac:(clinear_untimed).
  Ltac cconstant := let f := ltac2:(t |- ctimed "cconstant" t) in f ltac:(cconstant_untimed).
  Ltac cpolynomial := let f := ltac2:(t |- ctimed "cpolynomial" t) in f ltac:(cpolynomial_untimed).

  Global Hint Extern 10 (ConstantBound _) => solve [cconstant_core] : typeclass_instances.
  Global Hint Extern 10 (LinearBound _) => solve [clinear_core] : typeclass_instances.
  Global Hint Extern 10 (PolynomialBound _) => solve [cpolynomial_core] : typeclass_instances.
End Bounds.
