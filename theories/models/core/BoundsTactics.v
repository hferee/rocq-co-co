(** * Tactics for the bounds

    The tactics that prove the bounds of [Bounds]: the facts on the sizes
    and on the values, one form per atom for [lia] ([cnorm_types]), the
    choice of the constants of the polynomials, and [cconstant], [clinear]
    and [cpolynomial]. *)

From Complexity Require Import CostModelCore GroundTypes Poly Bounds.
From Complexity Require Export Advice.
From Stdlib Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** The constants of the costs, declared by the generic cost model
    ([c_S], [c_cons], ...), their order and operations ([cle], [cplus],
    ...), and the functions that costs use ([czip_option]): the tactics
    unfold them ([autounfold with costs], created in [CostModelCore]), so
    that a constant fixed by a model becomes a number, and an abstract one
    stays an atom for [lia]. The bounds themselves are instances of
    [ComplexityBound]. *)

(** ** One form per atom

    [lia] and [nia] compare their atoms syntactically, and an atom may have
    several forms. [cnorm_types] gives it one: it unfolds the projections
    [val] and [pot] (primitive, with two forms that print the same), the
    sizes with their instances, the type aliases in the arguments of the
    functions ([@length clause l] and [@length (list nat) l]), and runs
    [cnorm_hook], which the libraries extend with the forms of their own
    functions ([ListCosts] for the sums of lists). *)

(** A size is normalised with its instance. *)
Ltac cnorm_size T S x :=
  let U := eval cbv in T in
  let R := eval cbv in S in
  tryif (constr_eq T U; constr_eq S R) then fail
  else (progress (change (@size T S x) with (@size U R x) in *)).

(** A type alias: a type headed by a definition, closed, with its head
    normal form. *)
Ltac2 is_data_sort (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Sort _ => Bool.neg (Bool.or (Constr.equal t constr:(Prop)) (Constr.equal t constr:(SProp)))
  | _ => false
  end.

Ltac2 alias (c : constr) : (constr * constr) option :=
  let head := match Constr.Unsafe.kind c with Constr.Unsafe.App h _ => h | _ => c end in
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Constant _ _ =>
      if Constr.Unsafe.is_closed c then
        if is_data_sort (Std.eval_hnf (Constr.type c)) then
          let u := Std.eval_hnf c in
          if Constr.equal c u then None else Some (c, u)
        else None
      else None
  | _ => None
  end.

(** The first alias, not in [seen], among the arguments of the
    applications in [c]. *)
Ltac2 rec find_alias (seen : constr list) (c : constr) : (constr * constr) option :=
  let r := Ref.ref None in
  let visit t := match Ref.get r with Some _ => () | None => Ref.set r (find_alias seen t) end in
  (match Constr.Unsafe.kind c with
   | Constr.Unsafe.App _ args =>
       Array.iter (fun a =>
         match Ref.get r with
         | Some _ => ()
         | None =>
             match alias a with
             | Some (t, u) => if List.exist (Constr.equal t) seen then () else Ref.set r (Some (t, u))
             | None => ()
             end
         end) args
   | _ => ()
   end);
  Constr.Unsafe.iter visit c;
  Ref.get r.

(** Unfolds the aliases of the goal and of the hypotheses, one by one. *)
Ltac2 cnorm_aliases () :=
  Control.enter (fun () =>
    let rec loop seen :=
      let r := Ref.ref (find_alias seen (Control.goal ())) in
      List.iter (fun (_, _, t) =>
        match Ref.get r with None => Ref.set r (find_alias seen t) | Some _ => () end) (Control.hyps ());
      match Ref.get r with
      | Some (t, u) =>
          ltac1:(t u |- try change t with u in * ) (Ltac1.of_constr t) (Ltac1.of_constr u);
          loop (t :: seen)
      | None => ()
      end in
    loop []).

Ltac2 mutable cnorm_hook : unit -> unit := fun () => ().

(** The facts that the proofs of a file give to the arithmetic of [cbound],
    after those on the values: none by default. *)
Ltac2 mutable cfacts_hook : unit -> unit := fun () => ().

Ltac cnorm_types :=
  try unfold val in *; try unfold pot in *;
  (* the measure of costs: in [nat], the cost itself *)
  try autounfold with measures in *;
  repeat match goal with
  | |- context [@size ?T ?S ?x] => cnorm_size T S x
  | _ : context [@size ?T ?S ?x] |- _ => cnorm_size T S x
  end;
  ltac2:(cnorm_aliases (); cnorm_hook ()).

(** ** Facts for the tactics

    [SizeFact x P]: a fact [P] on the size of [x]. [ValueFact x P]: a fact
    [P x] on the value [x] of a function that [lia] cannot derive, such as
    [length (filter p l) <= length l]. Both are registered with the
    functions, and added by the tactics ([add_size_facts],
    [add_value_facts]). *)
Class SizeFact {A} (x : A) (P : Prop) := size_fact : P.
Class ValueFact {A} (x : A) (P : A -> Prop) := value_fact : P x.
#[global] Hint Mode ValueFact - ! - : typeclass_instances.

Ltac add_size_facts :=
  repeat match goal with
  | |- context [@size _ _ ?x] =>
      lazymatch goal with
      | _ : context [@size _ _ x] |- _ => fail
      | _ => pose proof (size_fact (x := x))
      end
  end;
  cnorm_types.


(** A fact is known if it, or its first part, is a hypothesis. *)
Ltac value_fact_known T :=
  lazymatch T with
  | ?A /\ _ => value_fact_known A
  | _ => lazymatch goal with _ : T |- _ => idtac end
  end.

Ltac add_value_facts :=
  repeat match goal with
  | |- context [?x] =>
      (* no fact on the arithmetic and the logic of the inequalities *)
      lazymatch x with
      | _ + _ => fail | _ * _ => fail | _ - _ => fail | S _ => fail | O => fail
      | Nat.max _ _ => fail | Nat.min _ _ => fail
      | _ <= _ => fail | _ < _ => fail | _ /\ _ => fail | _ = _ => fail
      | _ => idtac
      end;
      let H := constr:(value_fact (x := x)) in
      let T := type of H in
      let T := eval cbv beta in T in
      tryif value_fact_known T then fail
      else (let F := fresh "Hv" in pose proof (H : T) as F; decompose [and] F)
  end;
  cnorm_types.

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

(** ** Polynomial bounds by monotonicity *)

(** [cmono_le X]: [t <= ?u], with [?u] the term [t] in which each measure
    (an atom) is replaced by [X], by monotonicity. *)
Ltac cmono_le X :=
  lazymatch goal with
  | |- ?a + ?b <= _ => eapply Nat.add_le_mono; [cmono_le X | cmono_le X]
  | |- ?a * ?b <= _ => eapply Nat.mul_le_mono; [cmono_le X | cmono_le X]
  | |- ?a - ?b <= _ => eapply Nat.le_trans; [apply Nat.le_sub_l | cmono_le X]
  | |- S ?a <= _ => eapply le_n_S; cmono_le X
  | |- 0 <= _ => apply le_n
  | |- ?m <= _ => let H := fresh in assert (H : m <= X) by lia; exact H
  end.

Ltac2 rec prodX (x : constr) (i : int) : constr :=
  if Int.equal i 0 then constr:(1) else let p := prodX x (Int.sub i 1) in constr:($x * $p).

(** The degree [d] of [X * (X * ... 1)]. *)
Ltac2 rec xdeg (x : constr) (t : constr) : int :=
  lazy_match! t with
  | ?a * ?b => if Constr.equal a x then Int.add 1 (xdeg x b) else 0
  | _ => 0
  end.

Ltac2 cpow_chain (x : constr) (hx : constr) (d : int) : unit :=
  let rec go i :=
    if Int.lt i d then
      (let p := prodX x i in
       ltac1:(x p hx |- pose proof (Nat.mul_le_mono_r 1 x p hx))
         (Ltac1.of_constr x) (Ltac1.of_constr p) (Ltac1.of_constr hx);
       go (Int.add i 1))
    else () in
  go 0.

(** [cmono_poly]: [cost <= k * (X * (... * 1))], the goal of a polynomial
    bound ([polynomial_constants]), where [X] is [1] plus the sizes and [k]
    the sum of the coefficients of the cost: each measure of the cost is at
    most [X] (by [lia], from the facts on the sizes), and each power of [X]
    at most [X ^ d]. [nia] may not find these products, for a degree [d]
    above [2]. *)
Ltac2 cmono_poly () :=
  lazy_match! goal with
  | [ |- _ <= _ * (?x * ?r) ] =>
      let d := Int.add 1 (xdeg x r) in
      ltac1:(x |- assert (1 <= x) by lia) (Ltac1.of_constr x);
      let hx := Control.hyp (match List.last_opt (Control.hyps ()) with Some (h, _, _) => h | None => Control.throw Not_found end) in
      ltac1:(x |- eapply Nat.le_trans; [cmono_le x |]) (Ltac1.of_constr x);
      cpow_chain x hx d;
      ltac1:(lia)
  end.
Ltac cmono_poly := ltac2:(cmono_poly ()).

(** For each goal [cost <= bound]: if the degree of its cost is larger
    than [deg], the degree of the bound, it cannot hold for large values of
    the arguments, whatever the constants: it is left, and explained (and
    not given to [nia], which would search for a proof forever); otherwise
    [lia] or [nia] try to prove it. *)
(** The hypotheses of a case (a test [(10 <? n) = false], or [n <= 10])
    may bound the arguments: the inequality may then hold, with constants
    that the degree does not give. *)
Ltac2 bounded_case () : bool :=
  List.exist (fun (_, body, ty) =>
    match body with
    | Some _ => false
    | None => lazy_match! ty with
              | _ = true => true | _ = false => true
              | _ <= ?k => Option.is_some (nat_value k)
              | _ < ?k => Option.is_some (nat_value k)
              | _ => false end
    end) (Control.hyps ()).

Ltac2 degree_message (g : constr) (d : int) (deg : int) (kind : string) : unit :=
  let tail :=
    if bounded_case () then
      [Message.of_string "For large arguments the left side is the larger, unless the hypotheses of the case bound them (a test, say):";
       Advice.nl (); Message.of_string "then prove a bound in their values first (ComplexityBound, as an instance), from which this one follows."]
    else
      [Message.of_string "For large arguments the left side is the larger, whatever the constants: the function has no ";
       Message.of_string kind; Message.of_string " bound. Try a bound of a higher degree (PolynomialBound)."] in
  Message.print (Advice.cat (List.append
    [Message.of_string "The inequality "; Message.of_constr g;
     Message.of_string (if bounded_case () then " may not hold:" else " cannot hold:");
     Advice.nl (); Message.of_string "its left side, the cost found, has degree "; Message.of_int d;
     Message.of_string " in the arguments, and its right side, a "; Message.of_string kind;
     Message.of_string " bound, has degree "; Message.of_int deg; Message.of_string ".";
     Advice.nl ()] tail)).

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
    | None => ltac1:(first [solve [lia] | solve [cmono_poly] | cnia])
    end).

Ltac2 polynomial_constants () :=
  instantiate_poly (fun k d n =>
    let k := nat_constr k in
    let d := nat_constr d in
    let s := psum 0 n in
    constr:(pmul (pconst $k) (ppow (padd (pconst 1) $s) $d))).


(** The tactics that use the definitions of [Bounds]. *)
Module Type BoundsModel := GroundCostModel <+ CostSizes <+ Bounds.

Module BoundsTactics (Import CM : BoundsModel).
  (** ** Proofs of bounds

      [cost_split_by tac] reduces [FirstOrderBound f g] to inequalities
      between the costs of the bound of [f] given by [tac] (typeclass search
      in [cost_split]) and [g] ([size_costs]), with the facts on the sizes of
      the arguments ([add_size_facts]) and the constants of the model
      unfolded ([costs]).

      [cconstant], [clinear] and [cpolynomial] prove [ConstantBound f],
      [LinearBound f] and [PolynomialBound f] from the bound of [f] found by
      typeclass search, choosing the constants ([linear_constants]);
      [clinear_using H] from the bound [H]. The inequalities that [lia]
      and [nia] do not prove are left, for example when they need facts on
      the measures of the arguments. *)

  (** Decompose [bound_order] goals into inequalities between costs. The
      arguments of functions are named as in the right-hand side (usually
      the claimed bound). *)
  Ltac bo_split :=
    repeat match goal with
    | |- @bound_order _ (_ -> _) _ _ ?c =>
        let c := eval hnf in c in
        apply bound_order_arr;
        lazymatch c with
        | fun x => _ => let y := fresh x in intro y
        | _ => intro
        end;
        let w := fresh "Hwf" in intro w;
        split
    | |- @bound_order _ _ _ _ _ => solve [apply ground_order]
    end;
    (* the order of the costs: [le] in time *)
    try unfold cle.

  (** The inputs of ground data ([IsGround], found by typeclass search) are
      replaced by their values, which keep the names of the inputs: their
      complexities carry no information. *)
  Ltac destr_inputs :=
    repeat match goal with
    | c : ℂI _ unit |- _ => let v := fresh "v" in destruct c as [v []]; rename v into c
    | c : ℂI ?A ?C |- _ =>
        let _ := constr:(_ : IsGround (_ : Repr A C)) in
        let v := fresh "v" in let p := fresh "p" in destruct c as [v p]; rename v into c
    end.

  (** Replaces the complexity bound with an evar. The complexity bound goal
      will eventually need to be taken from the shelf. *)
  Ltac capply := eapply ComplexityBound_mono; [shelve|].

  (** The goals of [size_costs]: one inequality per application. *)
  Ltac sc_split :=
    cbn [size_costs];
    repeat match goal with
    | |- forall _, _ => intro
    | |- _ /\ _ => split
    | |- True => exact I
    end.

  Ltac cost_split_by tac :=
    unfold FirstOrderBound; cbn [fo_repr];
    eexists; split; [tac | sc_split];
    destr_inputs;
    cbv beta iota zeta delta [cost res val pot cle cnat]; autounfold with costs;
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

  Ltac clinear_by tac :=
    unfold LinearBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; linear_constants ()) in
      split tac; cbn [peval nth]; first [solve [lia] | cnia_now]
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
      split tac; cbn [peval nth]; first [solve [lia] | cnia_now]
    | reflexivity ].
  Ltac cconstant_core := cconstant_by ltac:(typeclasses eauto).
  Ltac cconstant_untimed :=
    unfold ConstantBound; eexists; split; cycle 1;
    [ let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; constant_constants_any ()) in
      split ltac:(cinstance); cbn [peval nth]; ltac2:(csolve_degree 0 "constant"); cadvice
    | reflexivity ].

  Ltac cpolynomial_by tac :=
    unfold PolynomialBound; eexists;
    let split := ltac2:(t |- ltac1:(t |- cost_split_by t) t; polynomial_constants ()) in
    split tac;
    cbn [peval nth Nat.pow]; first [solve [lia] | solve [cmono_poly] | cnia_now].
  Ltac cpolynomial_core := cpolynomial_by ltac:(typeclasses eauto).
  Ltac cpolynomial_untimed := cpolynomial_by ltac:(cinstance); cadvice.

  (** Bounds without an instance are derived from the bounds of
      [ComplexityBound] found by typeclass search, when [cconstant],
      [clinear] or [cpolynomial] proves them. *)
  (** The same within the timeout ([ctimeout], [Advice]). *)
  Ltac clinear := let f := ltac2:(t |- ctimed "clinear" t) in f ltac:(idtac; clinear_untimed).
  Ltac cconstant := let f := ltac2:(t |- ctimed "cconstant" t) in f ltac:(idtac; cconstant_untimed).
  Ltac cpolynomial := let f := ltac2:(t |- ctimed "cpolynomial" t) in f ltac:(idtac; cpolynomial_untimed).

  Global Hint Extern 10 (ConstantBound _) => solve [cconstant_core] : typeclass_instances.
  Global Hint Extern 10 (LinearBound _) => solve [clinear_core] : typeclass_instances.
  Global Hint Extern 10 (PolynomialBound _) => solve [cpolynomial_core] : typeclass_instances.
End BoundsTactics.
