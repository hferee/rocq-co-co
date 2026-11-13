(** * One axiom for all fixpoints

    A Gallina axiom cannot quantify over the syntax of [fix] terms (their
    number of arguments, recursive argument, mutual functions, ...). Instead,
    [fix_complexity] uses the unfolding equation of a recursive function:
    `f e a = F (ECons e (f e)) a` (pointwise in all the arguments). Here
    `f e` is the recursive function whose free variables are the values of
    the environment `e`, as for any closure ([Combinators]); the functional
    `F` is the code of the body of the fixpoint, in the environment `e`
    extended with the recursive function itself, read from it by the
    recursive calls. The candidate complexity [cf] of [f] is a bound as soon
    as it bounds the cost of building the closure `f e` ([c_clo]), and of
    one unfolding, plus [c_fix], where the recursive calls cost what [cf]
    says.

    This covers any structural recursion (any arity, recursive argument in
    any position, matches on other arguments, recursive calls on deeper
    subterms, polymorphic fixpoints), through an indexed function mutual
    recursion, and fixpoints with free variables, such as [fold_left], a
    fixpoint under `fun f`: `f` is in the environment, and the recursive
    calls do not pass it again. A closed recursive function is the case of
    the empty environment [tt] ([fix_closed_complexity]), where the
    recursive calls read the function in [ECons tt f].

    Since the axiom holds for every function satisfying the equation,
    [ComplexityBound f c] now means that the function [f] is computable within
    [c], rather than that a particular term defining it is. This is sound
    because each unfolding costs at least one ([c_fix ⊕] below, with
    [1 <= c_fix]): the recurrence cannot be satisfied by an unfolding that
    does not terminate. With free unfoldings, every function would have every
    bound ([UnguardedFix]). The condition is a premise of the rule, not an
    axiom, so that a model where [c_fix] is [0] stays consistent: its
    recursive functions cannot be analysed. *)

From Complexity Require Export TimeCombinators.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** An input that is an environment, split into its two parts ([crec_env]),
    so that the goals name the arguments of the environment as the claimed
    bound does, rather than after the fields of the records. *)
Lemma env_input_split {E A CE CA} (P : ℂI (env E A) (CE * CA) -> Prop) :
  (forall (ce : ℂI E CE) (ca : ℂI A CA), P (ECons (val ce) (val ca) ⋊ (pot ce, pot ca))) ->
  forall c, P c.
Proof. intros H [[e a] [pe pa]]. exact (H (e ⋊ pe) (a ⋊ pa)). Qed.

(** The functional of a recursive function is compiled with the combinators
    ([crec] leaves it to [cbc]): this module type depends on their model. As
    for the combinators, the model of fixpoints ([FixTimeCostModel], at the
    end) is made of its axioms, of the rules derived from them
    ([FixRules], which its instances include) and of the tactics that they
    justify, in functors ([FixTactics]). *)
Module Type FixTimeCostAxioms
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT).

  (** The cost of an unfolding. *)
  Parameter c_fix : nat.
  #[global] Hint Unfold c_fix : costs.

  (** For a recursive function [f e] with the environment [e]: its
      functional [F] runs in [e] extended with [f e]. *)
  Parameter fix_complexity : forall {E CE A B CA CB} `{Repr E CE} `{Repr A CA} `{Repr B CB}
    (ar : Arity B) (f : E -> A -> B)
    (F : env E (A -> B) -> A -> B)
    (cF : ℂI (env E (A -> B)) (CE * (ℂI A CA -> ℂO CB)) -> ℂO (ℂI A CA -> ℂO CB))
    (cf : ℂI E CE -> ℂO (ℂI A CA -> ℂO CB)),
    1 <= c_fix ->
    (forall e, is_fixpoint ar (fun g => F (ECons e g)) (f e)) ->
    ComplexityBound F cF ->
    bound_order
      (fun ce : ℂI E CE => c_clo +> fun ca : ℂI A CA =>
         c_fix ⊕ pot <$> (F ⋊ cF) · (ECons (val ce) (f (val ce)) ⋊ (pot ce, res (cf ce))) · ca)
      cf ->
    ComplexityBound f cf.
End FixTimeCostAxioms.

(** The rules derived from the axiom, included in its instances. *)
Module FixRules
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import FX : FixTimeCostAxioms CM BT CB).

  (** ** Closed recursive functions

      A closed recursive function [f] is [f' tt], for the function [f']
      of an empty environment: its functional runs in [ECons tt f], and
      reads [f] in it ([ehd]). The cost of building the closure [f' tt] is
      not that of [f], a value. *)
  Lemma fix_closed_complexity : forall {A B CA CB} `{Repr A CA} `{Repr B CB}
    (ar : Arity B) (f : A -> B) (F : env unit (A -> B) -> A -> B)
    (cF : ℂI (env unit (A -> B)) (unit * (ℂI A CA -> ℂO CB)) -> ℂO (ℂI A CA -> ℂO CB))
    (cf : ℂI A CA -> ℂO CB),
    1 <= c_fix ->
    is_fixpoint ar (fun g => F (ECons tt g)) f ->
    ComplexityBound F cF ->
    bound_order (fun ca : ℂI A CA => c_fix ⊕ pot <$> (F ⋊ cF) · (ECons tt f ⋊ (tt, cf)) · ca) cf ->
    ComplexityBound f cf.
  Proof.
    intros A B CA CB RA RB ar f F cF cf Hpos Hfix HF Hrec.
    assert (H : ComplexityBound (fun _ : unit => f) (fun _ => c_clo +> cf)).
    { apply (fix_complexity ar (fun _ => f) F cF (fun _ => c_clo +> cf) Hpos).
      - intros []. exact Hfix.
      - exact HF.
      - apply bound_order_arr. intros [[] []]. split; [apply Nat.le_refl | exact Hrec]. }
    exact (apply_complexity _ tt_complexity H).
  Qed.
End FixRules.

Module Type FixTimeCostRules
  (CM : CostModel) (BT : BasicTimeCostModel CM) (CB : CombinatorTimeCostModel CM BT) :=
  FixTimeCostAxioms CM BT CB <+ FixRules CM BT CB.

Module FixTactics
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM)
  (Import CB : CombinatorTimeCostModel CM BT) (Import FX : FixTimeCostRules CM BT CB).

  (** In a goal [ComplexityBound f cf] where [f] is a recursive function,
      [crec] leaves the goals `ComplexityBound F ?cF` (to be solved by
      [cbc]) and the recurrence on [cf]. [fix_equation] gives the
      functional `FF` of [f], over the recursive function: `F` is `FF`
      reading it in the environment ([ehd]), beta-reduced, so that each
      recursive call reads it. [crec_mutual] does the same for
      [fun b => if b then f1 else f2], where [f1] and [f2] are mutually
      recursive. The premise [1 <= c_fix] is proved by [cfix_pos], from the
      value of [c_fix] or from a hypothesis. *)
  Ltac cfix_pos := solve [assumption | autounfold with costs; lia].
  Ltac crec_with eq :=
    let H := fresh "Hunfold" in
    let Hpos := fresh "Hpos" in
    eq; intro H; assert (Hpos : 1 <= c_fix) by cfix_pos;
    lazymatch type of H with
    | is_fixpoint ?ar ?FF ?f =>
        let F := eval cbv beta in (fun eg : env unit _ => FF (ehd eg)) in
        eapply (fix_closed_complexity ar f F _ _ Hpos H)
    end; clear H Hpos.
  Ltac crec := crec_with fix_equation.
  Ltac crec_mutual := crec_with fix_equation_mutual.

  (** ** Arguments passed unchanged

      [crec_env] is for a recursive function [h] some of whose arguments
      are passed unchanged by every recursive call ([env_fix]): the
      function of the parameters of a section ([fold_left]), the first
      arguments ([Nat.pow], [rec_pos]), or the second of two ([app],
      [Nat.add], [Nat.mul]). They are the environment of the fixpoint, the
      function [ef_f] of [fix_complexity], and the recursive calls do not
      pass them again. [h] is [ef_f] itself when there is one of them,
      first; otherwise [h] is built from [ef_f] by closures ([Lam]) or by
      [Cc], whose bounds give the one of [h] from the bound [cf] of
      [ef_f]. [cf] is taken from the claimed bound [ch] of [h]: the cost of
      the closure [ef_f e] ([c_clo]), then what [ch] gives once all the
      arguments of the environment are given; for [Cc], the cost of [Cc]
      and of the closure are taken off the cost that [ch] gives. *)

  (** The types [T], [C] and [X] of a complexity of type
      [ℂI T C -> ℂO X]. *)
  Ltac2 dest_bound_type (t : constr) : constr * constr * constr :=
    let fail () := fail_msg "crec_env: unexpected type of bound" in
    match Constr.Unsafe.kind (Std.eval_hnf t) with
    | Constr.Unsafe.Prod b body =>
        let (ta, ca) := match Constr.Unsafe.kind (Std.eval_hnf (Constr.Binder.type b)) with
                        | Constr.Unsafe.App _ a => if Int.equal (Array.length a) 2
                                     then (Array.get a 0, Array.get a 1) else fail ()
                        | _ => fail () end in
        let x := match Constr.Unsafe.kind (Std.eval_hnf (lower body)) with
                 | Constr.Unsafe.App _ a => if Int.equal (Array.length a) 1 then Array.get a 0 else fail ()
                 | _ => fail () end in
        (ta, ca, x)
    | _ => fail ()
    end.

  (** The complexity types [C1; ..; Ck] of the first [k] arguments. *)
  Ltac2 rec bound_ctypes (k : int) (t : constr) : constr list :=
    if Int.equal k 0 then []
    else let (_, c, x) := dest_bound_type t in c :: bound_ctypes (Int.sub k 1) x.

  (** [C1], [C1 * C2], [(C1 * C2) * C3], ...: the complexity type of an
      environment ([Repr_env]), and its components. *)
  Ltac2 rec prod_type (cs : constr list) : constr :=
    match List.rev cs with
    | [] => constr:(unit)
    | c :: [] => c
    | c :: rest => let p := prod_type (List.rev rest) in constr:(($p * $c)%type)
    end.
  Ltac2 rec prod_values (cs : constr list) (p : constr) : constr list :=
    match List.rev cs with
    | [] => []
    | _ :: [] => [p]
    | _ :: rest => List.append (prod_values (List.rev rest) constr:(fst $p)) [constr:(snd $p)]
    end.

  (** [cf] for [k >= 2] arguments passed unchanged, first. *)
  Ltac2 env_bound_prefix (ef : env_fix) (ch : constr) : constr :=
    let tys := ef.(ef_tys) in
    let cs := bound_ctypes (List.length tys) (Constr.type ch) in
    let ee := ef.(ef_E) in
    let ce_ty := prod_type cs in
    Constr.in_context @ce constr:(ℂI $ee $ce_ty) (fun () =>
      let ce := Control.hyp @ce in
      let cps := List.map2 (fun v p => constr:($v ⋊ $p))
                   (env_values tys constr:(val $ce)) (prod_values cs constr:(pot $ce)) in
      let rec apply_all x cps :=
        match cps with [] => x | cp :: cps => apply_all constr:(res $x $cp) cps end in
      let x := match cps with
               | cp :: cps => apply_all constr:($ch $cp) cps
               | [] => fail_msg "crec_env" end in
      Control.refine (fun () => constr:(c_clo +> res $x))).

  (** The names of the arguments of a bound [fun cx => k +> fun cy => ..]
      ([n] of them), or default names. *)
  Ltac2 rec bound_names (n : int) (c : constr) : ident list :=
    if Int.equal n 0 then []
    else
      let dflt := Option.default (Fresh.fresh (Fresh.Free.of_ids []) @c) in
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Lambda b body =>
          let nm := dflt (Constr.Binder.name b) in
          let rest := match Constr.Unsafe.kind body with
                      | Constr.Unsafe.App _ a =>
                          if Int.equal (Array.length a) 3 then Array.get a 2 else body
                      | _ => body end in
          nm :: bound_names (Int.sub n 1) rest
      | _ => dflt None :: bound_names (Int.sub n 1) c
      end.

  (** [cf] for [h l m] where only [m] is passed unchanged: its arguments
      have the names of those of [ch], so that the proof scripts can refer
      to them. *)
  Ltac2 env_bound_swap (ch : constr) : constr :=
    let (t1, c1, x) := dest_bound_type (Constr.type ch) in
    let (t2, c2, _) := dest_bound_type x in
    let (n1, n2) := match bound_names 2 ch with
                    | n1 :: n2 :: _ => (n1, n2)
                    | _ => (@cl, @cm) end in
    let (n1, n2) := if Ident.equal n1 n2 then (@cl, @cm) else (n1, n2) in
    Constr.in_context n2 constr:(ℂI $t2 $c2) (fun () =>
      let cm := Control.hyp n2 in
      let inner := Constr.in_context n1 constr:(ℂI $t1 $c1) (fun () =>
        let cl := Control.hyp n1 in
        Control.refine (fun () =>
          constr:((cost (res ($ch $cl) $cm) - (c_step + c_frame + c_clo)) +> res (res ($ch $cl) $cm)))) in
      Control.refine (fun () => constr:(c_clo +> $inner))).

  Ltac clear_wrappers := repeat match goal with H : ComplexityBound _ _ |- _ => clear H end.

  (** Split the input [h], an environment of the arguments [names] (the
      first one first), into one input for each of them, named [names]. *)
  Ltac2 rec split_env_input (h : ident) (names : ident list) :=
    match List.rev names with
    | [] => ()
    | n :: [] => Std.rename [(h, n)]
    | nk :: rest_rev =>
        let h' := Fresh.in_goal @ce in
        ltac1:(h h' nk |- revert h; apply env_input_split; intros h' nk)
          (Ltac1.of_ident h) (Ltac1.of_ident h') (Ltac1.of_ident nk);
        split_env_input h' (List.rev rest_rev)
    end.

  Ltac2 crec_env () :=
    match Constr.Unsafe.kind (Control.goal ()) with
    | Constr.Unsafe.App _ gargs =>
        let i := Int.sub (Array.length gargs) 2 in
        let h := Array.get gargs i in
        let ch := Array.get gargs (Int.add i 1) in
        let ef := env_fix h in
        fix_equation_env ef;
        let hu := Fresh.in_goal @Hunfold in
        Std.intro (Some hu) None;
        let hp := Fresh.in_goal @Hpos in
        ltac1:(hp |- assert (hp : 1 <= c_fix) by cfix_pos) (Ltac1.of_ident hp);
        let ar := ef.(ef_ar) in
        let f := ef.(ef_f) in
        let fF0 := ef.(ef_F) in
        let fF := lift_cases fF0 in
        let tys := ef.(ef_tys) in
        let k := List.length tys in
        let swap := ef.(ef_swap) in
        if Bool.and (Bool.neg swap) (Int.equal k 1) then
          ltac1:(ar f F H Hp |- eapply (fix_complexity ar f F _ _ Hp H); clear H Hp)
            (Ltac1.of_constr ar) (Ltac1.of_constr f) (Ltac1.of_constr fF)
            (Ltac1.of_ident hu) (Ltac1.of_ident hp)
        else
          let cf := if swap then env_bound_swap ch else env_bound_prefix ef ch in
          let hf := Fresh.in_goal @Hf in
          ltac1:(ar f F H Hp cf Hf |-
                   assert (Hf : ComplexityBound f cf);
                   [eapply (fix_complexity ar f F _ cf Hp H); clear H Hp | clear H Hp])
            (Ltac1.of_constr ar) (Ltac1.of_constr f) (Ltac1.of_constr fF)
            (Ltac1.of_ident hu) (Ltac1.of_ident hp) (Ltac1.of_constr cf) (Ltac1.of_ident hf);
          (* the recurrence, for each argument of the environment, named as in [ch] *)
          (if swap then () else
             Control.focus 2 2 (fun () =>
               let names := List.map (fun n => Fresh.in_goal n) (bound_names k ch) in
               let ce := Fresh.in_goal @ce in
               ltac1:(ce |- apply bound_order_arr; intro ce) (Ltac1.of_ident ce);
               split_env_input ce names;
               ltac1:(split)));
          (* the bound of [h], from the one of [f] *)
          let n := Control.numgoals () in
          Control.focus n n (fun () =>
            let rec lams j x :=
              if Int.equal j 0 then x
              else lams (Int.sub j 1) (mkapp constr:(@Lam) [| hole (); hole (); hole (); x |]) in
            let w := if swap then mkapp constr:(@Cc) [| hole (); hole (); hole (); f |]
                     else lams (Int.sub k 1) f in
            replace_goal_arg i w;
            let rec wrap hc j :=
              if Int.equal j 0 then hc
              else
                let hn := Fresh.in_goal @Hw in
                (if swap then
                   ltac1:(hc hn |- pose proof (apply_complexity _ hc Cc_complexity) as hn)
                     (Ltac1.of_ident hc) (Ltac1.of_ident hn)
                 else
                   ltac1:(hc hn |- pose proof (apply_complexity _ hc Lam_complexity) as hn)
                     (Ltac1.of_ident hc) (Ltac1.of_ident hn));
                wrap hn (Int.sub j 1) in
            let hw := wrap hf (if swap then 1 else Int.sub k 1) in
            ltac1:(hw |- eapply ComplexityBound_mono; [| exact hw]) (Ltac1.of_ident hw);
            ltac1:(clear_wrappers))
    | _ => fail_msg "crec_env: unexpected goal"
    end.
  Ltac crec_env := ltac2:(crec_env ()).

  (** ** Proofs of bounds

      [cbound] ([TimeCombinators]) extended to recursive functions: if
      the function is recursive, its functional is compiled and the
      recurrence of [fix_complexity] is reduced to inequalities between
      costs; otherwise, the previous [cbound_start] applies. The extension
      holds in every model with fixpoints, and so in the hint of
      [TimeCombinators] for bounds without instance. Mutually recursive
      functions [f1] and [f2] are analysed together, as the function
      [fun b => if b then f1 else f2] ([crec_mutual]); [cproject] then gives
      the bound of each one. [cbound_mutual] is the same, for mutually
      recursive functions only. A recursive function with arguments passed
      unchanged is analysed with them in the environment of its fixpoint
      ([crec_env]), which is tried first. *)
  Ltac2 Set cbound_start as previous := fun () =>
    let rec first_rec tacs :=
      match tacs with
      | [] => previous ()
      | t :: tacs =>
          match Control.case t with
          | Val _ => Control.focus 1 1 (fun () => ltac1:(cbc_found))
          | Err _ => first_rec tacs
          end
      end in
    first_rec [crec_env; (fun () => ltac1:(crec)); (fun () => ltac1:(crec_mutual))].
  Ltac cbound_mutual := crec_mutual; [cbc_found | cfinish].
End FixTactics.

Module Type FixTimeCostModel
  (CM : CostModel) (BT : BasicTimeCostModel CM) (CB : CombinatorTimeCostModel CM BT) :=
  FixTimeCostAxioms CM BT CB <+ FixRules CM BT CB <+ FixTactics CM BT CB.

