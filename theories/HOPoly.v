(** * Higher-order polynomials

    The polynomials over the natural numbers at all simple types: the
    functionals obtained from the natural numbers, addition and
    multiplication by application and the combinators [K] and [S]
    ([is_hpoly]). By combinatory completeness, they are the denotations of
    the λ-terms over [+] and [×]. At type [N ⇒ .. ⇒ N] they contain the usual
    polynomials ([poly], [poly_hpoly]); at type 2 they contain the
    second-order polynomials of Kapron and Cook. They bound the basic
    feasible functionals ([BFFFeasibility]).

    [hpoly] proves that a λ-term over [+], [×] and numbers is a higher-order
    polynomial, by bracket abstraction ([BracketCompile]).

    B. M. Kapron, S. A. Cook. A new characterization of type-2 feasibility.
    SIAM Journal on Computing 25(1):117-132, 1996.

    M. Bezem. Strongly majorizable functionals of finite type: a model for
    bar recursion containing discontinuous functionals. Journal of Symbolic
    Logic 50(3):652-660, 1985. *)

From Complexity Require Import Combinators Compile BracketCompile.
From Stdlib Require Import Arith Lia List Program.Basics.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** ** Types and functionals *)

(** Simple types over a base type of natural numbers. *)
Inductive ty : Type := tN | tArr (σ τ : ty).
Infix "⇒" := tArr (at level 60, right associativity).

Fixpoint M (σ : ty) : Type := match σ with tN => nat | σ ⇒ τ => M σ -> M τ end.

(** ** Higher-order polynomials *)

Inductive is_hpoly : forall σ, M σ -> Prop :=
| hp_const (n : nat) : is_hpoly tN n
| hp_add : is_hpoly (tN ⇒ tN ⇒ tN) Nat.add
| hp_mul : is_hpoly (tN ⇒ tN ⇒ tN) Nat.mul
| hp_K σ τ : is_hpoly (σ ⇒ τ ⇒ σ) (fun x _ => x)
| hp_S σ τ ρ : is_hpoly ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ) (fun f g x => f x (g x))
| hp_app σ τ f x : is_hpoly (σ ⇒ τ) f -> is_hpoly σ x -> is_hpoly τ (f x).

(** The combinators of [Combinators] are higher-order polynomials. *)
Lemma hp_Kc σ τ : is_hpoly (σ ⇒ τ ⇒ σ) (@Kc (M σ) (M τ)).
Proof. exact (hp_K σ τ). Qed.

Lemma hp_Sc σ τ ρ : is_hpoly ((σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ) (@Sc (M σ) (M τ) (M ρ)).
Proof. exact (hp_S σ τ ρ). Qed.

(** [I = S K K]. *)
Lemma hp_Ic σ : is_hpoly (σ ⇒ σ) (@Ic (M σ)).
Proof. exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_S σ (σ ⇒ σ) σ) (hp_K σ (σ ⇒ σ))) (hp_K σ σ)). Qed.

(** [B = S (K S) K]. *)
Lemma hp_compose σ τ ρ : is_hpoly ((τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ) (@compose (M σ) (M τ) (M ρ)).
Proof.
  exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_S (τ ⇒ ρ) (σ ⇒ τ ⇒ ρ) ((σ ⇒ τ) ⇒ σ ⇒ ρ))
    (hp_app _ _ _ _ (hp_K _ (τ ⇒ ρ)) (hp_S σ τ ρ))) (hp_K (τ ⇒ ρ) σ)).
Qed.

(** [C = S (B B S) (K K)]. *)
Lemma hp_Cc σ τ ρ : is_hpoly ((σ ⇒ τ ⇒ ρ) ⇒ τ ⇒ σ ⇒ ρ) (@Cc (M σ) (M τ) (M ρ)).
Proof.
  exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_S (σ ⇒ τ ⇒ ρ) (τ ⇒ σ ⇒ τ) (τ ⇒ σ ⇒ ρ))
    (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_compose _ _ _) (hp_compose _ _ _)) (hp_S σ τ ρ)))
    (hp_app _ _ _ _ (hp_K _ _) (hp_K τ σ))).
Qed.

Create HintDb hpoly.
#[global] Hint Resolve hp_add hp_mul hp_K hp_S hp_Kc hp_Sc hp_Ic hp_compose hp_Cc : hpoly.

(** [hpoly] proves a goal [is_hpoly σ m], for a λ-term [m] built from
    numbers, [+], [×], and other higher-order polynomials (from the hint
    database [hpoly] or the hypotheses). [m] is replaced by a convertible
    term of combinators ([BracketCompile]), whose applications are split,
    the types of the arguments being read from their Rocq types. *)
Ltac2 rec reify_ty_norm (t : constr) : constr :=
  lazy_match! t with
  | nat => constr:(tN)
  | M ?s => s
  | ?a -> ?b => let a := reify_ty_norm a in let b := reify_ty_norm b in constr:($a ⇒ $b)
  | _ =>
      (* [M σ] unfolded by unification: the fixpoint of [M] applied to [σ] *)
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App h args =>
          match Constr.Unsafe.kind h with
          | Constr.Unsafe.Fix _ _ _ _ => Array.get args 0
          | _ => Control.zero Match_failure
          end
      | _ => Control.zero Match_failure
      end
  end.

(** The type of the functionals of type [t] ([cbn] folds most of the
    unfoldings of [M] that unification leaves). *)
Ltac2 reify_ty (t : constr) : constr := reify_ty_norm (Std.eval_cbn RedFlags.all t).

Ltac2 rec hp_solve () :=
  lazy_match! goal with
  | [ |- is_hpoly ?s ?t ] =>
      let leaf () :=
        lazy_match! t with
        | @Kc ?a ?b => let a := reify_ty a in let b := reify_ty b in exact (hp_Kc $a $b)
        | @Sc ?x ?a ?b =>
            let x := reify_ty x in let a := reify_ty a in let b := reify_ty b in
            exact (hp_Sc $x $a $b)
        | @Ic ?a => let a := reify_ty a in exact (hp_Ic $a)
        | @compose ?a ?b ?c =>
            let a := reify_ty a in let b := reify_ty b in let c := reify_ty c in
            exact (hp_compose $a $b $c)
        | @Cc ?x ?a ?b =>
            let x := reify_ty x in let a := reify_ty a in let b := reify_ty b in
            exact (hp_Cc $x $a $b)
        | Nat.add => exact hp_add
        | Nat.mul => exact hp_mul
        | _ =>
            lazy_match! s with
            | tN => exact (hp_const $t)
            | _ => ltac1:(solve [eauto with hpoly])
            end
        end in
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App f args =>
          let n := Array.length args in
          let x := Array.get args (Int.sub n 1) in
          let u := Constr.Unsafe.make (Constr.Unsafe.App f (Array.sub args 0 (Int.sub n 1))) in
          Control.plus
            (fun () =>
               lazy_match! s with
               | tN => exact (hp_const $t)
               | _ =>
                   let sx := reify_ty (Constr.type x) in
                   refine '(hp_app $sx $s $u $x _ _); Control.enter hp_solve
               end)
            (fun _ => leaf ())
      | _ => leaf ()
      end
  end.

Ltac2 hpoly () :=
  lazy_match! goal with
  | [ |- is_hpoly ?s ?m ] =>
      replace_goal_arg 1 (bracket_compile m);
      (* the types of the abstracted variables, lost by bracket abstraction *)
      lazy_match! goal with
      | [ |- is_hpoly _ ?t ] => Std.unify (Constr.type t) constr:(M $s)
      end;
      hp_solve ()
  end.

Ltac hpoly := ltac2:(hpoly ()).

(** ** Strong majorization

    [mle σ x y]: [y] majorizes [x], pointwise and hereditarily, on
    arguments related in the same way. A functional is monotone when it
    majorizes itself. *)
Fixpoint mle (σ : ty) : M σ -> M σ -> Prop :=
  match σ with
  | tN => le
  | σ ⇒ τ => fun f g => forall x y, mle σ x y -> mle τ (f x) (g y)
  end.

Definition monotone (σ : ty) (x : M σ) : Prop := mle σ x x.

(** ** Constructions *)

(** The constant [0] at any type, the value at [0]s, and the addition of a
    number at every argument. *)
Fixpoint botM (σ : ty) : M σ := match σ with tN => 0 | σ ⇒ τ => fun _ => botM τ end.

Fixpoint baseM (σ : ty) : M σ -> nat :=
  match σ with tN => fun n => n | σ ⇒ τ => fun f => baseM τ (f (botM σ)) end.

Fixpoint plusM (σ : ty) : nat -> M σ -> M σ :=
  match σ with tN => Nat.add | σ ⇒ τ => fun k f x => plusM τ k (f x) end.

Lemma hp_botM σ : is_hpoly σ (botM σ).
Proof. induction σ as [|σ _ τ IH]; [exact (hp_const 0)|]. cbn. hpoly. Qed.

Lemma hp_baseM σ : is_hpoly (σ ⇒ tN) (baseM σ).
Proof.
  induction σ as [|σ _ τ IH]; [exact (hp_Ic tN)|]. pose proof (hp_botM σ). cbn. hpoly.
Qed.

Lemma hp_plusM σ : is_hpoly (tN ⇒ σ ⇒ σ) (plusM σ).
Proof. induction σ as [|σ _ τ IH]; [exact hp_add|]. cbn. hpoly. Qed.

#[global] Hint Resolve hp_botM hp_baseM hp_plusM : hpoly.

Lemma mle_bot σ : monotone σ (botM σ).
Proof. induction σ as [|σ _ τ IH]; cbn; [lia | intros; apply IH]. Qed.

Lemma baseM_mono σ x y : mle σ x y -> baseM σ x <= baseM σ y.
Proof.
  revert x y; induction σ as [|σ _ τ IH]; intros x y H; [exact H|].
  apply IH, H, mle_bot.
Qed.

Lemma baseM_plus σ k x : baseM σ (plusM σ k x) = k + baseM σ x.
Proof. revert x; induction σ as [|σ _ τ IH]; intro x; [reflexivity | apply IH]. Qed.

Lemma mle_plus σ k k' x y : k <= k' -> mle σ x y -> mle σ (plusM σ k x) (plusM σ k' y).
Proof.
  revert x y; induction σ as [|σ _ τ IH]; intros x y Hk H; cbn in *; [lia|].
  intros a b Hab. apply IH, H, Hab. exact Hk.
Qed.

(** ** Usual polynomials

    Polynomials with natural coefficients in variables [pvar i], evaluated
    on the list of the values of the variables, [0] for those that are
    missing. They are the bounds of [Bounds] (in the sizes of the arguments
    of a function), and they are higher-order polynomials ([poly_hpoly]). *)
Inductive poly : Type :=
| pconst (k : nat)
| pvar (i : nat)
| padd (p q : poly)
| pmul (p q : poly)
| ppow (p : poly) (d : nat).

Fixpoint peval (p : poly) (ss : list nat) : nat :=
  match p with
  | pconst k => k
  | pvar i => nth i ss 0
  | padd p q => peval p ss + peval q ss
  | pmul p q => peval p ss * peval q ss
  | ppow p d => peval p ss ^ d
  end.

Fixpoint pdeg (p : poly) : nat :=
  match p with
  | pconst _ => 0
  | pvar _ => 1
  | padd p q => Nat.max (pdeg p) (pdeg q)
  | pmul p q => pdeg p + pdeg q
  | ppow p d => pdeg p * d
  end.

(** The type [N ⇒ .. ⇒ N] of the functions of [n] numbers, the application
    of such a function to a list, and the translation of a polynomial in
    [n] variables. *)
Fixpoint nary (n : nat) : ty := match n with 0 => tN | S n => tN ⇒ nary n end.

Fixpoint applyN (n : nat) : M (nary n) -> list nat -> nat :=
  match n with
  | 0 => fun f _ => f
  | S n => fun f ss => applyN n (f (hd 0 ss)) (tl ss)
  end.

Fixpoint constN (n : nat) : nat -> M (nary n) :=
  match n with 0 => fun k => k | S n => fun k _ => constN n k end.

Fixpoint projN (n i : nat) : M (nary n) :=
  match n, i with
  | 0, _ => 0
  | S n, 0 => constN n
  | S n, S i => fun _ => projN n i
  end.

Fixpoint addN (n : nat) : M (nary n ⇒ nary n ⇒ nary n) :=
  match n with 0 => Nat.add | S n => fun f g x => addN n (f x) (g x) end.

Fixpoint mulN (n : nat) : M (nary n ⇒ nary n ⇒ nary n) :=
  match n with 0 => Nat.mul | S n => fun f g x => mulN n (f x) (g x) end.

Fixpoint powN (n d : nat) (f : M (nary n)) : M (nary n) :=
  match d with 0 => constN n 1 | S d => mulN n f (powN n d f) end.

Fixpoint ptrans (n : nat) (p : poly) : M (nary n) :=
  match p with
  | pconst k => constN n k
  | pvar i => projN n i
  | padd p q => addN n (ptrans n p) (ptrans n q)
  | pmul p q => mulN n (ptrans n p) (ptrans n q)
  | ppow p d => powN n d (ptrans n p)
  end.

Lemma hp_constN n : is_hpoly (tN ⇒ nary n) (constN n).
Proof. induction n as [|n IH]; [exact (hp_Ic tN)|]. cbn. hpoly. Qed.

Lemma hp_projN n i : is_hpoly (nary n) (projN n i).
Proof.
  revert i; induction n as [|n IH]; intros [|i]; cbn; try exact (hp_const 0);
    [apply hp_constN | specialize (IH i); hpoly].
Qed.

Lemma hp_addN n : is_hpoly (nary n ⇒ nary n ⇒ nary n) (addN n).
Proof. induction n as [|n IH]; [exact hp_add|]. cbn. hpoly. Qed.

Lemma hp_mulN n : is_hpoly (nary n ⇒ nary n ⇒ nary n) (mulN n).
Proof. induction n as [|n IH]; [exact hp_mul|]. cbn. hpoly. Qed.

Lemma hp_ptrans n p : is_hpoly (nary n) (ptrans n p).
Proof.
  induction p as [k|i|p IHp q IHq|p IHp q IHq|p IHp d]; cbn.
  - apply (hp_app _ _ _ _ (hp_constN n) (hp_const k)).
  - apply hp_projN.
  - exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_addN n) IHp) IHq).
  - exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_mulN n) IHp) IHq).
  - induction d as [|d IHd]; cbn.
    + apply (hp_app _ _ _ _ (hp_constN n) (hp_const 1)).
    + exact (hp_app _ _ _ _ (hp_app _ _ _ _ (hp_mulN n) IHp) IHd).
Qed.

Lemma applyN_constN n k ss : applyN n (constN n k) ss = k.
Proof. revert ss; induction n; intro ss; [reflexivity | apply IHn]. Qed.

Lemma applyN_projN n i ss : length ss = n -> applyN n (projN n i) ss = nth i ss 0.
Proof.
  revert i ss; induction n as [|n IH]; intros i ss Hl.
  - destruct ss; [destruct i; reflexivity | discriminate].
  - destruct ss as [|s ss]; [discriminate|]. destruct i; cbn.
    + apply applyN_constN.
    + apply IH. cbn in Hl. lia.
Qed.

Lemma applyN_addN n f g ss : applyN n (addN n f g) ss = applyN n f ss + applyN n g ss.
Proof. revert f g ss; induction n; intros; [reflexivity | apply IHn]. Qed.

Lemma applyN_mulN n f g ss : applyN n (mulN n f g) ss = applyN n f ss * applyN n g ss.
Proof. revert f g ss; induction n; intros; [reflexivity | apply IHn]. Qed.

(** Every polynomial in [n] variables is (the uncurried form of) a
    higher-order polynomial of type [N ⇒ .. ⇒ N]. *)
Theorem poly_hpoly n p :
  is_hpoly (nary n) (ptrans n p) /\
  forall ss, length ss = n -> applyN n (ptrans n p) ss = peval p ss.
Proof.
  split; [apply hp_ptrans|]. intros ss Hl.
  induction p as [k|i|p IHp q IHq|p IHp q IHq|p IHp d]; cbn [ptrans peval].
  - apply applyN_constN.
  - apply applyN_projN, Hl.
  - rewrite applyN_addN, IHp, IHq. reflexivity.
  - rewrite applyN_mulN, IHp, IHq. reflexivity.
  - induction d as [|d IHd]; cbn [powN Nat.pow].
    + apply applyN_constN.
    + rewrite applyN_mulN, IHp, IHd. reflexivity.
Qed.

(** ** Growth

    A higher-order polynomial of type [N ⇒ N] is bounded by a polynomial
    ([hpoly_growth]). The proof is by a logical relation on the families of
    functionals indexed by a number [n] ([pgrowth]): at [N], the families
    bounded by a polynomial in [n]; at [σ ⇒ τ], the families that map those
    of [σ] to those of [τ]. *)
Fixpoint pgrowth (σ : ty) : (nat -> M σ) -> Prop :=
  match σ return (nat -> M σ) -> Prop with
  | tN => fun G => exists c d, forall n, G n <= c * (n + 1) ^ d
  | σ ⇒ τ => fun G => forall H, pgrowth σ H -> pgrowth τ (fun n => G n (H n))
  end.

Lemma pgrowth_hpoly σ m : is_hpoly σ m -> pgrowth σ (fun _ => m).
Proof.
  induction 1 as [k| | |σ τ|σ τ ρ|σ τ f x _ IHf _ IHx].
  - exists k, 0. intro n. cbn. lia.
  - intros G1 (c1 & d1 & H1) G2 (c2 & d2 & H2). exists (c1 + c2), (d1 + d2). intro n.
    specialize (H1 n). specialize (H2 n).
    assert ((n + 1) ^ d1 <= (n + 1) ^ (d1 + d2)) by (apply Nat.pow_le_mono_r; lia).
    assert ((n + 1) ^ d2 <= (n + 1) ^ (d1 + d2)) by (apply Nat.pow_le_mono_r; lia).
    nia.
  - intros G1 (c1 & d1 & H1) G2 (c2 & d2 & H2). exists (c1 * c2), (d1 + d2). intro n.
    specialize (H1 n). specialize (H2 n). rewrite Nat.pow_add_r. nia.
  - intros G1 H1 G2 _. exact H1.
  - intros F HF G HG X HX. exact (HF X HX (fun n => G n (X n)) (HG X HX)).
  - exact (IHf (fun _ => x) IHx).
Qed.

Theorem hpoly_growth (p : M (tN ⇒ tN)) :
  is_hpoly (tN ⇒ tN) p -> exists c d, forall n, p n <= c * (n + 1) ^ d.
Proof.
  intro H. apply (pgrowth_hpoly _ _ H (fun n => n)). exists 1, 1. intro n. rewrite Nat.pow_1_r. lia.
Qed.

(** [2 ^ n] is not bounded by a polynomial. *)
Lemma sq_le_pow2 k : 4 <= k -> k * k <= 2 ^ k.
Proof.
  induction k as [|k IH]; intro Hk; [lia|].
  destruct (Nat.eq_dec k 3) as [->|Hk3]; [cbn; lia|].
  specialize (IH ltac:(lia)). rewrite Nat.pow_succ_r'. nia.
Qed.

Lemma lin_lt_pow2 a b : exists k, a * k + b < 2 ^ k.
Proof.
  exists (2 * (a + b) + 4). pose proof (sq_le_pow2 (2 * (a + b) + 4) ltac:(lia)).
  set (k := 2 * (a + b) + 4) in *. set (P := 2 ^ k) in *. nia.
Qed.

Theorem pow2_not_poly c d : ~ (forall n, 2 ^ n <= c * (n + 1) ^ d).
Proof.
  intro H. destruct (lin_lt_pow2 d (c + 1)) as [j Hj].
  assert (Hj1 : 1 <= 2 ^ j) by (apply Nat.pow_le_mono_r with (a := 2) (b := 0); lia).
  specialize (H (2 ^ j - 1)). replace (2 ^ j - 1 + 1) with (2 ^ j) in H by lia.
  rewrite <- Nat.pow_mul_r in H.
  pose proof (Nat.pow_gt_lin_r 2 c ltac:(lia)).
  assert (2 ^ (2 ^ j - 1) <= 2 ^ (c + j * d)) by (rewrite Nat.pow_add_r; nia).
  apply Nat.pow_le_mono_r_iff in H1; lia.
Qed.
