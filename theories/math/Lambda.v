(** * Simply typed λ-calculus over a signature

    The terms of the simply typed λ-calculus over one base type and a
    signature `C` of typed constants, with de Bruijn variables
    (`term C Γ σ`, in the context [Γ]), and their denotations in the
    functionals over a type `B` (`sem B σ`), for an interpretation of the
    constants (`Interp C B`).

    The denotation of a term in the context [Γ] is a function of the
    environment (`envT B Γ`, the values of the variables), built from the
    closure combinators of the categorical abstract machine
    ([Combinators]): it is the closure conversion of the term, so that the
    cost model gives its complexity ([BFFFeasibility]). On a closed term,
    it computes to the expected functional ([⟦ t ⟧]).

    Closed terms are written with binders, in parametric higher-order
    abstract syntax ([pterm], with the notation [<{ .. }>]), and converted
    to de Bruijn terms by computation ([of_pterm], [db]).

    Reference:
    A. Chlipala. Parametric higher-order abstract syntax for mechanized
    semantics. ICFP 2008. *)

From Complexity Require Export Combinators.
From Stdlib Require Import List Program.Basics.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** ** Types and functionals *)

(** Simple types over a base type. *)
Inductive ty : Type := tN | tArr (σ τ : ty).
Infix "⇒" := tArr (at level 60, right associativity).

Definition ty_eq_dec (σ τ : ty) : {σ = τ} + {σ <> τ}.
Proof. decide equality. Defined.

(** The functionals of type [σ] over base type `B`. *)
Fixpoint sem (B : Type) (σ : ty) : Type :=
  match σ with tN => B | σ ⇒ τ => sem B σ -> sem B τ end.

(** [ext_eq σ f g]: [f] and [g] are equal on equal arguments,
    hereditarily. It is the equality of functionals, without functional
    extensionality. *)
Fixpoint ext_eq {B} (σ : ty) : sem B σ -> sem B σ -> Prop :=
  match σ return sem B σ -> sem B σ -> Prop with
  | tN => eq
  | σ ⇒ τ => fun f g => forall x y, ext_eq σ x y -> ext_eq τ (f x) (g y)
  end.

(** ** Terms *)

(** The variables of type [σ] in the context [Γ], the last one first. *)
Inductive var : list ty -> ty -> Type :=
| vz {Γ σ} : var (σ :: Γ) σ
| vs {Γ σ τ} : var Γ σ -> var (τ :: Γ) σ.

Section Terms.
  Variable C : ty -> Type.

  Inductive term : list ty -> ty -> Type :=
  | tvar {Γ σ} : var Γ σ -> term Γ σ
  | tcst {Γ σ} : C σ -> term Γ σ
  | tlam {Γ σ τ} : term (σ :: Γ) τ -> term Γ (σ ⇒ τ)
  | tapp {Γ σ τ} : term Γ (σ ⇒ τ) -> term Γ σ -> term Γ τ.
End Terms.

Arguments tvar {C Γ σ}.
Arguments tcst {C Γ σ}.
Arguments tlam {C Γ σ τ}.
Arguments tapp {C Γ σ τ}.

(** ** Denotation *)

(** The interpretation of the constants of `C` as functionals over `B`. *)
Class Interp (C : ty -> Type) (B : Type) := cinterp : forall σ, C σ -> sem B σ.
#[global] Hint Mode Interp + - : typeclass_instances.

(** Environments: the values of the variables, the last one first. *)
Fixpoint envT (B : Type) (Γ : list ty) : Type :=
  match Γ with [] => unit | σ :: Γ => env (envT B Γ) (sem B σ) end.

Fixpoint lookup {B Γ σ} (x : var Γ σ) : envT B Γ -> sem B σ :=
  match x in var Γ σ return envT B Γ -> sem B σ with
  | vz => ehd
  | vs x => compose (lookup x) etl
  end.

Fixpoint interp {C B} `{Interp C B} {Γ σ} (t : term C Γ σ) : envT B Γ -> sem B σ :=
  match t in term _ Γ σ return envT B Γ -> sem B σ with
  | tvar x => lookup x
  | tcst c => Kc (cinterp _ c)
  | tlam t => Lam (interp t)
  | tapp t u => Sc (interp t) (interp u)
  end.

(** The denotation of a closed term. *)
Definition eval {C B} `{Interp C B} {σ} (t : term C [] σ) : sem B σ := interp t tt.
Notation "⟦ t ⟧" := (eval t) (format "⟦ t ⟧").

(** Unfolds the denotations of terms, given the interpretations [I] of the
    constants. *)
Ltac simpl_interp I :=
  cbv beta iota delta [eval interp lookup cinterp I Lam Sc Kc compose] in *;
  cbn [ehd etl] in *.

(** ** Weakening *)

(** [wkn Γ t]: the term [t] of context [Δ] in the context [Δ ++ Γ]. *)
Fixpoint wvar {Δ τ} (Γ : list ty) (x : var Δ τ) : var (Δ ++ Γ) τ :=
  match x in var Δ τ return var (Δ ++ Γ) τ with
  | vz => vz
  | vs x => vs (wvar Γ x)
  end.

Fixpoint wkn {C Δ σ} (Γ : list ty) (t : term C Δ σ) : term C (Δ ++ Γ) σ :=
  match t in term _ Δ σ return term C (Δ ++ Γ) σ with
  | tvar x => tvar (wvar Γ x)
  | tcst c => tcst c
  | tlam t => tlam (wkn Γ t)
  | tapp t u => tapp (wkn Γ t) (wkn Γ u)
  end.

(** A closed term in any context. *)
Definition wk {C Γ σ} (t : term C [] σ) : term C Γ σ := wkn Γ t.

(** [csubst s t]: [t] with every constant [c] replaced by the closed
    term [s c]. *)
Fixpoint csubst {C D} (s : forall σ, C σ -> term D [] σ) {Γ σ} (t : term C Γ σ) : term D Γ σ :=
  match t with
  | tvar x => tvar x
  | tcst c => wk (s _ c)
  | tlam t => tlam (csubst s t)
  | tapp t u => tapp (csubst s t) (csubst s u)
  end.

(** ** Logical relations

    A relation `R` between functionals, defined at arrow types from its
    values at the argument and result types, relates the denotations of a
    term in related environments, when it relates the constants to
    themselves ([rel_interp]), and the denotation of a closed term to its
    weakenings ([rel_wk]). *)
Section Logical.
  Context {C B} `{Interp C B} (R : forall σ, sem B σ -> sem B σ -> Prop).
  Hypothesis Rlam : forall σ τ f g, (forall x y, R σ x y -> R τ (f x) (g y)) -> R (σ ⇒ τ) f g.
  Hypothesis Rapp : forall σ τ f g x y, R (σ ⇒ τ) f g -> R σ x y -> R τ (f x) (g y).
  Hypothesis Rcst : forall σ (c : C σ), R σ (cinterp σ c) (cinterp σ c).

  Fixpoint rel_env (Γ : list ty) : envT B Γ -> envT B Γ -> Prop :=
    match Γ with
    | [] => fun _ _ => True
    | σ :: Γ => fun e e' => rel_env Γ (etl e) (etl e') /\ R σ (ehd e) (ehd e')
    end.

  Lemma rel_interp Γ σ (t : term C Γ σ) e e' : rel_env Γ e e' -> R σ (interp t e) (interp t e').
  Proof.
    revert e e'. induction t as [Γ σ x|Γ σ c|Γ σ τ t IH|Γ σ τ t IHt u IHu]; intros e e' He.
    - induction x as [Γ σ|Γ σ τ x IHx]; [apply He | apply IHx, He].
    - apply Rcst.
    - apply Rlam. intros a a' Ha. apply IH. split; assumption.
    - apply (Rapp _ _ _ _ _ _ (IHt e e' He) (IHu e e' He)).
  Qed.

  Fixpoint rel_wenv (Γ Δ : list ty) : envT B Δ -> envT B (Δ ++ Γ) -> Prop :=
    match Δ with
    | [] => fun _ _ => True
    | σ :: Δ => fun e e' => rel_wenv Γ Δ (etl e) (etl e') /\ R σ (ehd e) (ehd e')
    end.

  Lemma rel_wkn Γ Δ σ (t : term C Δ σ) e e' :
    rel_wenv Γ Δ e e' -> R σ (interp t e) (interp (wkn Γ t) e').
  Proof.
    revert e e'. induction t as [Δ σ x|Δ σ c|Δ σ τ t IH|Δ σ τ t IHt u IHu]; intros e e' He.
    - induction x as [Δ σ|Δ σ τ x IHx]; [apply He | apply IHx, He].
    - apply Rcst.
    - apply Rlam. intros a a' Ha. apply IH. split; assumption.
    - apply (Rapp _ _ _ _ _ _ (IHt e e' He) (IHu e e' He)).
  Qed.

  Corollary rel_wk Γ σ (t : term C [] σ) e : R σ ⟦t⟧ (interp (@wk _ Γ _ t) e).
  Proof. exact (rel_wkn Γ [] σ t tt e I). Qed.

  Corollary rel_eval σ (t : term C [] σ) : R σ ⟦t⟧ ⟦t⟧.
  Proof. exact (rel_interp [] σ t tt tt I). Qed.
End Logical.

(** Every denotation is extensional, when the constants are. *)
(** [ext_eq] is a partial equivalence relation. *)
Lemma ext_eq_per {B} σ :
  (forall x y : sem B σ, ext_eq σ x y -> ext_eq σ y x) /\
  (forall x y z : sem B σ, ext_eq σ x y -> ext_eq σ y z -> ext_eq σ x z).
Proof.
  induction σ as [|σ [Sσ Tσ] τ [Sτ Tτ]]; [split; intros; congruence|]. split.
  - intros f g H a b Hab. apply Sτ, H, Sσ, Hab.
  - intros f g h H1 H2 a b Hab. apply (Tτ _ (g b)); [apply H1, Hab | apply H2, (Tσ _ a); [apply Sσ|]; exact Hab].
Qed.

Lemma ext_eq_sym {B} σ (x y : sem B σ) : ext_eq σ x y -> ext_eq σ y x.
Proof. apply ext_eq_per. Qed.

Lemma ext_eq_trans {B} σ (x y z : sem B σ) : ext_eq σ x y -> ext_eq σ y z -> ext_eq σ x z.
Proof. apply ext_eq_per. Qed.

Lemma ext_eq_eval {C B} `{Interp C B} :
  (forall σ (c : C σ), ext_eq σ (cinterp σ c) (cinterp σ c)) ->
  forall σ (t : term C [] σ), ext_eq σ ⟦t⟧ ⟦t⟧.
Proof.
  intros HC σ t. apply (rel_eval ext_eq); [intros ? ? ? ? Hf; exact Hf | intros ? ? ? ? ? ? Hf; apply Hf | exact HC].
Qed.

(** ** Terms with binders

    `pterm C V σ`: the terms whose variables are Rocq variables of types
    `V σ`. A closed term is a term for every `V` ([PTerm]). *)
Section PTerms.
  Variables (C : ty -> Type) (V : ty -> Type).

  Inductive pterm : ty -> Type :=
  | PVar {σ} : V σ -> pterm σ
  | PCst {σ} : C σ -> pterm σ
  | PAbs {σ τ} : (V σ -> pterm τ) -> pterm (σ ⇒ τ)
  | PApp {σ τ} : pterm (σ ⇒ τ) -> pterm σ -> pterm τ.
End PTerms.

Arguments PVar {C V σ}.
Arguments PCst {C V σ}.
Arguments PAbs {C V σ τ}.
Arguments PApp {C V σ τ}.

Definition PTerm (C : ty -> Type) (σ : ty) : Type := forall V, pterm C V σ.

(** The numerals of a signature, from literals of type [X]. *)
Class PNum (C : ty -> Type) (X : Type) := pnum : forall {V}, X -> pterm C V tN.

(** The atoms of terms: variables, numerals and closed terms. *)
Class PEmbed (C V : ty -> Type) (X : Type) (σ : ty) := pembed : X -> pterm C V σ.
#[global] Instance embed_var {C V σ} : PEmbed C V (V σ) σ := PVar.
#[global] Instance embed_num {C V X} `{PNum C X} : PEmbed C V X tN := pnum.
#[global] Instance embed_closed {C V σ} : PEmbed C V (PTerm C σ) σ := fun t => t V.

(** [<{ λ x y, f (g x) y }>]: a closed term. The constants of a signature
    are added to the entry [lam] by the files that define them. *)
Declare Custom Entry lam.
Notation "<{ e }>" := (fun V : ty -> Type => (e : pterm _ V _)) (e custom lam at level 200).
Notation "( e )" := e (in custom lam at level 0, e custom lam at level 200).
Notation "x" := (pembed x) (in custom lam at level 0, x constr at level 0).
Notation "f x" := (PApp f x) (in custom lam at level 10, left associativity).
Notation "'λ' x .. y , t" := (PAbs (fun x => .. (PAbs (fun y => t)) ..))
  (in custom lam at level 200, x binder, y binder, t custom lam at level 200).

(** The denotation of a closed term, directly. *)
Fixpoint pdenote {C B} `{Interp C B} {σ} (t : pterm C (sem B) σ) : sem B σ :=
  match t with
  | PVar x => x
  | PCst c => cinterp _ c
  | PAbs f => fun x => pdenote (f x)
  | PApp t u => pdenote t (pdenote u)
  end.

Definition pden {C B} `{Interp C B} {σ} (t : PTerm C σ) : sem B σ := pdenote (t (sem B)).

(** Conversion to de Bruijn terms: the variables are numbered from the
    outermost binder (levels), and their types are checked. *)
Fixpoint var_at (Γ : list ty) (i : nat) (σ : ty) : option (var Γ σ) :=
  match Γ return option (var Γ σ) with
  | [] => None
  | τ :: Γ =>
      match i with
      | 0 => match ty_eq_dec τ σ with
             | left e => Some (eq_rect τ (fun s => var (τ :: Γ) s) vz σ e)
             | right _ => None
             end
      | S i => option_map vs (var_at Γ i σ)
      end
  end.

Fixpoint to_term {C} (Γ : list ty) {σ} (t : pterm C (fun _ => nat) σ) : option (term C Γ σ) :=
  match t in pterm _ _ σ return option (term C Γ σ) with
  | PVar n => option_map tvar (var_at Γ (length Γ - S n) _)
  | PCst c => Some (tcst c)
  | PAbs f => option_map tlam (to_term (_ :: Γ) (f (length Γ)))
  | PApp t u =>
      match to_term Γ t, to_term Γ u with
      | Some a, Some b => Some (tapp a b)
      | _, _ => None
      end
  end.

Definition of_pterm {C σ} (t : PTerm C σ) : option (term C [] σ) := to_term [] (t _).

(** [db t]: the de Bruijn term of the closed term [t], elaborated with
    the expected type (which gives the signature and the types of the
    unused variables). *)
Ltac2 db_of (t : preterm) :=
  let g := Std.eval_hnf (Control.goal ()) in
  lazy_match! g with
  | term ?c ?g ?s =>
      Std.unify g constr:(@nil ty);
      let t := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags
                 (Constr.Pretype.expected_oftype constr:(PTerm $c $s)) t in
      let u := Std.eval_vm None constr:(of_pterm $t) in
      lazy_match! u with
      | Some ?v => exact $v
      | None => Control.throw (Tactic_failure (Some (Message.of_string "db: ill-formed term")))
      end
  end.

Abbreviation db t := (ltac2:(db_of t)) (only parsing).
