(** * Second-order polynomials

    Kapron and Cook's second-order polynomials, in a function variable [F]
    and a number variable [n]: constants, [n], sums, products and
    applications of [F]. They are higher-order polynomials ([HOPoly]) of
    type [(N ⇒ N) ⇒ N ⇒ N] ([sopoly_hpoly]). Conversely, every higher-order
    polynomial of this type is extensionally a second-order polynomial
    ([hpoly_sopoly]), by a definability logical relation on the families
    indexed by [F] and [n] ([sodef]). They bound the basic feasible
    functionals of type 2 ([BFF2_sopoly_bound] in [BFFFeasibility]).

    B. M. Kapron, S. A. Cook. A new characterization of type-2 feasibility.
    SIAM Journal on Computing 25(1):117-132, 1996. *)


(* For now, there is only one ground-type variable and one
 first-order variable. We can later generalise to arbitry arity using
 indexed families of argument, but this is enough for now. *)
From Complexity Require Export HOPoly.
From Stdlib Require Import Arith Lia List.
Import ListNotations.
Inductive sopoly : Type :=
| soconst (k : nat)
| sovar
| soadd (p q : sopoly)
| somul (p q : sopoly)
| soapp (p : sopoly).

Fixpoint soeval (p : sopoly) (F : nat -> nat) (n : nat) : nat :=
  match p with
  | soconst k => k
  | sovar => n
  | soadd p q => soeval p F n + soeval q F n
  | somul p q => soeval p F n * soeval q F n
  | soapp p => F (soeval p F n)
  end.

(** ** Second-order polynomials are higher-order polynomials

    The translation into a term, in the context of [F] and [n]. *)
Fixpoint sotrans (p : sopoly) : term hpc [tN; tN ⇒ tN] tN :=
  match p with
  | soconst k => tcst (hnum k)
  | sovar => tvar vz
  | soadd p q => tapp (tapp (tcst hadd) (sotrans p)) (sotrans q)
  | somul p q => tapp (tapp (tcst hmul) (sotrans p)) (sotrans q)
  | soapp p => tapp (tvar (vs vz)) (sotrans p)
  end.

Definition sohpoly (p : sopoly) : hpoly ((tN ⇒ tN) ⇒ tN ⇒ tN) := tlam (tlam (sotrans p)).

(** Every second-order polynomial is a higher-order polynomial. *)
Theorem sopoly_hpoly p F n : ⟦sohpoly p⟧ F n = soeval p F n.
Proof.
  change (interp (sotrans p) (ECons (ECons tt F) n) = soeval p F n).
  induction p; cbn; rewrite ?IHp, ?IHp1, ?IHp2; reflexivity.
Qed.

(** ** Higher-order polynomials with second-order type are second-order
  polynomials

    A logical relation on the families indexed by [F] and [n]: at [N], the
    family is the value of a second-order polynomial. *)

Fixpoint sodef (σ : ty) : ((nat -> nat) -> nat -> M σ) -> Prop :=
  match σ return ((nat -> nat) -> nat -> M σ) -> Prop with
  | tN => fun G => exists q, forall F n, G F n = soeval q F n
  | σ ⇒ τ => fun G => forall H, sodef σ H -> sodef τ (fun F n => G F n (H F n))
  end.

Fixpoint sodef_env (Γ : list ty) : ((nat -> nat) -> nat -> envT nat Γ) -> Prop :=
  match Γ with
  | [] => fun _ => True
  | σ :: Γ => fun E =>
      sodef_env Γ (fun F n => etl (E F n)) /\ sodef σ (fun F n => ehd (E F n))
  end.

Lemma sodef_cst σ (c : hpc σ) : sodef σ (fun _ _ => cinterp σ c).
Proof.
  destruct c as [k| |].
  - exists (soconst k). reflexivity.
  - intros G1 (q1 & H1) G2 (q2 & H2). exists (soadd q1 q2). intros F n. cbn. now rewrite H1, H2.
  - intros G1 (q1 & H1) G2 (q2 & H2). exists (somul q1 q2). intros F n. cbn. now rewrite H1, H2.
Qed.

Lemma sodef_interp Γ σ (p : term hpc Γ σ) E :
  sodef_env Γ E -> sodef σ (fun F n => interp p (E F n)).
Proof.
  revert E. induction p as [Γ σ x|Γ σ c|Γ σ τ p IH|Γ σ τ p IHp q IHq]; intros E HE.
  - induction x as [Γ σ|Γ σ τ x IHx]; [apply HE | exact (IHx _ (proj1 HE))].
  - apply sodef_cst.
  - intros H HH. exact (IH (fun F n => ECons (E F n) (H F n)) (conj HE HH)).
  - exact (IHp E HE _ (IHq E HE)).
Qed.

(** Every higher-order polynomial of type [(N ⇒ N) ⇒ N ⇒ N] is a
    second-order polynomial. *)
Theorem hpoly_sopoly (p : hpoly ((tN ⇒ tN) ⇒ tN ⇒ tN)) :
  exists q, forall F n, ⟦p⟧ F n = soeval q F n.
Proof.
  assert (HF : sodef (tN ⇒ tN) (fun F _ => F)).
  { intros G (q & Hq). exists (soapp q). intros F n. cbn. now rewrite Hq. }
  assert (Hn : sodef tN (fun _ n => n)) by now exists sovar.
  exact (sodef_interp [] _ p (fun _ _ => tt) I (fun F _ => F) HF (fun _ n => n) Hn).
Qed.
