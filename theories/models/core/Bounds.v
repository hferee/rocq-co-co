(** * Bounds in the sizes of the inputs

    [ComplexityBound f c] bounds the costs of [f] by a function [c] of its
    inputs; the usual classes of complexity bound them by a function of the
    sizes of the inputs only. The tactics are in [BoundsTactics]. *)

From Complexity Require Import CostModelCore Poly.
From Stdlib Require Import List.
Import ListNotations.

(** ** Sizes

    The size of a value: the length of its binary encoding. *)
Class Size (A : Type) := size : A -> nat.
Notation "#| x |" := (size x) (at level 0, x at level 99, format "#| x |").

#[global] Instance Size_unit : Size unit := fun _ => 1.
Lemma size_tt : size tt = 1.
Proof. reflexivity. Qed.

(** ** Measures of costs

    [cnat c]: the measure of a cost, which the bounds compare to functions
    of the sizes. Fixed by the model. Time: the cost itself; peak space:
    the peak ([SpaceCostModel]). The tactics unfold it ([measures]). *)
Create HintDb measures.
Module Type CostSizes (Import CM : CostModelAxioms).
  Parameter cnat : Cost -> nat.
  #[global] Hint Unfold cnat : measures.
End CostSizes.

Module Bounds (Import CM : CostModelCore) (Import CS : CostSizes CM).
  (** ** First-order functions

      [FirstOrder A CA]: [A] is a type of first-order functions, whose
      arguments and result have a representation and a size, and [CA] the
      type of their complexities; [fo_repr] is their representation. The
      size of the result excludes the functions, which have none. *)
  Inductive FirstOrder : Type -> Type -> Type :=
  | fo_res {B CB} (RB : Repr B CB) : Size B -> FirstOrder B CB
  | fo_arg {A CA B CB} (RA : Repr A CA) : Size A -> FirstOrder B CB ->
      FirstOrder (A -> B) (ℂI A CA -> ℂO CB).
  Existing Class FirstOrder.
  Global Existing Instances fo_res fo_arg.

  Fixpoint fo_repr {A CA} (fo : FirstOrder A CA) : Repr A CA :=
    match fo in FirstOrder A CA return Repr A CA with
    | fo_res RB _ => RB
    | fo_arg RA _ fo => Repr_arr RA (fo_repr fo)
    end.

  (** [size_costs fo g ss c]: each application costs at most [g] of the
      sizes of the arguments so far ([ss], then the new one). The
      complexities of the results are not constrained. *)
  Fixpoint size_costs {A CA} (fo : FirstOrder A CA) (g : list nat -> nat) (ss : list nat) : CA -> Prop :=
    match fo in FirstOrder A CA return CA -> Prop with
    | fo_res _ _ => fun _ => True
    | fo_arg _ SA fo => fun c => forall ca,
        cnat (cost (c ca)) <= g (ss ++ [size (Size := SA) (val ca)]) /\
        size_costs fo g (ss ++ [size (Size := SA) (val ca)]) (res (c ca))
    end.

  (** ** Bounds

      [FirstOrderBound f g]: [f] has a complexity whose costs are at most
      [g] of the sizes. [g] is a polynomial ([Poly]) for [PolynomialBound],
      of degree at most [1] for [LinearBound], and [0] for [ConstantBound]. *)
  Definition FirstOrderBound {A CA} `{fo : FirstOrder A CA} (f : A) (g : list nat -> nat) : Prop :=
    exists c, @ComplexityBound A (repr_ctype (R := fo_repr fo)) f c /\ size_costs fo g [] c.

  Class PolynomialBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    polynomial_bound : exists p, FirstOrderBound f (peval p).

  Class LinearBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    linear_bound : exists p, pdeg p <= 1 /\ FirstOrderBound f (peval p).

  Class ConstantBound {A CA} `{FirstOrder A CA} (f : A) : Prop :=
    constant_bound : exists p, pdeg p = 0 /\ FirstOrderBound f (peval p).

  (** The bounds are closed upwards in [g]. *)
  Lemma size_costs_mono {A CA} (fo : FirstOrder A CA) (g g' : list nat -> nat) ss c :
    (forall ss, g ss <= g' ss) -> size_costs fo g ss c -> size_costs fo g' ss c.
  Proof.
    intro Hg. revert ss c. induction fo as [B CB RB SB | A CA B CB RA SA fo IH]; intros ss c; cbn; [auto|].
    intros H ca. destruct (H ca) as [H1 H2]. split; [specialize (Hg (ss ++ [size (val ca)])); lia | exact (IH _ _ H2)].
  Qed.

  Lemma FirstOrderBound_mono {A CA} `{FirstOrder A CA} (f : A) (g g' : list nat -> nat) :
    (forall ss, g ss <= g' ss) -> FirstOrderBound f g -> FirstOrderBound f g'.
  Proof. intros Hg (c & Hc & Hs). exists c. split; [exact Hc | exact (size_costs_mono _ _ _ _ _ Hg Hs)]. Qed.

  (** A constant bound is linear, a linear bound is polynomial. *)
  Global Instance LinearBound_PolynomialBound {A CA} `{FirstOrder A CA} (f : A)
    {Hf : LinearBound f} : PolynomialBound f.
  Proof. destruct Hf as (p & _ & Hf). exists p. exact Hf. Qed.

  Global Instance ConstantBound_LinearBound {A CA} `{FirstOrder A CA} (f : A)
    {Hf : ConstantBound f} : LinearBound f.
  Proof. destruct Hf as (p & Hp & Hf). exists p. split; [lia | exact Hf]. Qed.
End Bounds.

(** The cost model with the bounds in the sizes. *)
Module Type BoundsCore := CostModelCore.CostModelCore <+ CostSizes <+ Bounds.
