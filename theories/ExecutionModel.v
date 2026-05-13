(* For archive. This file is not used anymore. *)
From Complexity Require Import SimpleTypes.
From Stdlib Require Import Classes.Morphisms Basics.

(* Now, assume that there is a computation model -- think of λ-calculus --
  that can realise elements of simple types,
  and that has a notion of cost that lifts to all simple types. *)

Module Type ExecutionModel.
  (* Abstraction A is the type of terms that realise elements of Rocq's type A. *)
  Parameter Abstraction : SimpleType -> Type.
  Notation "⟨ A ⟩" := (Abstraction A).

  (* An abstract term realises a Rocq term. *)
  Parameter realises: forall {A : SimpleType}, ⟨A⟩ -> Type_of_SimpleType A -> Prop.
  Infix "realises!" := realises (at level 40).

  (* Realisability is an extensional property *)
  Parameter realises_ext: forall {A},
    Proper ((eq) ==> ext_eq ==> (iff)) (@realises A).
  Global Existing Instance realises_ext.
End ExecutionModel.

(* Any execution model should at least include the application function *)

Module Type BasicExecutionModel.
  Include ExecutionModel.

  (* Evaluation is definable at all types. *)
  Parameter eval: forall {A B : SimpleType}, ⟨(A ⇝ B) ⇝ A ⇝ B⟩.

  Parameter eval_realises: forall A B,
    realises (@eval A B) (fun (f : A -> B) (x : A) => f x).
 (* TODO: what else should be there? *)
End BasicExecutionModel.