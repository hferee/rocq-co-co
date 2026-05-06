From Complexity Require Import CostModel.
From Stdlib Require Import Program.Basics Lia List.

Module Type ListTimeCostModel
  (Import CM : CostModel) (Import BT : BasicTimeCostModel CM).

  (* Weird? set Type as a ground Type to allow polymorphic functions? *)
  Parameter TypeGround : GroundType Type.
  Existing Instance TypeGround.


  (* Scott encoding for lists. Useful? *)
  Fixpoint enc {A : Type} (l : list A) 
  : forall {C}, C -> (A -> C -> C) -> C
  := fun {C} n c =>
  match l with
  | nil => n
  | h :: t => c h (enc t n c)
  end.

  (* Contrary to coq-library-complexity, we can't
  register arbitrary inductive types here.
  Either hard-code them into SimpleTypes, or
  try something similar (see Encodings branch) *)
  (* List constructor *)
(*   Parameter cons_complexity :
    ComplexityBound _ cons (fun ca => (1, fun cl => 1
  Existing Instance cons_complexity. *)

End ListTimeCostModel.