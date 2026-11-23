(** * Functions on options of any data

    As for lists ([HOListComplexity]): the bounds are in the complexities
    of the element ([czip_option]) and of the function. *)

From Complexity Require Export TimeCostModel.

(** No timeout in the library ([ctimeout]). *)
#[local] Ltac2 Set ctimeout := 0.

(** The element of an option, with its complexity, or [d] when it is
    missing. *)
Definition czip_option {A CA} (d : CA) (co : ℂI (option A) (option CA)) : option (ℂI A CA) :=
  match val co with Some x => Some (x ⋊ option_dflt d (pot co)) | None => None end.

#[global] Hint Unfold czip_option : costs.

Module HOOptionComplexity (Import Time : TimeCostModel.TimeCostModel).

  Global Instance option_map_complexity {A CA B CB} `{Repr A CA} `{Repr B CB} :
    Time.ComplexityBound (@option_map A B)
      (fun cf : ℂI (A -> B) (ℂI A CA -> ℂO CB) => 1 +> fun co : ℂI (option A) (option CA) =>
         (match czip_option cdefault co with Some x => cost (pot cf x) | None => 0 end + 10)
         +> option_map (fun x => res (pot cf x)) (czip_option cdefault co)).
  Proof. cbound. Qed.
End HOOptionComplexity.
