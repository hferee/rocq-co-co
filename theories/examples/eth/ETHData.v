(** * The data types of the ETH algorithm in the cost model

    The algorithm ([ETHAlgorithm]) defines its own data types: the literals
    ([literal]), the parameters ([params]), the eigenvalues of the pairs of
    points ([pair_eig]) and the designs ([design]). As the data types of
    the standard library ([TimeDatatypes]), they come with their own
    axioms: their representations and sizes, the complexities of their
    constructors and of their case analyses. They are stated here, with
    the algorithm; [literal] has all of them, the other types their
    representations and sizes only.

    A match on a literal is compiled to its case combinator
    [literal_case], which the compiler finds by its name ([Combinators]),
    as a match on a pair ([prod_case]); the projections [lvar] and [lpos]
    are such matches. As for the data types of the standard library, the
    costs of the constructor and of the case analysis are parameters
    ([ParamETHData]), [1] in the time cost model ([ETHData], as
    [TimeCostModel]). *)

From Complexity Require Export TimeStdlib ETHAlgorithm.

(** ** The case combinator of [literal] *)

Definition literal_case {E A : Type} (f : env (env E nat) bool -> A) (l : E -> literal) (e : E) : A :=
  match l e with mkLit v p => f (ECons (ECons e v) p) end.

#[global] Typeclasses Opaque literal_case.
#[global] Hint Unfold literal_case : comb.

Module Type ParamETHData (Import Time : TimeStdlib).

  (** ** Literals: a variable and a sign *)

  #[global] Declare Instance Repr_literal : Ground literal.
  #[global] Declare Instance Size_literal : Size literal.
  Parameter size_mkLit : forall (v : nat) (p : bool), size (mkLit v p) = 1 + size v + size p.

  Parameter c_mkLit : nat.
  Parameter c_case_literal : nat.
  #[global] Hint Unfold c_mkLit c_case_literal : costs.

  #[global] Declare Instance mkLit_complexity :
    ComplexityBound mkLit (fun _ => c_clo +> fun _ => c_mkLit >|).

  (** The branch runs in the environment extended with the variable, then
      the sign. *)
  #[global] Declare Instance literal_case_complexity :
    forall {E CE A CA} `{Repr E CE} `{Repr A CA},
    ComplexityBound (@literal_case E A)
      (fun cf : ℂI (env (env E nat) bool -> A) (ℂI (env (env E nat) bool) ((CE * unit) * unit) -> ℂO CA) =>
         c_clo +>
       fun cl : ℂI (E -> literal) (ℂI E CE -> ℂO unit) => c_clo +>
       fun ce : ℂI E CE => c_case_literal ⊕ c_frame ⊕ cost (pot cl ce) ⊕
         match val cl (val ce) with
         | mkLit v p => pot cf (ECons (ECons (val ce) v) p ⋊ ((pot ce, tt), tt))
         end).

  (** ** The other types: representations and sizes *)

  #[global] Declare Instance Repr_params : Ground params.
  #[global] Declare Instance Size_params : Size params.
  #[global] Declare Instance Repr_pair_eig : Ground pair_eig.
  #[global] Declare Instance Size_pair_eig : Size pair_eig.
  #[global] Declare Instance Repr_design : Ground design.
  #[global] Declare Instance Size_design : Size design.
End ParamETHData.

(** With the constants of the time cost model. *)
Module Type ETHData (Time : TimeStdlib) :=
  ParamETHData Time with Definition c_mkLit := 1 with Definition c_case_literal := 1.
