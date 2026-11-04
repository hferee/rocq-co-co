(** * Basic feasible functionals

    The basic feasible functionals (BFF) are the functionals of finite type
    over the natural numbers that are computable in polynomial time. They are
    the functionals defined by the closed terms of the simply typed
    λ-calculus over constants for polynomial-time functions and a recursor
    [R], bounded recursion on notation: Cook & Urquhart's system PV^ω
    ([pv], [is_BFF]). At type 2, they are the functionals computed by oracle
    Turing machines in time bounded by a second-order polynomial in the
    lengths of their inputs (Kapron & Cook).

    Numbers are binary ([N]); the length [|x|] of [x] is its number of bits
    ([N.size_nat], [0] for [0]). The constants of PV^ω are defined below by
    recursion on notation, that is on the bits of their arguments (through
    [positive]), as programs whose costs [BFFComplexity] analyses; each one
    is shown equal to its arithmetic definition. The terms are those of
    [Lambda], written with binders ([<{ λ x, .. }>]); derived functions are
    defined as terms, and every term has a higher-order polynomial
    majorant ([BFF_majorant]).

    S. A. Cook, A. Urquhart. Functional interpretations of feasibly
    constructive arithmetic. Annals of Pure and Applied Logic 63(2):103-200,
    1993.

    B. M. Kapron, S. A. Cook. A new characterization of type-2 feasibility.
    SIAM Journal on Computing 25(1):117-132, 1996. *)

From Complexity Require Import Combinators Lambda HOPoly.
From Stdlib Require Import Arith PArith NArith Lia NArithRing List.
Import ListNotations.
Local Open Scope N_scope.

(** ** Successors and truncation *)

(** [s0 x = 2 x] and [s1 x = 2 x + 1]: a bit appended to [x]. *)
Definition s0 (x : N) : N := match x with N0 => N0 | Npos p => Npos (xO p) end.
Definition s1 (x : N) : N := match x with N0 => Npos xH | Npos p => Npos (xI p) end.

(** [tr x = ⌊x / 2⌋]: the last bit removed. *)
Definition tr (x : N) : N :=
  match x with
  | N0 => N0
  | Npos p => match p with xH => N0 | xO q | xI q => Npos q end
  end.

Lemma s0_spec x : s0 x = 2 * x.
Proof. destruct x; reflexivity. Qed.

Lemma s1_spec x : s1 x = 2 * x + 1.
Proof. destruct x; reflexivity. Qed.

Lemma tr_spec x : tr x = x / 2.
Proof. rewrite <- N.div2_div. destruct x as [|[p|p|]]; reflexivity. Qed.

(** ** Padding, chopping and smash *)

(** [pad x y = x 2^|y|]: [|y|] zeros appended to [x]. *)
Fixpoint pad_pos (x : N) (q : positive) : N :=
  match q with xH => s0 x | xO q | xI q => s0 (pad_pos x q) end.
Definition pad (x y : N) : N := match y with N0 => x | Npos q => pad_pos x q end.

(** [chop x y = ⌊x / 2^|y|⌋]: the last [|y|] bits of [x] removed. *)
Fixpoint chop_pos (x : N) (q : positive) : N :=
  match q with xH => tr x | xO q | xI q => tr (chop_pos x q) end.
Definition chop (x y : N) : N := match y with N0 => x | Npos q => chop_pos x q end.

(** [smash x y = 2^(|x| |y|)]: [|x|] zeros appended [|y|] times to [1]. *)
Fixpoint smash_pos (x : N) (q : positive) : N :=
  match q with xH => pad 1 x | xO q | xI q => pad (smash_pos x q) x end.
Definition smash (x y : N) : N := match y with N0 => 1 | Npos q => smash_pos x q end.

Lemma pos_succ p : N.pos (Pos.succ p) = N.succ (N.pos p).
Proof. reflexivity. Qed.

Lemma pad_pos_spec x q : pad_pos x q = x * 2 ^ N.pos (Pos.size q).
Proof.
  induction q as [q IH|q IH|]; cbn [pad_pos Pos.size]; rewrite s0_spec; [| |rewrite N.pow_1_r; ring];
    rewrite IH, (pos_succ (Pos.size q)), N.pow_succ_r'; ring.
Qed.

Lemma pad_spec x y : pad x y = x * 2 ^ N.size y.
Proof. destruct y as [|q]; cbn; [ring | apply pad_pos_spec]. Qed.

Lemma chop_pos_spec x q : chop_pos x q = x / 2 ^ N.pos (Pos.size q).
Proof.
  induction q as [q IH|q IH|]; cbn [chop_pos Pos.size]; rewrite tr_spec; [| |reflexivity];
    rewrite IH, (pos_succ (Pos.size q)), N.pow_succ_r', N.Div0.div_div, N.mul_comm;
    try reflexivity; try discriminate; apply N.pow_nonzero; discriminate.
Qed.

Lemma chop_spec x y : chop x y = x / 2 ^ N.size y.
Proof. destruct y as [|q]; cbn; [now rewrite N.div_1_r | apply chop_pos_spec]. Qed.

Lemma smash_pos_spec x q : smash_pos x q = 2 ^ (N.size x * N.pos (Pos.size q)).
Proof.
  induction q as [q IH|q IH|]; cbn [smash_pos Pos.size]; rewrite pad_spec; [| |cbn [N.size]; rewrite N.mul_1_r; ring];
    rewrite IH, (pos_succ (Pos.size q)), N.mul_succ_r, N.pow_add_r; ring.
Qed.

Lemma smash_spec x y : smash x y = 2 ^ (N.size x * N.size y).
Proof. destruct y as [|q]; cbn; [now rewrite N.mul_0_r | apply smash_pos_spec]. Qed.

(** ** Conditional and parity *)

Definition cond (x y z : N) : N := match x with N0 => y | Npos _ => z end.

(** [par x = x mod 2]: the last bit of [x]. The basis of PV^ω is a
    collection of polynomial-time functions (all of them, in Cook and
    Kapron's version), which must contain such a test: the other functions
    do not depend on the values of the bits of their arguments, except for
    [cond] which tests [0], and neither does the recursor [R] (whose step
    function receives the whole argument), so that they do not define the
    parity. *)
Definition par (x : N) : N :=
  match x with N0 => 0 | Npos p => match p with xO _ => 0 | _ => 1 end end.

Lemma par_spec x : par x = x mod 2.
Proof. destruct x as [|[p|p|]]; try reflexivity; cbn [par].
  - apply (N.mod_unique _ _ (Npos p) 1); [lia|]. change (Npos p~1) with (2 * Npos p + 1). ring.
  - apply (N.mod_unique _ _ (Npos p) 0); [lia|]. change (Npos p~0) with (2 * Npos p). ring.
Qed.

(** ** Bounded recursion on notation *)

(** [len_le t u]: [|t| <= |u|], in time [min |t| |u|]. *)
Fixpoint pos_len_le (p q : positive) : bool :=
  match p with
  | xH => true
  | xO p | xI p => match q with xH => false | xO q | xI q => pos_len_le p q end
  end.
Definition len_le (t u : N) : bool :=
  match t with
  | N0 => true
  | Npos p => match u with N0 => false | Npos q => pos_len_le p q end
  end.

Lemma len_le_spec t u : len_le t u = (N.size_nat t <=? N.size_nat u)%nat.
Proof.
  destruct t as [|p]; [reflexivity|]. destruct u as [|q]; cbn; [destruct p; reflexivity|].
  revert q. induction p as [p IH|p IH|]; intros [q|q|]; cbn; try apply IH; try reflexivity;
    match goal with p : positive |- _ => destruct p; reflexivity end.
Qed.

(** [R a F h w]: the recursion on notation of step [F] from [a], each value
    being bounded by the length of [h]:
    - [R a F h 0 = a];
    - [R a F h w = t] if [|t| <= |h w|], and [h w] otherwise, where
      [t = F w (R a F h ⌊w / 2⌋)] ([bnd t (h w)]).

    It is Cook and Urquhart's recursor, on numbers instead of strings (as
    restated by Kapron and Steinberg, with [w] the string [c i] of digit
    [i]): the step function receives the whole argument [w], unlike the
    limited recursion on notation of Cobham and Mehlhorn, which has one
    step function for each bit.

    B. M. Kapron, F. Steinberg. Type-two polynomial-time and restricted
    lookahead. arXiv:1801.07485, 2018. *)
Definition bnd (t b : N) : N := if len_le t b then t else b.

Fixpoint rec_pos (a : N) (F : N -> N -> N) (h : N -> N) (q : positive) : N :=
  match q with
  | xH => bnd (F 1 a) (h 1)
  | xO q' => bnd (F (Npos (xO q')) (rec_pos a F h q')) (h (Npos (xO q')))
  | xI q' => bnd (F (Npos (xI q')) (rec_pos a F h q')) (h (Npos (xI q')))
  end.
Definition R (a : N) (F : N -> N -> N) (h : N -> N) (w : N) : N :=
  match w with N0 => a | Npos q => rec_pos a F h q end.

Lemma R_0 a F h : R a F h 0 = a.
Proof. reflexivity. Qed.

Lemma R_step a F h w : w <> 0 ->
  R a F h w =
    let t := F w (R a F h (w / 2)) in
    if (N.size_nat t <=? N.size_nat (h w))%nat then t else h w.
Proof.
  intro Hw. rewrite <- N.div2_div. destruct w as [|[q|q|]]; [easy| | |];
    cbn; unfold bnd; rewrite len_le_spec; reflexivity.
Qed.

(** The values of [R] are bounded by the length of [h]. *)
Lemma R_size a F h w : w <> 0 -> (N.size_nat (R a F h w) <= N.size_nat (h w))%nat.
Proof.
  intro Hw. rewrite R_step by exact Hw. cbn zeta.
  destruct (Nat.leb_spec (N.size_nat (F w (R a F h (w / 2)))) (N.size_nat (h w))); lia.
Qed.

(** ** Examples of basic feasible functionals *)

(** Application twice. *)
Definition twice (f : N -> N) (x : N) : N := f (f x).

(** ** Lengths of the values of the constants *)

Lemma size_s0 x : (N.size_nat (s0 x) <= S (N.size_nat x))%nat.
Proof. destruct x; cbn; lia. Qed.

Lemma size_s1 x : (N.size_nat (s1 x) <= S (N.size_nat x))%nat.
Proof. destruct x; cbn; lia. Qed.

Lemma size_tr x : (N.size_nat (tr x) <= N.size_nat x)%nat.
Proof. destruct x as [|[p|p|]]; cbn; lia. Qed.

Lemma size_par x : (N.size_nat (par x) <= 1)%nat.
Proof. destruct x as [|[p|p|]]; cbn; lia. Qed.

Lemma size_pad_pos x q : (N.size_nat (pad_pos x q) <= N.size_nat x + Pos.size_nat q)%nat.
Proof.
  induction q as [q IH|q IH|]; cbn [pad_pos Pos.size_nat];
    [pose proof (size_s0 (pad_pos x q)) | pose proof (size_s0 (pad_pos x q))
    | pose proof (size_s0 x)]; lia.
Qed.

Lemma size_pad x y : (N.size_nat (pad x y) <= N.size_nat x + N.size_nat y)%nat.
Proof. destruct y as [|q]; cbn; [lia | apply size_pad_pos]. Qed.

Lemma size_chop_pos x q : (N.size_nat (chop_pos x q) <= N.size_nat x)%nat.
Proof.
  induction q as [q IH|q IH|]; cbn [chop_pos];
    [pose proof (size_tr (chop_pos x q)) | pose proof (size_tr (chop_pos x q))
    | pose proof (size_tr x)]; lia.
Qed.

Lemma size_chop x y : (N.size_nat (chop x y) <= N.size_nat x)%nat.
Proof. destruct y as [|q]; cbn; [lia | apply size_chop_pos]. Qed.

Lemma size_smash_pos x q : (N.size_nat (smash_pos x q) <= Pos.size_nat q * N.size_nat x + 1)%nat.
Proof.
  induction q as [q IH|q IH|]; cbn [smash_pos Pos.size_nat];
    [pose proof (size_pad (smash_pos x q) x) | pose proof (size_pad (smash_pos x q) x)
    | pose proof (size_pad 1 x)]; cbn in *; nia.
Qed.

Lemma size_smash x y : (N.size_nat (smash x y) <= N.size_nat y * N.size_nat x + 1)%nat.
Proof. destruct y as [|q]; cbn; [lia | apply size_smash_pos]. Qed.

Lemma size_cond x y z : (N.size_nat (cond x y z) <= N.size_nat y + N.size_nat z)%nat.
Proof. destruct x; cbn; lia. Qed.

Lemma size_R a F h w : (N.size_nat (R a F h w) <= N.size_nat a + N.size_nat (h w))%nat.
Proof.
  destruct (N.eq_dec w 0) as [->|Hw]; [cbn; lia|].
  pose proof (R_size a F h w Hw). lia.
Qed.

(** ** PV^ω

    The terms of PV^ω are the simply typed λ-terms ([Lambda]) over the
    constants [pv], interpreted by the functions above. They are written
    with binders, as [<{ λ f x, f (f x) }>], where [s0], [s1], [tr], [pad],
    [chop], [smash], [cond], [par] and [R] are the constants, and the
    numerals are built from [0], [s0] and [s1]. A basic feasible functional
    is a functional equal to the denotation of a closed term of PV^ω
    ([is_BFF]), as a functional ([ext_eq]: equal on equal arguments). *)
Inductive pv : ty -> Type :=
| c0 : pv tN
| cs0 : pv (tN ⇒ tN)
| cs1 : pv (tN ⇒ tN)
| ctr : pv (tN ⇒ tN)
| cpad : pv (tN ⇒ tN ⇒ tN)
| cchop : pv (tN ⇒ tN ⇒ tN)
| csmash : pv (tN ⇒ tN ⇒ tN)
| ccond : pv (tN ⇒ tN ⇒ tN ⇒ tN)
| cpar : pv (tN ⇒ tN)
| cR : pv (tN ⇒ (tN ⇒ tN ⇒ tN) ⇒ (tN ⇒ tN) ⇒ tN ⇒ tN).

Abbreviation den := (sem N).

#[global] Instance pv_interp : Interp pv N :=
  fun σ c =>
    match c in pv σ return den σ with
    | c0 => 0 | cs0 => s0 | cs1 => s1 | ctr => tr | cpad => pad | cchop => chop
    | csmash => smash | ccond => cond | cpar => par | cR => R
    end.

Fixpoint pnum_pos {V} (p : positive) : pterm pv V tN :=
  match p with
  | xH => PApp (PCst cs1) (PCst c0)
  | xO p => PApp (PCst cs0) (pnum_pos p)
  | xI p => PApp (PCst cs1) (pnum_pos p)
  end.

#[global] Instance pv_num : PNum pv N :=
  fun V n => match n with N0 => PCst c0 | Npos p => pnum_pos p end.
#[global] Instance pv_num_nat : PNum pv nat := fun V n => pnum (N.of_nat n).
(** The numerals of higher-order polynomials, in [N_scope]. *)
#[global] Instance hp_num_N : PNum hpc N := fun V n => pnum (N.to_nat n).

Notation "'s0'" := (PCst cs0) (in custom lam at level 0).
Notation "'s1'" := (PCst cs1) (in custom lam at level 0).
Notation "'tr'" := (PCst ctr) (in custom lam at level 0).
Notation "'pad'" := (PCst cpad) (in custom lam at level 0).
Notation "'chop'" := (PCst cchop) (in custom lam at level 0).
Notation "'smash'" := (PCst csmash) (in custom lam at level 0).
Notation "'cond'" := (PCst ccond) (in custom lam at level 0).
Notation "'par'" := (PCst cpar) (in custom lam at level 0).
Notation "'R'" := (PCst cR) (in custom lam at level 0).

Definition is_BFF (σ : ty) (f : den σ) : Prop := exists t : term pv [] σ, ext_eq σ ⟦t⟧ f.

Ltac simpl_pv := simpl_interp pv_interp.

(** The constants are extensional, so that the denotations of terms are
    BFFs ([BFF_eval]). *)
Lemma R_ext a F F' h h' w :
  (forall x y, F x y = F' x y) -> (forall x, h x = h' x) -> R a F h w = R a F' h' w.
Proof.
  intros HF Hh. destruct w as [|q]; [reflexivity|]. cbn [R].
  induction q as [q IH|q IH|]; cbn [rec_pos]; rewrite ?IH, HF, Hh; reflexivity.
Qed.

Lemma ext_eq_pv σ (c : pv σ) : ext_eq σ (cinterp σ c) (cinterp σ c).
Proof.
  destruct c; cbn; intros; subst; try reflexivity.
  apply R_ext; intros; [apply H0 | apply H1]; reflexivity.
Qed.

Lemma BFF_eval σ (t : term pv [] σ) : is_BFF σ ⟦t⟧.
Proof. exists t. apply (ext_eq_eval ext_eq_pv). Qed.

Lemma bff_app σ τ f x : is_BFF (σ ⇒ τ) f -> is_BFF σ x -> is_BFF τ (f x).
Proof. intros [t Ht] [u Hu]. exists (tapp t u). exact (Ht _ _ Hu). Qed.

Lemma bff_ext σ f g : is_BFF σ f -> ext_eq σ f g -> is_BFF σ g.
Proof. intros [t Ht] H. exists t. exact (ext_eq_trans _ _ _ _ Ht H). Qed.

(** [twice] is the denotation of [λ f x, f (f x)]. *)
Example twice_BFF : is_BFF ((tN ⇒ tN) ⇒ tN ⇒ tN) twice :=
  BFF_eval ((tN ⇒ tN) ⇒ tN ⇒ tN) (db <{ λ f x, f (f x) }>).

(** ** Derived functions

    Polynomial-time functions defined in PV^ω, with their specifications.
    Each one is the denotation ([pden]) of a term [.._t] with binders,
    abstracted over the functions that it uses, and [.._pv] is its closed
    term of PV^ω. *)

(** [eqbit b c]: [1] if the bits [b] and [c] are equal, [0] otherwise. *)
Definition eqbit_t : PTerm pv (tN ⇒ tN ⇒ tN) := <{ λ b c, cond b (cond c 1 0) c }>.
Definition eqbit (b c : N) : N := Eval cbn in pden eqbit_t b c.
Definition eqbit_pv : term pv [] _ := db eqbit_t.

(** [inc z = z + 1], from the last bit: [inc (2 z) = 2 z + 1] and
    [inc (2 z + 1) = 2 inc z]. *)
Definition inc_t : PTerm pv (tN ⇒ tN) := <{ λ z, R 1 (λ w r, cond (par w) (s1 (tr w)) (s0 r)) s1 z }>.
Definition inc (z : N) : N := Eval cbn in pden inc_t z.
Definition inc_pv : term pv [] _ := db inc_t.

(** [len y]: the length [|y|] of [y], in binary. *)
Definition len_t : PTerm pv ((tN ⇒ tN) ⇒ tN ⇒ tN) := <{ λ inc y, R 0 (λ _ r, inc r) (λ w, w) y }>.
Definition len (y : N) : N := Eval cbn in pden len_t inc y.
Definition len_pv : term pv [] _ := tapp (db len_t) inc_pv.

(** [eqN x y]: [1] if [x = y], [0] otherwise. The bits of [x] and [y] are
    compared from the most significant one, up to the length of
    [pad (s1 x) y]: the recursion is on its prefixes [w], and the bit
    [|w| - 1] of [x] is the parity of [chop x (tr w)]. *)
Definition eqN_t : PTerm pv ((tN ⇒ tN ⇒ tN) ⇒ tN ⇒ tN ⇒ tN) :=
  <{ λ eqbit x y,
       R 1 (λ w r, cond r 0 (eqbit (par (chop x (tr w))) (par (chop y (tr w))))) (λ _, 1)
         (pad (s1 x) y) }>.
Definition eqN (x y : N) : N := Eval cbn in pden eqN_t eqbit x y.
Definition eqN_pv : term pv [] _ := tapp (db eqN_t) eqbit_pv.

(** [pw2 x y]: [1] if [y = 2^x], [0] otherwise: [y] is a power of [2] (it is
    [2^(|y| - 1)]) of length [x + 1]. *)
Definition pw2_t : PTerm pv ((tN ⇒ tN ⇒ tN) ⇒ (tN ⇒ tN) ⇒ (tN ⇒ tN) ⇒ tN ⇒ tN ⇒ tN) :=
  <{ λ eqN len inc x y, cond y 0 (cond (eqN y (pad 1 (tr y))) 0 (eqN (len y) (inc x))) }>.
Definition pw2 (x y : N) : N := Eval cbn in pden pw2_t eqN len inc x y.
Definition pw2_pv : term pv [] _ := tapp (tapp (tapp (db pw2_t) eqN_pv) len_pv) inc_pv.

Definition eqbit_BFF : is_BFF (tN ⇒ tN ⇒ tN) eqbit := BFF_eval _ eqbit_pv.
Definition inc_BFF : is_BFF (tN ⇒ tN) inc := BFF_eval _ inc_pv.
Definition len_BFF : is_BFF (tN ⇒ tN) len := BFF_eval _ len_pv.
Definition eqN_BFF : is_BFF (tN ⇒ tN ⇒ tN) eqN := BFF_eval _ eqN_pv.
Definition pw2_BFF : is_BFF (tN ⇒ tN ⇒ tN) pw2 := BFF_eval _ pw2_pv.


Lemma bnd_le t u : (N.size_nat t <= N.size_nat u)%nat -> bnd t u = t.
Proof. intro H. unfold bnd. rewrite len_le_spec. apply Nat.leb_le in H. rewrite H. reflexivity. Qed.

Lemma size_nat_succ_le p : (Pos.size_nat (Pos.succ p) <= S (Pos.size_nat p))%nat.
Proof. induction p; cbn; lia. Qed.

Lemma inc_spec z : inc z = N.succ z.
Proof.
  destruct z as [|p]; [reflexivity|]. unfold inc. cbn [R].
  induction p as [p IH|p IH|]; cbn [rec_pos]; cbn beta.
  - rewrite IH. cbn [par cond]. rewrite bnd_le; [reflexivity|].
    cbn. pose proof (size_nat_succ_le p). lia.
  - cbn [par cond tr s1]. rewrite bnd_le; [reflexivity | cbn; lia].
  - reflexivity.
Qed.

Lemma size_nat_size q : Pos.to_nat (Pos.size q) = Pos.size_nat q.
Proof. induction q; cbn [Pos.size Pos.size_nat]; rewrite ?Pos2Nat.inj_succ; lia. Qed.

Lemma size_nat_le_to_nat p : (Pos.size_nat p <= Pos.to_nat p)%nat.
Proof. induction p; cbn [Pos.size_nat]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO; lia. Qed.

Lemma len_spec y : len y = N.size y.
Proof.
  destruct y as [|p]; [reflexivity|]. unfold len. cbn [R].
  induction p as [p IH|p IH|]; cbn [rec_pos]; cbn beta.
  1, 2: rewrite IH, inc_spec; cbn [N.size N.succ]; rewrite bnd_le; [reflexivity|];
    cbn [N.size_nat Pos.size Pos.size_nat];
    pose proof (size_nat_le_to_nat (Pos.succ (Pos.size p)));
    rewrite Pos2Nat.inj_succ, size_nat_size in H; lia.
  - reflexivity.
Qed.

Lemma eqbit_spec b c : b < 2 -> c < 2 -> eqbit b c = if (b =? c) then 1 else 0.
Proof.
  intros Hb Hc. assert (b = 0 \/ b = 1) as [-> | ->] by lia;
    assert (c = 0 \/ c = 1) as [-> | ->] by lia; reflexivity.
Qed.

Lemma bit01 z : z mod 2 = 0 \/ z mod 2 = 1.
Proof. pose proof (N.mod_lt z 2 ltac:(discriminate)). set (b := z mod 2) in *. lia. Qed.

Lemma eqb_mod_succ x y e :
  (x mod 2 ^ N.succ e =? y mod 2 ^ N.succ e) =
  ((x mod 2 ^ e =? y mod 2 ^ e) && ((x / 2 ^ e) mod 2 =? (y / 2 ^ e) mod 2))%bool.
Proof.
  assert (He : 2 ^ e <> 0) by (apply N.pow_nonzero; lia).
  rewrite N.pow_succ_r', (N.mul_comm 2), !N.Div0.mod_mul_r by lia.
  pose proof (N.mod_lt x (2 ^ e) He). pose proof (N.mod_lt y (2 ^ e) He).
  destruct (bit01 (x / 2 ^ e)) as [Hx|Hx], (bit01 (y / 2 ^ e)) as [Hy|Hy]; rewrite Hx, Hy;
    set (P := 2 ^ e) in *; set (u := x mod P) in *; set (v := y mod P) in *;
    match goal with |- (?a =? ?b) = _ => destruct (N.eqb_spec a b) end;
    destruct (N.eqb_spec u v); cbn; try reflexivity; exfalso; nia.
Qed.

Lemma eqN_spec x y : eqN x y = if (x =? y) then 1 else 0.
Proof.
  set (G := fun w r => cond r 0 (eqbit (par (chop x (tr w))) (par (chop y (tr w))))).
  assert (L : forall p, rec_pos 1 G (fun _ => 1) p =
                if (x mod 2 ^ N.size (Npos p) =? y mod 2 ^ N.size (Npos p)) then 1 else 0).
  { induction p as [p IH|p IH|]; cbn [rec_pos].
    1, 2: rewrite IH; unfold G; cbn [tr N.size Pos.size];
      rewrite (pos_succ (Pos.size p)), eqb_mod_succ, !chop_spec, !par_spec, eqbit_spec
        by (apply N.mod_lt; lia);
      cbn [N.size]; destruct (_ =? _); destruct (_ =? _); reflexivity.
    - unfold G. cbn [tr chop cond]. rewrite !par_spec, eqbit_spec by (apply N.mod_lt; lia).
      cbn [N.size]. rewrite N.pow_1_r. destruct (_ =? _); reflexivity. }
  unfold eqN. fold G.
  assert (Hw : pad (s1 x) y <> 0).
  { rewrite pad_spec, s1_spec. pose proof (N.pow_nonzero 2 (N.size y)). lia. }
  destruct (pad (s1 x) y) as [|p0] eqn:E; [contradiction|]. cbn [R]. rewrite L.
  pose proof (N.size_gt (Npos p0)).
  assert (x < 2 ^ N.size (Npos p0)).
  { rewrite <- E, pad_spec, s1_spec in *. pose proof (N.pow_nonzero 2 (N.size y)). nia. }
  assert (y < 2 ^ N.size (Npos p0)).
  { rewrite <- E, pad_spec, s1_spec in *. pose proof (N.size_gt y). nia. }
  rewrite !N.mod_small by assumption. reflexivity.
Qed.

Lemma size_pow2 x : N.size (2 ^ x) = N.succ x.
Proof.
  rewrite N.size_log2 by (apply N.pow_nonzero; lia). rewrite N.log2_pow2 by lia. reflexivity.
Qed.

Lemma pw2_spec x y : pw2 x y = if (y =? 2 ^ x) then 1 else 0.
Proof.
  unfold pw2. destruct y as [|p].
  - pose proof (N.pow_nonzero 2 x). destruct (N.eqb_spec 0 (2 ^ x)); [lia | reflexivity].
  - cbn [cond]. rewrite !eqN_spec, len_spec, inc_spec, pad_spec, N.mul_1_l.
    assert (Ht : N.size (tr (Npos p)) = N.pred (N.size (Npos p))).
    { destruct p; cbn [tr N.size Pos.size]; try reflexivity;
        rewrite pos_succ, N.pred_succ; reflexivity. }
    rewrite Ht.
    destruct (N.eqb_spec (Npos p) (2 ^ N.pred (N.size (Npos p)))) as [H1|H1];
      destruct (N.eqb_spec (N.size (Npos p)) (N.succ x)) as [H2|H2];
      destruct (N.eqb_spec (Npos p) (2 ^ x)) as [H3|H3]; cbn [cond]; try reflexivity;
      exfalso.
    all: try (rewrite H2, N.pred_succ in H1; contradiction).
    all: rewrite H3 in *; rewrite size_pow2 in *; rewrite ?N.pred_succ in *; contradiction.
Qed.


(** ** Polynomial majorants

    [vmaj σ f m]: the lengths of the values of [f] are bounded by [m], at
    every type: at [N], [m] bounds the length of the number; at [σ ⇒ τ],
    [m a] bounds [f x] for every argument [x] bounded by a monotone [a].
    Every term of PV^ω has a higher-order polynomial majorant: the same
    term, with each constant replaced by its majorant ([pv_maj],
    [BFF_majorant]). Unlike [BFF_hpoly_bound] ([BFFFeasibility]), this is
    about the functionals, not about their costs in a cost model. *)
Fixpoint vmaj (σ : ty) : den σ -> M σ -> Prop :=
  match σ return den σ -> M σ -> Prop with
  | tN => fun x m => (N.size_nat x <= m)%nat
  | σ ⇒ τ => fun f m => forall x a, monotone σ a -> vmaj σ x a -> vmaj τ (f x) (m a)
  end.

Lemma vmaj_mle σ f m m' : vmaj σ f m -> mle σ m m' -> vmaj σ f m'.
Proof.
  revert f m m'; induction σ as [|σ _ τ IH]; intros f m m' Hf Hm; cbn in *; [lia|].
  intros x a Ha Hx. exact (IH _ _ _ (Hf x a Ha Hx) (Hm a a Ha)).
Qed.

Definition pv_maj σ (c : pv σ) : hpoly σ :=
  match c in pv σ return hpoly σ with
  | c0 => db <{ 0 }>
  | cs0 => db <{ λ a, a + 1 }>
  | cs1 => db <{ λ a, a + 1 }>
  | ctr => db <{ λ a, a }>
  | cpad => db <{ λ a b, a + b }>
  | cchop => db <{ λ a _, a }>
  | csmash => db <{ λ a b, b * a + 1 }>
  | ccond => db <{ λ _ b c, b + c }>
  | cpar => db <{ λ _, 1 }>
  | cR => db <{ λ a _ h w, a + h w }>
  end.

Lemma vmaj_cst σ (c : pv σ) : vmaj σ (cinterp σ c) ⟦pv_maj σ c⟧.
Proof.
  destruct c; simpl_hp; simpl_pv.
  - cbn. lia.
  - intros x a _ Hx. cbn in *. pose proof (size_s0 x). lia.
  - intros x a _ Hx. cbn in *. pose proof (size_s1 x). lia.
  - intros x a _ Hx. cbn in *. pose proof (size_tr x). lia.
  - intros x a _ Hx y b _ Hy. cbn in *. pose proof (size_pad x y). lia.
  - intros x a _ Hx y b _ Hy. cbn in *. pose proof (size_chop x y). lia.
  - intros x a _ Hx y b _ Hy. cbn in *. pose proof (size_smash x y). nia.
  - intros x a _ Hx y b _ Hy z c _ Hz. cbn in *. pose proof (size_cond x y z). lia.
  - intros x a _ Hx. cbn in *. pose proof (size_par x). lia.
  - (* R: its values are bounded by those of [h] *)
    intros a am _ Ha F mF _ _ h mh Hmh Hh w wm _ Hw. cbn in *.
    pose proof (size_R a F h w). pose proof (Hh w (N.size_nat w) (le_n _) (le_n _)).
    pose proof (Hmh _ _ Hw). lia.
Qed.

Fixpoint vmaj_env (Γ : list ty) : envT N Γ -> envT nat Γ -> Prop :=
  match Γ with
  | [] => fun _ _ => True
  | σ :: Γ => fun e me =>
      vmaj_env Γ (etl e) (etl me) /\ monotone σ (ehd me) /\ vmaj σ (ehd e) (ehd me)
  end.

Lemma vmaj_env_mono Γ e me : vmaj_env Γ e me -> rel_env mle Γ me me.
Proof.
  revert e me; induction Γ as [|σ Γ IH]; intros e me He; [exact I|].
  destruct He as (He & Hm & _). exact (conj (IH _ _ He) Hm).
Qed.

Lemma vmaj_interp Γ σ (t : term pv Γ σ) e me :
  vmaj_env Γ e me -> vmaj σ (interp t e) (interp (csubst pv_maj t) me).
Proof.
  revert e me. induction t as [Γ σ x|Γ σ c|Γ σ τ t IH|Γ σ τ t IHt u IHu]; intros e me He.
  - induction x as [Γ σ|Γ σ τ x IHx]; [apply He | exact (IHx _ _ (proj1 He))].
  - eapply vmaj_mle; [apply vmaj_cst | apply mle_wk].
  - intros x a Ha Hx. exact (IH (ECons e x) (ECons me a) (conj He (conj Ha Hx))).
  - exact (IHt e me He _ _ (mle_interp _ _ _ _ _ (vmaj_env_mono _ _ _ He)) (IHu e me He)).
Qed.

Theorem BFF_majorant σ (t : term pv [] σ) : vmaj σ ⟦t⟧ ⟦csubst pv_maj t⟧.
Proof. exact (vmaj_interp [] σ t tt tt I). Qed.
