(** This module defines the _verification_ versions of:
    - Terms.
    - Thinnings and substitutions.
    - Smart weakening on terms. *)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Index.

(***********************************************************************)
(** * Evar identifiers *)
(***********************************************************************)

(** [evar_id] is the type of evar identifier. You can think of [evar_id]
    as simply [nat], but the actual implementaion
    is kept abstract to demonstrate that we only need decidable equality on
    evar identifiers.
*)
Parameter evar_id : Type.

(** [evar_id_eqb x y] checks whether the evar identifiers [x] and [y] are equal. *)
Parameter evar_id_eqb : evar_id -> evar_id -> bool.

(** Specification of [evar_id_eqb]. *)
Parameter evar_id_eqb_spec : forall x y, reflect (x = y) (evar_id_eqb x y).

Lemma evar_id_eqb_same x : evar_id_eqb x x = true.
Proof. destruct (evar_id_eqb_spec x x) ; auto. Qed.

Lemma evar_id_eqb_diff x y :
  x <> y -> evar_id_eqb x y = false.
Proof.
destruct (evar_id_eqb_spec x y) ; subst ; auto. intros H. exfalso. now apply H.
Qed.

(***********************************************************************)
(** * Terms *)
(***********************************************************************)

(** Verification terms [term s] model concrete terms [term s], modulo a
    couple simplifications to ease reasoning:
    - verification terms don't include names of binders.
    - verification terms use binary applications instead of n-ary applications.

    In [term s] the scope is a _non-uniform_ parameter: this gives slightly
    better behaviour in dependent pattern matching.
*)
Inductive term (s : scope) : Type :=
(** [Type_] is the type of types (i.e. [Type] in Rocq).
    For the moment we don't support universes or other sorts such as [Prop]. *)
| Type_ : term s
(** [TVar i] is a local variable, encoded using a de Bruijn index [i]. *)
| Var (i : index s) : term s
(** [Lam x ty body] represents the lambda abstraction [fun x : ty => body]. *)
| Lam (x : tag) (ty : term s) (body : term (s ▷ x)) : term s
(** [Prod x a b] represents the dependent product [forall x : a, b].
    If [b] does not depend on [x] the product is non-dependent: [a -> b]. *)
| Prod (x : tag) (a : term s) (b : term (s ▷ x)) : term s
(** [App t u] represents the application of the function [t] to the
    argument [u]. *)
| App (t u : term s) : term s
(** [Evar e] represents an existential variable (evar) used for unification.
    Information pertaining to evars is stored in the evar-map. *)
| Evar (e : evar_id) : term s.

Arguments Type_ {s}.
Arguments Var {s}.
Arguments Lam {s}.
Arguments Prod {s}.
Arguments App {s}.
Arguments Evar {s}.

Derive Signature NoConfusion NoConfusionHom for term.

(** Size of a term. *)
Equations term_size {s} : term s -> nat :=
term_size Type_ := 0 ;
term_size (Var _) := 0 ;
term_size (Lam x ty body) := term_size ty + term_size body + 1 ;
term_size (Prod x a b) := term_size a + term_size b + 1 ;
term_size (App t u) := term_size t + term_size u + 1 ;
term_size (Evar _) := 0.

(** N-ary application. *)
Equations apps {s} : term s -> list (term s) -> term s :=
apps t [] := t ;
apps t (u :: us) := apps (App t u) us.

Lemma apps_nil {s} (t : term s) : apps t [] = t.
Proof. reflexivity. Qed.

Lemma apps_cons {s} (t : term s) u us :
  apps t (u :: us) = apps (App t u) us.
Proof. reflexivity. Qed.

Lemma apps_app {s} f (ts us : list (term s)) :
  apps f (ts ++ us) = apps (apps f ts) us.
Proof.
induction ts in f, us |- * ; cbn ; simp apps. reflexivity.
Qed.

(** The head of an application is the subterm in function position,
    and the head of any other term is the complete term. *)
Fixpoint head {s} (t : term s) : term s :=
  match t with
  | App t _ => head t
  | _ => t
  end.

(***********************************************************************)
(** * Simple test functions *)
(***********************************************************************)

Definition is_type {s} (t : term s) : Prop :=
  match t with Type_ => True | _ => False end.

Definition is_var {s} (t : term s) : Prop :=
  match t with Var _ => True | _ => False end.

Definition is_lam {s} (t : term s) : Prop :=
  match t with Lam _ _ _ => True | _ => False end.

Definition is_prod {s} (t : term s) : Prop :=
  match t with Prod _ _ _ => True | _ => False end.

Definition is_app {s} (t : term s) : Prop :=
  match t with App _ _ => True | _ => False end.

Definition is_evar {s} (t : term s) : Prop :=
  match t with Evar _ => True | _ => False end.

(***********************************************************************)
(** * Thinnings *)
(***********************************************************************)

(** [thinning s s'] is the type of verification thinnings from scope [s] to scope [s'].
    Thinnings are order-preserving renamings and are thus injective: the operation
    [thicken] is the partial inverse of [thin].

    We could think of simply encoding a thinning as a pair of a renaming and a
    proof of monotonicity. We do *not* choose this encoding because it makes it
    impossible to define the function [thicken] (we would only be able to
    write [thicken] as a relation).
*)
Inductive thinning : scope -> scope -> Type :=
| ThinNil : thinning ∅ ∅
| ThinSkip {s s'} x : thinning s s' -> thinning s (s' ▷ x)
| ThinKeep {s s'} x : thinning s s' -> thinning (s ▷ x) (s' ▷ x).

Arguments ThinSkip {s s'}.
Arguments ThinKeep {s s'}.

Derive Signature NoConfusion NoConfusionHom for thinning.

(** Identity thinning. *)
Equations tid {s} : thinning s s :=
@tid ∅ := ThinNil ;
@tid (s ▷ x) := ThinKeep x tid.

(** Shift thinning. *)
Definition tshift {s x} : thinning s (s ▷ x) :=
  ThinSkip x tid.

(** [tcomp δ1 δ2] is the composition of the thinning [δ1] followed by the thinning [δ2]. *)
Equations tcomp {s s' s''} : thinning s s' -> thinning s' s'' -> thinning s s'' :=
tcomp ThinNil δ2 := δ2 ;
tcomp δ1 (ThinSkip x δ2) := ThinSkip _ (tcomp δ1 δ2) ;
tcomp (ThinKeep x δ1) (ThinKeep _ δ2) := ThinKeep x (tcomp δ1 δ2) ;
tcomp (ThinSkip x δ1) (ThinKeep _ δ2) := ThinSkip x (tcomp δ1 δ2).

(** [replace_tag x] is a thinning which replaces the tag of variable [I0] with [x].
    Computationally it behaves as the identity. *)
Definition replace_tag {s x0} (x : tag) : thinning (s ▷ x0) (s ▷ x).
destruct x0. destruct x. exact tid.
Defined.

(** Apply a thinning to an index. *)
Equations tapply {s s'} : thinning s s' -> index s -> index s' :=
tapply (ThinSkip x δ) i := IS (tapply δ i) ;
tapply (ThinKeep x δ) I0 := I0 ;
tapply (ThinKeep x δ) (IS i) := IS (tapply δ i).

(** Apply a thinning to a term. *)
Equations thin {s s'} (δ : thinning s s') (t : term s) : term s' :=
thin δ Type_ := Type_ ;
thin δ (Var i) := Var (tapply δ i) ;
thin δ (Lam x ty body) := Lam x (thin δ ty) (thin (ThinKeep x δ) body) ;
thin δ (Prod x a b) := Prod x (thin δ a) (thin (ThinKeep x δ) b) ;
thin δ (App f arg) := App (thin δ f) (thin δ arg) ;
thin δ (Evar ev) := Evar ev.

Section Thicken.
  #[local] Notation "f <$> x" := (option_map f x)
    (at level 61, left associativity).

  #[local] Notation "f <*> x" := (option_apply f x)
    (at level 62, left associativity).

  (** [tapply_inv δ i] is the partial inverse of [tapply]: it finds an
      index [i'] if it exists such that [tapply δ i' = i]. *)
  Equations tapply_inv {s s'} : thinning s s' -> index s' -> option (index s) :=
  tapply_inv (ThinSkip x δ) I0 := None ;
  tapply_inv (ThinSkip x δ) (IS i) := tapply_inv δ i ;
  tapply_inv (ThinKeep x δ) I0 := Some I0 ;
  tapply_inv (ThinKeep x δ) (IS i) := IS <$> tapply_inv δ i.

  (** [thicken δ t'] is the partial inverse of [thin]: if computes a term [t]
      if it exists such that [thin δ t = t']. *)
  Equations thicken {s s'} : thinning s s' -> term s' -> option (term s) :=
  thicken δ Type_ := Some Type_ ;
  thicken δ (Var i) := Var <$> tapply_inv δ i ;
  thicken δ (Lam x ty body) := Lam x <$> thicken δ ty <*> thicken (ThinKeep x δ) body ;
  thicken δ (Prod x a b) := Prod x <$> thicken δ a <*> thicken (ThinKeep x δ) b ;
  thicken δ (App f arg) := App <$> thicken δ f <*> thicken δ arg ;
  thicken δ (Evar e) := Some (Evar e).

End Thicken.

(***********************************************************************)
(** * Substitutions *)
(***********************************************************************)

(** [subst s s'] is the type of substitutions from scope [s] to scope [s'].
    We wrap the underlying function [index s -> term s'] in a record
    to avoid setoid rewrite issues.

    Use [sapply σ i] to apply a substitution [σ] to an index [i]. *)
Record subst (s s' : scope) := {
  sapply : index s -> term s'
}.

Arguments sapply {s s'}.

(** [sid] is the identity substitution. *)
Definition sid {s} : subst s s := {|
  sapply i := Var i
|}.

(** [sshift] is the substitution which increments every index. *)
Definition sshift {s α} : subst s (s ▷ α) := {|
  sapply i := Var (IS i)
|}.

(** [stcomp σ δ] is the composition of substitution [σ] followed by thinning [δ]. *)
Definition stcomp {s1 s2 s3} (σ1 : subst s1 s2) (δ2 : thinning s2 s3) : subst s1 s3 := {|
  sapply i := thin δ2 (sapply σ1 i)
|}.

(** [tscomp δ σ] is the composition of thinning [δ] followed by substitution [σ]. *)
Definition tscomp {s1 s2 s3} (δ1 : thinning s1 s2) (σ2 : subst s2 s3) : subst s1 s3 := {|
  sapply i := sapply σ2 (tapply δ1 i)
|}.

Equations scons_aux {s s' x} : term s' -> subst s s' -> index (s ▷ x) -> term s' :=
scons_aux t σ I0 := t ;
scons_aux t σ (IS i) := sapply σ i.

(** [scons x t σ] maps [I0] to [t] and [IS i] to [σ i]. *)
Definition scons {s s'} x (t : term s') (σ : subst s s') : subst (s ▷ x) s' := {|
  sapply i := scons_aux t σ i
|}.

(** [sup σ] lifts [σ] through a binder. *)
Definition sup {s s'} x (σ : subst s s') : subst (s ▷ x) (s' ▷ x) :=
  scons x (Var I0) (stcomp σ tshift).

(** Apply a substitution to a term. *)
Equations substitute {s s'} : subst s s' -> term s -> term s' :=
substitute σ Type_ := Type_ ;
substitute σ (Var i) := sapply σ i ;
substitute σ (Lam x ty body) := Lam x (substitute σ ty) (substitute (sup x σ) body) ;
substitute σ (Prod x a b) := Prod x (substitute σ a) (substitute (sup x σ) b) ;
substitute σ (App t u) := App (substitute σ t) (substitute σ u) ;
substitute σ (Evar e) := Evar e.

(** [scomp σ1 σ2] is the composition of [σ1] followed by [σ2]. *)
Definition scomp {s1 s2 s3} (σ1 : subst s1 s2) (σ2 : subst s2 s3) : subst s1 s3 := {|
  sapply i := substitute σ2 (sapply σ1 i)
|}.

(** [subst_of_thin δ] lifts a thinning [δ] into an equivalent subtitution. *)
Definition subst_of_thin {s s'} (δ : thinning s s') : subst s s' := {|
  sapply i := Var (tapply δ i)
|}.

(** [t[x := u]] substitutes variable [x] with [u] in [t].
    It assumes the scope of [t] is of the form [_ ▷ x]. *)
#[global] Notation "t [ x ::= u ]" := (substitute (@scons _ _ x u sid) t)
  (at level 10, format "t [ x  ::=  u ]").

(***********************************************************************)
(** * Smart constructors *)
(***********************************************************************)

(** [wk_idx] is a thinning which weakens any index [i] into the ambient scope. *)
Fixpoint wk_idx {s s'} {wit : scope_incl s s'} : thinning s s' :=
  match wit with
  | scope_incl_refl => tid
  | scope_incl_keep x wit => ThinKeep x (@wk_idx _ _ wit)
  | scope_incl_skip x wit => ThinSkip x (@wk_idx _ _ wit)
  end.

(** [wk t] weakens the term [t] to the current scope. *)
Definition wk {s s'} `{scope_incl s s'} (t : term s) : term s' :=
  thin wk_idx t.

(** [arrow a b] builds the non-dependent product [a -> b]. *)
Definition arrow {s} (a b : term s) : term s :=
  Prod TAG a (wk b).

(*(** [lam ty body] builds the lambda abstraction [fun x : ty => body] in HOAS style. *)
Definition lam {s} (ty : term s) (body : forall x, term (s ▷ x)) : term s :=
  Lam TAG ty (body TAG).

(** [prod ty body] builds the dependent product [forall x : a, b] in HOAS style. *)
Definition prod {s} (a : term s) (b : forall x, term (s ▷ x)) : term s :=
  Prod TAG a (b TAG).
*)
