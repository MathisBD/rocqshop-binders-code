(** This file defines a unary parametricity translation for a simple
    dependently typed calculus. *)

From Equations Require Import Equations.
From PhantomNames Require Import Index.

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).

(** Notation for dependent pairs. *)
Notation "⟨ x , y ⟩" := (existT _ x y) (format "⟨ x ,  y ⟩").

(***********************************************************************)
(** * Term syntax *)
(***********************************************************************)

(** A simple dependently-typed calculus. *)
Inductive term (s : scope) : Type :=
(** [Type_] is the type of types. *)
| Type_
(** [TVar i] is a local variable, encoded using a de Bruijn index [i]. *)
| Var (i : index s)
(** [Lam x ty body] represents the lambda abstraction [fun x : ty => body]. *)
| Lam (x : tag) (ty : term s) (body : term (s ▷ x))
(** [Prod x a b] represents the dependent product [forall x : a, b].
    If [b] does not depend on [x] the product is non-dependent: [a -> b]. *)
| Prod (x : tag) (a : term s) (b : term (s ▷ x))
(** [App t u] represents the application of the function [t] to the
    argument [u]. *)
| App (t u : term s).

Arguments Type_ {s}.
Arguments Var {s}.
Arguments Lam {s}.
Arguments Prod {s}.
Arguments App {s}.

(***********************************************************************)
(** * Basic operations on terms *)
(***********************************************************************)

(** [#x] builds the term corresponding to a tag [x]. *)
Notation "# x" := (Var (idx_of x)) (at level 1, format "# x").

(** Apply a thinning to a term. *)
Equations thin {s s'} (δ : thinning s s') (t : term s) : term s' :=
thin δ Type_ := Type_ ;
thin δ (Var i) := Var (tapply δ i) ;
thin δ (Lam x ty body) := Lam x (thin δ ty) (thin (ThinKeep x δ) body) ;
thin δ (Prod x a b) := Prod x (thin δ a) (thin (ThinKeep x δ) b) ;
thin δ (App f arg) := App (thin δ f) (thin δ arg).

(** [wk t] weakens the term [t] to the current scope. *)
Definition wk {s s'} `{scope_incl s s'} (t : term s) : term s' :=
  thin wk_idx t.

(** [arrow a b] builds the non-dependent product [a -> b]. *)
Definition arrow {s} (a b : term s) : term s :=
  Prod TAG a (wk b).

(** [lam_fresh ty body] builds the lambda abstraction [fun x : ty => body] in HOAS style. *)
Definition lam_fresh {s} (ty : term s) (body : forall x, term (s ▷ x)) : term s :=
  Lam TAG ty (body TAG).

(** [prod_fresh ty body] builds the dependent product [forall x : a, b] in HOAS style. *)
Definition prod_fresh {s} (a : term s) (b : forall x, term (s ▷ x)) : term s :=
  Prod TAG a (b TAG).

(***********************************************************************)
(** * Parametricity translation *)
(***********************************************************************)

(** For each variable [x] we can build another variable [R x].
    It is very important that this definition is opaque (using Qed)
    so that [R x ≡ R y] if and only if [x ≡ y]. *)
Definition R (x : tag) : tag. exact x. Qed.

(** Parametricity translation of a scope: for each variable [x],
    add a variable [R x]. *)
Fixpoint param_scope (s : scope) : scope :=
  match s with
  | ∅ => ∅
  | s ▷ x => param_scope s ▷ x ▷ R x
  end.

(** [s] is included in [param_scope s]. *)
Fixpoint param_scope_incl s : scope_incl s (param_scope s) :=
  match s as s0 return scope_incl s0 (param_scope s0) with
  | ∅ => scope_incl_refl
  | s ▷ x => scope_incl_skip (R x) $ scope_incl_keep x $ param_scope_incl s
  end.
Existing Instance param_scope_incl.

(* If [x] is in scope [s], then [R x] is in scope [param_scope s]. *)
Fixpoint param_scope_mem_R x s (wit : scope_mem x s) : scope_mem (R x) (param_scope s) :=
  match wit with
  | scope_mem_here _ => scope_mem_here (R x)
  | scope_mem_skip y _ => scope_mem_skip (R y) $ scope_mem_skip y $ param_scope_mem_R x _ _
  end.
Existing Instance param_scope_mem_R.

(** Parametricity translation of a term.
    Notation [#x] builds the variable corresponding to tag [x]. *)
Fixpoint param_term {s} (t : term s) : term (param_scope s) :=
  match t with
  | Type_ => lam_fresh Type_ $ fun A => arrow #A Type_
  | Var i =>
    let '⟨x, _⟩ := tag_of i in #(R x)
  | Lam x ty body =>
    let pty := param_term ty in
    let pbody := param_term body in
    Lam x (wk ty) $ Lam (R x) (App (wk pty) #x) pbody
  | Prod x a b =>
    let pa := param_term a in
    let pb := param_term b in
    lam_fresh (wk (Prod x a b)) $ fun f =>
    Prod x (wk a) $
    Prod (R x) (App (wk pa) #x) $
    App (wk pb) (App #f #x)
  | App f arg =>
    let pf := param_term f in
    let parg := param_term arg in
    App (App pf (wk arg)) parg
  end.