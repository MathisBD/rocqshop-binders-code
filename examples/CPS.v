(** This file defines a CPS translation on a lambda calculus with let-bindings. *)

From Equations Require Import Equations.
From Common Require Import Index Thinnings.

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).

(** Notation for dependent pairs. *)
Notation "⟨ x , y ⟩" := (existT _ x y) (format "⟨ x ,  y ⟩").

(***********************************************************************)
(** * Term syntax *)
(***********************************************************************)

(** The lambda calculus with let-bindings. *)
Inductive term (s : scope) : Type :=
(** [TVar i] is a local variable, encoded using a de Bruijn index [i]. *)
| Var (i : index s)
(** [Lam x body] represents the lambda abstraction [fun x => body]. *)
| Lam (x : tag) (body : term (s ▷ x))
(** [App t u] represents the application of the function [t] to the
    argument [u]. *)
| App (t u : term s)
(** [LetIn x t u] represents the let-binding [let x := t in u]. *)
| LetIn (x : tag) (t : term s) (u : term (s ▷ x)).

Arguments Var {s}.
Arguments Lam {s}.
Arguments App {s}.
Arguments LetIn {s}.

(***********************************************************************)
(** * Basic operations on terms *)
(***********************************************************************)

(** [#x] builds the term corresponding to a tag [x]. *)
Notation "# x" := (Var (idx_of x)) (at level 1, format "# x").

(** Apply a thinning to a term. *)
Equations thin {s s'} (δ : thinning s s') (t : term s) : term s' :=
thin δ (Var i) := Var (tapply δ i) ;
thin δ (Lam x body) := Lam x (thin (ThinKeep x δ) body) ;
thin δ (App f arg) := App (thin δ f) (thin δ arg) ;
thin δ (LetIn x t u) := LetIn x (thin δ t) (thin (ThinKeep x δ) u).

(** [wk t] weakens the term [t] to the current scope. *)
Definition wk {s s'} `{scope_incl s s'} (t : term s) : term s' :=
  thin wk_idx t.

(** [lam_fresh body] builds the lambda abstraction [fun x => body] in HOAS style. *)
Definition lam_fresh {s} (body : forall x, term (s ▷ x)) : term s :=
  Lam TAG (body TAG).

(** [letin_fresh t u] builds the let-binding [let x := t in u] in HOAS style. *)
Definition letin_fresh {s} (t : term s) (u : forall x, term (s ▷ x)) : term s :=
  LetIn TAG t (u TAG).

(***********************************************************************)
(** * CPS translation *)
(***********************************************************************)

(** The translation function is not structurally recursive.
    We could define it by induction on the size of the input term,
    or by working in a monad which supports general recursion.
    We choose to disable guard checking for simplicity. *)
Unset Guard Checking.

Fixpoint cps {s} (t : term s) {struct t} : term s -> term s :=
  match t with
  | Var i => fun k =>
    App k (Var i)
  | Lam x t => fun k =>
      App k (Lam x (
        lam_fresh (fun k' => cps (wk t) #k'
      )))
  | App t u => fun k =>
      cps t (lam_fresh (fun x =>
      cps (wk u) (lam_fresh (fun y =>
        App (App #x #y) (wk k)
      ))))
  | LetIn x t u => fun k =>
      cps t (lam_fresh (fun v =>
        LetIn x #v (cps (wk u) (wk k)
      )))
  end.
