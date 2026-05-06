(** This file defines a CPS translation on a lambda calculus with let-bindings. *)

From Equations Require Import Equations.
From PhantomNames Require Import Index.

(***********************************************************************)
(** * Term syntax *)
(***********************************************************************)

(** The lambda calculus with let-bindings. *)
Inductive term (s : scope) : Type :=
(** [Var i] is a local variable, encoded using a de Bruijn index [i]. *)
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

(** [mk_lam body] builds the lambda abstraction [fun x => body] in HOAS style. *)
Definition mk_lam {s} (body : forall x, term (s ▷ x)) : term s :=
  Lam TAG (body TAG).

(** [mk_letin t u] builds the let-binding [let x := t in u] in HOAS style. *)
Definition mk_letin {s} (t : term s) (u : forall x, term (s ▷ x)) : term s :=
  LetIn TAG t (u TAG).

(***********************************************************************)
(** * CPS translation *)
(***********************************************************************)

(** The translation function is not structurally recursive.
    We could define it by induction on the size of the input term,
    or by working in a monad which supports general recursion.
    We choose to disable guard checking for simplicity. *)
Unset Guard Checking.

Fixpoint cps {s} (t : term s) (k : term s) {struct t} : term s :=
  match t with
  | Var i =>
    App k (Var i)
  | Lam x t =>
      App k (Lam x (mk_lam (fun k' => cps (wk t) #k')))
  | App t u =>
      cps t (mk_lam (fun x =>
      cps (wk u) (mk_lam (fun y =>
        App (App #x #y) (wk k)
      ))))
  | LetIn x t u =>
      cps t (mk_lam (fun v =>
        LetIn x #v (cps (wk u) (wk k)
      )))
  end.
