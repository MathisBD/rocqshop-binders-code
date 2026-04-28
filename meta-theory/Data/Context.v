(** This module defines the verification version of local contexts,
    which store the types of local variables in a given scope. *)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.Term.

(** [context s s'] is a context embedding terms from the inner scope [s']
    into the outer scope [s]. In other words:
    - [s'] is an extension of [s].
    - The context gives the types of all variables which are in [s'] but not in [s]. *)
Inductive context (s : scope) : scope -> Type :=
| Nil : context s s
| Cons {s'} (ctx : context s s') (x : tag) (ty : term s') : context s (s' ▷ x).

Arguments Nil {s}.
Arguments Cons {s s'}.

Derive Signature NoConfusion NoConfusionHom for context.

(** If we have a context from scope [s] to [s'] then we can weaken terms
    from [s] to [s']. *)
Equations scope_incl_context {s s'} : context s s' -> scope_incl s s' :=
scope_incl_context Nil := scope_incl_refl ;
scope_incl_context (Cons Γ x _) := scope_incl_skip x (scope_incl_context Γ).

(** Length of a context (i.e. number of variables it contains). *)
Equations context_length {s s'} : context s s' -> nat :=
context_length Nil := 0 ;
context_length (Cons ctx _ _) := S (context_length ctx).

(** Concatenate two contexts. *)
Equations app_context {s s' s''} : context s s' -> context s' s'' -> context s s'' :=
app_context Γ Nil := Γ ;
app_context Γ (Cons Γ' x ty) := Cons (app_context Γ Γ') x ty.

Declare Scope context_scope.
Delimit Scope context_scope with context.
Bind Scope context_scope with context.

Notation "Γ1 ++ Γ2" := (app_context Γ1 Γ2)
  (right associativity, at level 60) : context_scope.

Lemma app_context_nil_l {s s'} (Γ : context s s') :
  (Nil ++ Γ)%context = Γ.
Proof.
depind Γ ; simp app_context.
- reflexivity.
- rewrite IHΓ. reflexivity.
Qed.
#[export] Hint Rewrite @app_context_nil_l : app_context.

(** Lookup the type of a variable in a full context. *)
Equations lookup_context {s} : index s -> context ∅ s -> term s :=
lookup_context I0 (Cons ctx x ty) := wk ty ;
lookup_context (IS i) (Cons ctx x ty) := wk (lookup_context i ctx).

Equations prod_context {s s'} : context s s' -> term s' -> term s :=
prod_context Nil body := body ;
prod_context (Cons ctx x ty) body := prod_context ctx $ Prod x ty body.

Equations lam_context {s s'} : context s s' -> term s' -> term s :=
lam_context Nil body := body ;
lam_context (Cons ctx x ty) body := lam_context ctx $ Lam x ty body.

Equations context_indices {s s'} : context s s' -> list (index s') :=
context_indices Nil := [] ;
context_indices (Cons ctx _ _) := map IS (context_indices ctx) ++ [I0].

(** [context_subst Γ ts] is a substitution which replaces the variables bound in [Γ]
    with the terms in [ts]. The list [ts] is in the same order as the context [Γ]:
    de Bruijn index [0] corresponds to the last term in [ts].

    We assume the length of [ts] is equal to the length of [Γ]. *)
Equations context_subst {s s'} (Γ : context s s') (ts : list (term s)) : subst s' s :=
context_subst Nil _ := sid ;
context_subst (Cons Γ x ty) ts :=
  match snoc ts with
  | Some (ts, t) => scons x t (context_subst Γ ts)
  | None =>
    (* This case should never happen.
       We substitute [x] with a dummy term [Type_]. *)
    scons x Type_ (context_subst Γ [])
  end.