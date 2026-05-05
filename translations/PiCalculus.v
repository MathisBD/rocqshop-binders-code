(** This file defines a translation from the lambda calculus with explicit
    substitutions to the pi calculus. *)

From Common Require Import Index.

Notation "f $ x" := (f x) (at level 67, right associativity, only parsing).

(**************************************************************************)
(** * Lambda calculus with explicit substitutions *)
(**************************************************************************)

Inductive lterm (s : scope) :=
(** Variable constructor (using a de Bruijn index). *)
| lvar (i : index s)
(** Binary application. *)
| lapp (t u : lterm s)
(** Lambda abstraction. *)
| llam (x : tag) (body : lterm (s ▷ x))
(** Explicit substitution: [lsubst x t u] represents t[x := u]. *)
| lsubst (x : tag) (t : lterm (s ▷ x)) (u : lterm s).

Arguments lvar {s}.
Arguments lapp {s}.
Arguments llam {s}.
Arguments lsubst {s}.

Definition llam_fresh {s} (t : forall x, lterm (s ▷ x)) : lterm s :=
  llam TAG (t TAG).

Definition lsubst_fresh {s} (t : forall x, lterm (s ▷ x)) (u : lterm s) : lterm s :=
  lsubst TAG (t TAG) u.

Fixpoint lthin {s s'} (δ : thinning s s') (t : lterm s) : lterm s' :=
  match t with
  | lvar i => fun δ => lvar (tapply δ i)
  | lapp t u => fun δ => lapp (lthin δ t) (lthin δ u)
  | llam x t => fun δ => llam x (lthin (ThinKeep x δ) t)
  | lsubst x t u => fun δ => lsubst x (lthin (ThinKeep x δ) t) (lthin δ u)
  end δ.

(** Smart variable constructor. *)
Definition lvar_of {s} (x : tag) `{scope_mem x s} : lterm s :=
  lvar (idx_of x).

(** Smart weakening. *)
Definition lweak {s s'} `{scope_incl s s'} (t : lterm s) : lterm s' :=
  lthin wk_idx t.

(**************************************************************************)
(** * Pi calculus *)
(**************************************************************************)

Inductive pterm (s : scope) :=
(** Variable constructor. *)
| pvar (i : index s)
(** Null process. *)
| pzero
(** Parallel composition. *)
| ppar (t u : pterm s)
(** [pout c v] sends [v] on channel [c]. *)
| pout (c v : pterm s)
(** [pout2 c v u] sends [v] and [u] on channel [c]. *)
| pout2 (c v u : pterm s)
(** [pin c x k] receives one value [x] on channel [c] with continuation [k]. *)
| pin (c : pterm s) (x : tag) (k : pterm (s ▷ x))
(** [pin c x y k] receives two values [x] and [y] on channel [c] with continuation [k]. *)
| pin2 (c : pterm s) (x y : tag) (k : pterm (s ▷ x ▷ y))
(** [pnu k] creates a fresh variable (process name) and passes it to the continuation [k]. *)
| pnu (x : tag) (k : pterm (s ▷ x)).

Arguments pvar {s}.
Arguments pzero {s}.
Arguments ppar {s}.
Arguments pout {s}.
Arguments pout2 {s}.
Arguments pin {s}.
Arguments pin2 {s}.
Arguments pnu {s}.

(** Ternary composition. *)
Definition ppar3 {s} (t u v : pterm s) : pterm s :=
  ppar (ppar t u) v.

Definition pin_fresh {s} (c : pterm s) (k : forall x : tag, pterm (s ▷ x)) : pterm s :=
  pin c TAG (k TAG).

Definition pin2_fresh {s} (c : pterm s) (k : forall x y : tag, pterm (s ▷ x ▷ y)) : pterm s :=
  pin2 c TAG TAG (k TAG TAG).

Definition pin2_named_fresh {s} (c : pterm s) (x : tag) (k : forall y : tag, pterm (s ▷ x ▷ y)) : pterm s :=
  pin2 c x TAG (k TAG).

Definition pnu_fresh {s} (k : forall x : tag, pterm (s ▷ x)) : pterm s :=
  pnu TAG (k TAG).

Fixpoint pthin {s s'} (δ : thinning s s') (t : pterm s) : pterm s' :=
  match t with
  | pvar i => fun δ => pvar (tapply δ i)
  | pzero => fun δ => pzero
  | ppar t u => fun δ => ppar (pthin δ t) (pthin δ u)
  | pout c x => fun δ => pout (pthin δ c) (pthin δ x)
  | pout2 c x y => fun δ => pout2 (pthin δ c) (pthin δ x) (pthin δ y)
  | pin c x k => fun δ => pin (pthin δ c) x (pthin (ThinKeep x δ) k)
  | pin2 c x y k => fun δ => pin2 (pthin δ c) x y (pthin (ThinKeep y (ThinKeep x δ)) k)
  | pnu x k => fun δ => pnu x (pthin (ThinKeep x δ) k)
  end δ.

(** Smart variable constructor. *)
Definition pvar_of {s} (x : tag) `{scope_mem x s} : pterm s :=
  pvar (idx_of x).

(** Smart weakening. *)
Definition pweak {s s'} `{scope_incl s s'} (t : pterm s) : pterm s' :=
  pthin wk_idx t.

(**************************************************************************)
(** * Translation function *)
(**************************************************************************)

(** The translation function is not structurally recursive.
    We could define it by induction on the size of the input term,
    or by working in a monad which supports general recursion.
    We choose to disable guard checking for simplicity. *)
Unset Guard Checking.

Fixpoint translate {s} (t : lterm s) {struct t} : pterm s -> pterm s :=
  match t with
  | lvar x => fun a =>
      pout (pvar x) a
  | lapp t u => fun a =>
      pnu_fresh $ fun b =>
      pnu_fresh $ fun x =>
      ppar3 (translate (lweak t) (pvar_of b))
            (pout2 (pvar_of b) (pvar_of x) (pweak a))
            (pin_fresh (pvar_of x) $ fun c => translate (lweak u) (pvar_of c))
  | llam x t => fun a =>
      pin2_named_fresh a x $ fun b => translate (lweak t) (pvar_of b)
  | lsubst x t u => fun a =>
      pnu x $
      ppar (translate (lweak t) (pweak a))
           (pin_fresh (pvar_of x) $ fun b => translate (lweak u) (pvar_of b))
  end.