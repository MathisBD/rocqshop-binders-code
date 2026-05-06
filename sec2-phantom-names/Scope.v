(** This file defines tags, scopes, and typeclasses for scope membership and inclusion. *)

From Equations Require Export Equations.

(** We allow [Equations] to use UIP instances, e.g. when deriving
    instances of [NoConfusion] or [NoConfusionHom]. *)
#[export] Set Equations With UIP.

(***********************************************************************)
(** * Tags *)
(***********************************************************************)

(** [tag] represents phantom tags which are completely proof irrelevant and
    computationally irrelevant but are used to guide type-class resolution.
    Phantom tags enable one to build smart weakening operations
    (e.g. [wk] below).

    We put phantom tags in [Prop] so that they are erased by extraction. *)
Inductive tag : Prop :=
| TAG.

Derive NoConfusion for tag.

(** All tags are equal. *)
Lemma tag_eq (x y : tag) : x = y.
Proof. destruct x ; destruct y ; reflexivity. Qed.

#[export] Instance tag_EqDec : EqDec tag.
Proof. intros [] []. now left. Defined.

(***********************************************************************)
(** * Scopes *)
(***********************************************************************)

(** [scope] is isomorphic to the set of natural numbers [nat], but additionally
    contains phantom tags. *)
Inductive scope : Set :=
| SNil
| SCons (s : scope) (x : tag).

Derive NoConfusion for scope.

#[export] Instance scope_EqDec : EqDec scope.
Proof.
intros s s'. depind s ; depelim s'.
- now left.
- right. intros H. depelim H.
- right. intros H. depelim H.
- destruct (IHs s') ; destruct (eq_dec x x0) ; subst.
  + now left.
  + right. intros H. depelim H. auto.
  + right. intros H. depelim H. auto.
  + right. intros H. depelim H. auto.
Defined.

(** [∅] is the empty scope: it contains no variables. *)
Notation "∅" := SNil.

(** [s ▷ x] is the scope [s] extended with one variable [x].
    You can use index [I0] to refer to [x] and [IS] to refer
    to variables in [s]. *)
Notation "s ▷ x" := (SCons s x) (at level 20, left associativity).
