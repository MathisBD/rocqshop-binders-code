(** This file defines scopes and (well-scoped) de Bruijn indices. *)

From Equations Require Export Equations.

(** We allow [Equations] to use UIP instances, e.g. when deriving
    instances of [NoConfusion] or [NoConfusionHom]. *)
#[export] Set Equations With UIP.

(***********************************************************************)
(** * Scopes *)
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

(***********************************************************************)
(** * Typeclasses for scope membership and inclusion *)
(***********************************************************************)

(** [scope_mem x s] is a witness of the fact that variable [x]
    occurs in scope [s]. *)
Inductive scope_mem (x : tag) : scope -> Type :=
| scope_mem_here s : scope_mem x (s ▷ x)
| scope_mem_skip y s : scope_mem x s -> scope_mem x (s ▷ y).

Arguments scope_mem_here x {s}.
Arguments scope_mem_skip {x} y {s}.

(** We declare [scope_mem] as a typeclass to allow synthesizing
    a witness automatically. *)
Existing Class scope_mem.
#[export] Existing Instance scope_mem_here.
#[export] Existing Instance scope_mem_skip.

(** [scope_incl s s'] is a witness of the fact that the scope [s]
    is included in the scope [s'], i.e. that there exists a thinning
    from [s] to [s']. *)
Inductive scope_incl : scope -> scope -> Type :=
| scope_incl_refl s : scope_incl s s
| scope_incl_keep x s s' : scope_incl s s' -> scope_incl (s ▷ x) (s' ▷ x)
| scope_incl_skip x s s' : scope_incl s s' -> scope_incl s (s' ▷ x).

Arguments scope_incl_refl {s}.
Arguments scope_incl_keep x {s s'}.
Arguments scope_incl_skip x {s s'}.

(** We declare [scope_incl] as a typeclass to allow synthesizing
    a witness automatically. *)
Existing Class scope_incl.
#[export] Existing Instance scope_incl_refl.
#[export] Existing Instance scope_incl_keep.
#[export] Existing Instance scope_incl_skip.

#[export] Instance scope_incl_empty s : scope_incl ∅ s.
  induction s ; typeclasses eauto.
Defined.

(***********************************************************************)
(** * De Bruijn indices *)
(***********************************************************************)

(** [index s] is the type of de Bruijn indices in scope [s].
    You can think of an index as a natural number which
    tells you how many binders to count up (i.e. going towards the root)
    until you find the corresponding variable. *)
Inductive index : scope -> Type :=
| I0 {s x} : index (s ▷ x)
| IS {s x} : index s -> index (s ▷ x).

Derive Signature NoConfusion NoConfusionHom for index.

(** Boolean equality test on de Bruijn indices. *)
Equations index_eq {s} : index s -> index s -> bool :=
index_eq I0 I0 := true ;
index_eq (IS i) (IS i') := index_eq i i' ;
index_eq _ _ := false.

Lemma index_eq_spec {s} (i i' : index s) :
  reflect (i = i') (index_eq i i').
Proof.
funelim (index_eq i i').
- constructor. reflexivity.
- constructor. intros H ; depelim H.
- constructor. intros H ; depelim H.
- destruct H ; constructor.
  + f_equal. assumption.
  + intros H ; depelim H. auto.
Qed.

(** [idx_of x] returns the index corresponding to the tag [x]
    in the ambient scope [s]. *)
Fixpoint idx_of (x : tag) {s} {wit : scope_mem x s} : index s :=
  match wit with
  | scope_mem_here _ => I0
  | scope_mem_skip _ wit => IS (@idx_of x _ wit)
  end.

(** [tag_of i] creates a tag corresponding to a de Bruijn index [x],
    along with a witness that [x] is included in scope [s]. *)
Fixpoint tag_of {s} (i : index s) : { x & scope_mem x s } :=
  match i with
  | @I0 s x => existT _ x (scope_mem_here x)
  | @IS s x i =>
    let '(existT _ y H) := tag_of i in
    existT _ y (scope_mem_skip x H)
  end.