(** This module defines:
    - One-step reduction of contexts [cred1].
    - Multi-step reduction of contexts [cred].
    And proves basic properties, notably an alternate induction principle
    [cred_ind_alt] which expresses the fact that [cred] is the reflexive
    transitive closure of [cred1].
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.Context Theory.Relations Theory.Reduction.SubstReduction.

(***********************************************************************)
(** * One-step reduction of contexts *)
(***********************************************************************)

(** [cred1 flags Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    exactly one reduction step. *)
Inductive cred1 (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred1_head {s} Γ x (ty ty' : term s) :
    Σ ⊢ ty ~>{flags} ty' ->
    cred1 flags Σ (Cons Γ x ty) (Cons Γ x ty')

| cred1_tail {s} Γ Γ' x (ty : term s) :
    cred1 flags Σ Γ Γ' ->
    cred1 flags Σ (Cons Γ x ty) (Cons Γ' x ty).

Derive Signature for cred1.

(***********************************************************************)
(** * Multi-step reduction of contexts *)
(***********************************************************************)

(** [cred flags Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    zero or more reduction step.

    Note that we do not define [cred] as the reflexive-transitive closure
    of [cred1]: this fact is instead expressed by the lemma [cred_ind_alt].
    Consider using the tactic [induction H using cred_ind_alt] if you have
    a proof [H : cred flags Σ Γ Γ']. *)
Inductive cred (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred_nil : cred flags Σ Nil Nil

| cred_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ~~>{flags} ty' ->
    cred flags Σ Γ Γ' ->
    cred flags Σ (Cons Γ x ty) (Cons Γ' x ty').

Derive Signature for cred.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

#[export] Instance cred_Reflexive s flags Σ : Reflexive (@cred flags Σ s).
Proof.
intros Γ. induction Γ ; constructor.
- reflexivity.
- assumption.
Qed.

#[export] Instance cred_Transitive s flags Σ : Transitive (@cred flags Σ s).
Proof.
intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
- reflexivity.
- constructor.
  + now rewrite H.
  + now apply IHcred.
Qed.

#[export] Instance cred_of_cred1 s flags Σ :
  subrelation (@cred1 flags Σ s) (@cred flags Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

#[export] Instance cred1_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@cred1).
Proof.
intros f f' Hf Σ Σ' HΣ s Γ ? <- Γ' ? <- H. induction H.
- constructor. now rewrite <-Hf, <-HΣ.
- constructor. assumption.
Qed.

#[export] Instance cred_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@cred).
Proof.
intros f f' Hf Σ Σ' HΣ s Γ ? <- Γ' ? <- H. induction H.
- constructor.
- constructor.
  + now rewrite <-Hf, <-HΣ.
  + assumption.
Qed.

(** Due to technical limitations of setoid rewriting we need to split
    the [Proper] instances for [Cons] in two parts. *)

#[export] Instance cred1_Cons_congr_1 {s flags Σ} (Γ : context ∅ s) x :
  Proper (red1 flags Σ ==> cred1 flags Σ) (Cons Γ x).
Proof. intros ty ty' Hty. now constructor. Qed.

#[export] Instance cred_Cons_congr_1 {s flags Σ} (Γ : context ∅ s) x :
  Proper (red flags Σ ==> cred flags Σ) (Cons Γ x).
Proof. intros ty ty' Hty. now constructor. Qed.

#[export] Instance cred1_Cons_congr_2 {s flags Σ} :
  Proper (cred1 flags Σ ==> ∀ x, eq ==> cred1 flags Σ) (@Cons ∅ s).
Proof. intros Γ Γ' HΓ x ty ? <-. now constructor. Qed.

#[export] Instance cred_Cons_congr_2 {s flags Σ} :
  Proper (cred flags Σ ==> ∀ x, eq ==> cred flags Σ) (@Cons ∅ s).
Proof. intros Γ Γ' HΓ x ty ? <-. now constructor. Qed.

(***********************************************************************)
(** * Lemmas about context reduction *)
(***********************************************************************)

Lemma lookup_context_cred1 {s flags Σ} (i : index s) Γ Γ' :
  cred1 flags Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ~>{flags} lookup_context i Γ' \/
  lookup_context i Γ = lookup_context i Γ'.
Proof.
intros Hred. induction Hred ; depelim i ; simp lookup_context ; simp_subst.
- left. now apply red1_thin.
- now right.
- now right.
- destruct (IHHred i) as [H1 | H2].
  + left. apply red1_thin. apply H1.
  + right. now rewrite H2.
Qed.

#[export] Instance lookup_context_cred {s flags Σ} (i : index s) :
  Proper (cred flags Σ ==> red flags Σ) (@lookup_context s i).
Proof.
intros Γ Γ' HΓ. induction HΓ ; depelim i ; simp lookup_context ; simp_subst.
- now rewrite H.
- now rewrite IHHΓ.
Qed.

Lemma cred_is_clos_cred1_aux1 {s x flags Σ} (Γ Γ' : context ∅ s) ty :
  refl_trans_clos (cred1 flags Σ) Γ Γ' ->
  refl_trans_clos (cred1 flags Σ) (Cons Γ x ty) (Cons Γ' x ty).
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHrefl_trans_clos. apply refl_trans_clos_one. now constructor.
Qed.

Lemma cred_is_clos_cred1_aux2 {s x flags Σ} (Γ : context ∅ s) ty ty' :
  Σ ⊢ ty ~>{flags} ty' ->
  refl_trans_clos (cred1 flags Σ) (Cons Γ x ty) (Cons Γ x ty').
Proof. intros H. apply refl_trans_clos_one. now constructor. Qed.

(** [cred] is the reflexive-transitive closure of [cred1]. *)
Lemma cred_is_clos_cred1 {s flags Σ} (Γ Γ' : context ∅ s) :
  cred flags Σ Γ Γ' <-> refl_trans_clos (cred1 flags Σ) Γ Γ'.
Proof.
split ; intros H.
- induction H.
  + reflexivity.
  + induction H.
    * now apply cred_is_clos_cred1_aux1.
    * rewrite IHred by assumption. now apply cred_is_clos_cred1_aux2.
- induction H.
  + reflexivity.
  + rewrite IHrefl_trans_clos, H0. reflexivity.
Qed.

(** Alternate induction principle for [cred] which expresses the fact that
    [cred] is the reflexive-transitive closure of [cred1]. *)
Lemma cred_ind_alt flags Σ
  (P : forall s, context ∅ s -> context ∅ s -> Prop)
  (Hrefl : forall s Γ, P s Γ Γ)
  (Hstep : forall s Γ1 Γ2 Γ3,
    cred flags Σ Γ1 Γ2 -> P s Γ1 Γ2 ->
    cred1 flags Σ Γ2 Γ3 ->
    P s Γ1 Γ3) :
  forall s Γ1 Γ2, cred flags Σ Γ1 Γ2 -> P s Γ1 Γ2.
Proof.
intros s Γ1 Γ2 H. rewrite cred_is_clos_cred1 in H. induction H.
- apply Hrefl.
- apply Hstep with y ; auto. now rewrite cred_is_clos_cred1.
Qed.
