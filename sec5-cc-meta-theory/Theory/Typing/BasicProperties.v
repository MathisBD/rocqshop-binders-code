(** This module proves basic lemmas about the typing relation, notably:
    - The validity lemma: in any typing derivation [Σ ;; Γ ⊢ t : T],
      [T] is itself well-typed.
    - Uniqueness of types (up to conversion).
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Typing.SubstTyping.

(***********************************************************************)
(** * Miscellaneous lemmas *)
(***********************************************************************)

Lemma typing_lookup_context {Σ s} (Γ : context ∅ s) i :
  ctyping Σ Γ ->
  Σ ;; Γ ⊢ lookup_context i Γ : Type_.
Proof.
intros H. induction H.
- depelim i.
- depelim i ; simp lookup_context ; simp_subst.
  + change Type_ with (thin (@tshift s x) Type_).
    eapply typing_thin ; eauto. apply typing_tshift. constructor ; auto.
  + change Type_ with (thin (@tshift s x) Type_).
    eapply typing_thin ; eauto. apply typing_tshift. constructor ; auto.
Qed.

(** In a typing derivation, we can change the context to a convertible one
    so long as the new context is well-typed. *)
Lemma typing_cconv {Σ s} (Γ Γ' : context ∅ s) t T (HΣ : typing_evar_map Σ)  :
  cconv red_flags_all Σ Γ Γ' ->
  ctyping Σ Γ' ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ' ⊢ t : T.
Proof.
intros Hconv HΓ Ht. depind Ht.
- now apply typing_type.
- subst. apply typing_conv_type with (lookup_context i Γ').
  + apply typing_var ; auto.
  + now rewrite Hconv.
  + depind Hconv ; depelim i.
    * simp lookup_context. simp_subst. depelim H0. destruct H1 as (H1 & H2).
      specialize (H2 Γ' Hconv). change Type_ with (@thin s (s ▷ x) tshift Type_).
      eapply typing_thin ; [eapply H2 | eapply typing_tshift] ; try assumption.
      now depelim HΓ.
    * simp lookup_context. simp_subst. depelim H0. destruct H1 as (H1 & H2).
      specialize (H2 Γ' Hconv). change Type_ with (@thin s (s ▷ x) tshift Type_).
      eapply typing_thin ; [| eapply typing_tshift] ; try assumption.
      apply IHHconv ; auto. now depelim HΓ.
- apply typing_lam ; [apply IHHt1 | apply IHHt2] ; auto.
  + now rewrite Hconv.
  + constructor ; auto.
- apply typing_prod ; [apply IHHt1 | apply IHHt2] ; auto.
  + now rewrite Hconv.
  + constructor ; auto.
- apply typing_app with A ; [apply IHHt1 | apply IHHt2] ; auto.
- apply typing_evar with entry ; auto.
- apply typing_conv_type with A ; auto.
Qed.

Lemma well_typed_cconv flags {Σ s} (Γ Γ' : context ∅ s) t (HΣ : typing_evar_map Σ) :
  cconv flags Σ Γ Γ' ->
  ctyping Σ Γ' ->
  well_typed Σ Γ t ->
  well_typed Σ Γ' t.
Proof.
intros Hconv Htyp (T & Ht). exists T. eapply typing_cconv ; eauto.
now rewrite red_flags_incl_all in Hconv.
Qed.

(***********************************************************************)
(** * Validity lemma *)
(***********************************************************************)

(** The validity lemma for typing states that in any typing derivation,
    the type is well-typed. *)
Lemma typing_validity {Σ s} Γ (t T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : Type_.
Proof.
intros HΣ H. depind H.
- constructor. revert H. apply All_context_consequence. firstorder.
- subst. apply typing_lookup_context. revert H.
  apply All_context_consequence. firstorder.
- constructor ; auto.
- constructor. eapply typing_context_validity ; eauto.
- change Type_ with (Type_[x ::= arg]). eapply typing_substitute.
  + apply typing_prod_inv in IHtyping1. eapply IHtyping1.
  + apply typing_scons.
    * firstorder.
    * simp_subst. assumption.
    * apply typing_sid. eapply typing_context_validity ; eauto.
- simp_subst. change Type_ with (@thin ∅ s wk_idx Type_). eapply typing_thin.
  + apply typing_evar_type. now apply (HΣ ev).
  + constructor.
    * constructor.
    * revert H. apply All_context_consequence. firstorder.
    * intros i. depelim i.
- assumption.
Qed.

(***********************************************************************)
(** * Uniqueness of types *)
(***********************************************************************)

(** Types are unique (up to convertibility). This lemma will no longer be true
    once we add subtyping (with universes). *)
Lemma typing_unique_type {Σ s} Γ (t A A' : term s) :
  Σ ;; Γ ⊢ t : A ->
  Σ ;; Γ ⊢ t : A' ->
  Σ ⊢ A ≡ A'.
Proof.
intros HA. revert A'. induction HA ; intros A' HA'.
- apply typing_type_inv in HA'. now symmetry.
- subst. apply typing_var_inv in HA'. now symmetry.
- apply typing_lam_inv in HA'. destruct HA' as (body_ty' & HA' & Hty & Hbody).
  rewrite HA'. f_equiv. apply IHHA2. assumption.
- apply typing_prod_inv in HA'. now symmetry.
- apply typing_app_inv in HA'. destruct HA' as (x' & A'' & B'' & Hf' & Harg' & Hconv).
  change_tag x' with x. rewrite Hconv.
  apply IHHA1 in Hf'. inv_conv in Hf'. destruct Hf' as (HA & HB).
  rewrite HB. reflexivity.
- apply typing_evar_inv in HA'. destruct HA' as (entry' & Hentry & HA').
  rewrite H0 in Hentry. depelim Hentry. now symmetry.
- rewrite <-H. now apply IHHA1.
Qed.

(***********************************************************************)
(** * More miscellaneous lemmas *)
(***********************************************************************)

(*Lemma typing_lam_inv' Σ {s x} (Γ : context ∅ s) (ty : term s) body body_ty :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ Lam x ty body : Prod x ty body_ty ->
  Σ ;; Cons Γ x ty ⊢ body : body_ty.
Proof.
intros HΣ H. pose proof (H' := H). apply typing_validity in H' ; [| assumption].
inv_typing in H'. destruct H' as (_ & Hbody_ty).
inv_typing in H. destruct H as (body_ty' & Hconv & Hty & Hbody).
inv_conv in Hconv. destruct Hconv as (_ & Hconv).
apply typing_conv_type with body_ty'.
- assumption.
- now symmetry.
- assumption.
Qed.*)