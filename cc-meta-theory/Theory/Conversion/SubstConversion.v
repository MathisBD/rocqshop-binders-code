(** This module defines a conversion relation on substitutions
    and proves basic properties, notably:
    - The Chuch-Rosser lemma for substitutions.
    - Compatibility of thinning and substition with conversion.
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Conversion.TermConversion.

(***********************************************************************)
(** * Conversion relation on substitutions *)
(***********************************************************************)

Record sconv (flags : red_flags) (Σ : evar_map) {s s'} (σ σ' : subst s s') : Prop := {
  sconv_prop : forall i, Σ ⊢ sapply σ i ≡{flags} sapply σ' i
}.

#[export] Instance conv_sapply flags Σ s s' :
  Proper (sconv flags Σ ==> eq ==> conv flags Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

Section Instances.
  Context {flags : red_flags} {Σ : evar_map} {s s' : scope}.

  #[export] Instance sconv_Reflexive :
    Reflexive (@sconv flags Σ s s').
  Proof. intros σ. constructor. reflexivity. Qed.

  #[export] Instance sconv_Symmetric :
    Symmetric (@sconv flags Σ s s').
  Proof. intros σ σ' [Hσ]. constructor. intros i. now symmetry. Qed.

  #[export] Instance sconv_Transitive :
    Transitive (@sconv flags Σ s s').
  Proof.
  intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
  Qed.

  #[export] Instance sconv_of_sred :
    subrelation (@sred flags Σ s s') (@sconv flags Σ s s').
  Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

  #[export] Instance sconv_of_sred_flip :
    subrelation (Basics.flip (@sred flags Σ s s')) (@sconv flags Σ s s').
  Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

End Instances.

#[export] Instance sconv_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s s', eq ==> eq ==> impl) (@sconv).
Proof.
intros f f' Hf Σ Σ' HΣ s s' σ ? <- σ' ? <- H. constructor. intros i.
rewrite <-Hf, <-HΣ. apply H.
Qed.

(***********************************************************************)
(** * Church-Rosser lemma *)
(***********************************************************************)

(** Because a substitution is a finite collection of terms, the Church-Rosser
    property for substitutions follows from the Church-Rosser property for terms. *)
Lemma church_rosser_subst {s s' flags Σ} (σ σ' : subst s s') :
  sconv flags Σ σ σ' ->
  exists τ, sred flags Σ σ τ /\ sred flags Σ σ' τ.
Proof.
revert s' σ σ'. induction s.
- intros s' σ σ' Hσ.
  exists (subst_of_thin wk_idx). split ; constructor ; intros i ; depelim i.
- intros s' σ σ' Hσ.
  specialize (IHs s' (tscomp tshift σ) (tscomp tshift σ')).
  forward IHs. { constructor. intros i. simp_subst. now rewrite Hσ. }
  destruct IHs as (τ & H1 & H2).
  assert (exists t,
    Σ ⊢ sapply σ I0 ~~>{flags} t /\
    Σ ⊢ sapply σ' I0 ~~>{flags} t) as (t & Ht1 & Ht2).
  { apply church_rosser. now rewrite Hσ. }
  exists (scons x t τ). split.
  + constructor. intros i. depelim i ; simp_subst.
    * exact Ht1.
    * destruct H1 as [H1]. specialize (H1 i). simp_subst in H1. exact H1.
  + constructor. intros i. depelim i ; simp_subst.
    * exact Ht2.
    * destruct H2 as [H2]. specialize (H2 i). simp_subst in H2. exact H2.
Qed.

(***********************************************************************)
(** * Compatibility of conversion with thinning and substitution *)
(***********************************************************************)

Section Substitutivity.
  Context {s s' s'' : scope} {x : tag} {flags : red_flags} {Σ : evar_map}.

  #[export] Instance conv_thin (δ : thinning s s') :
    Proper (conv flags Σ ==> conv flags Σ) (thin δ).
  Proof.
  intros t t' H. apply church_rosser in H. destruct H as (u & H1 & H2).
  now rewrite H1, H2.
  Qed.

  (** Inversion lemma for conversion between two thinnings. *)
  Lemma conv_thicken' (δ : thinning s s') (t u : term s) :
    Σ ⊢ thin δ t ≡{flags} thin δ u ->
    Σ ⊢ t ≡{flags} u.
  Proof.
  intros H. apply church_rosser in H. destruct H as (v & H1 & H2).
  apply red_thicken in H1, H2. destruct H1 as (t' & -> & ->).
  destruct H2 as (? & Heq & ->). apply thin_inj in Heq. now subst.
  Qed.

  #[export] Instance conv_substitute :
    Proper (sconv flags Σ ==> conv flags Σ ==> conv flags Σ) (@substitute s s').
  Proof.
  intros σ σ' Hσ t t' Ht.
  apply church_rosser in Ht. destruct Ht as (u & -> & ->).
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_scons :
    Proper (conv flags Σ ==> sconv flags Σ ==> sconv flags Σ) (@scons s s' x).
  Proof.
  intros t t' Ht σ σ' Hσ. constructor. intros i.
  apply church_rosser in Ht. destruct Ht as (? & -> & ->).
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_stcomp :
    Proper (sconv flags Σ ==> eq ==> sconv flags Σ) (@stcomp s s' s'').
  Proof.
  intros σ σ' Hσ ρ ρ' <-. constructor. intros i.
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_tscomp :
    Proper (eq ==> sconv flags Σ ==> sconv flags Σ) (@tscomp s s' s'').
  Proof.
  intros ρ ρ' <- σ σ' Hσ. constructor. intros i.
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_sup :
    Proper (sconv flags Σ ==> sconv flags Σ) (@sup s s' x).
  Proof.
  intros σ σ' Hσ. apply church_rosser_subst in Hσ.
  destruct Hσ as (? & -> & ->). reflexivity.
  Qed.

  #[export] Instance conv_scomp :
    Proper (sconv flags Σ ==> sconv flags Σ ==> sconv flags Σ) (@scomp s s' s'').
  Proof.
  intros σ σ' Hσ τ τ' Hτ.
  apply church_rosser_subst in Hσ, Hτ.
  destruct Hσ as (? & -> & ->).
  destruct Hτ as (? & -> & ->).
  reflexivity.
  Qed.

End Substitutivity.
