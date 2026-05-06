(** This module defines reduction of substitutions and proves some
    basic properties, notably compatibility of reduction with
    thinning and substitution.
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Reduction.TermReduction.

(***********************************************************************)
(** * Reduction on substitutions *)
(***********************************************************************)

(** Reduction on substitutions is just pointwise reduction.

    We wrap the definition in a record because otherwise rewriting with
    [H : sred flags Σ σ σ'] will sometimes fail due to setoid rewrite
    wanting to rewrite [sapply σ i] into [sapply σ' i].  *)
Record sred flags Σ {s s'} (σ σ' : subst s s') := {
  sred_prop : forall i, Σ ⊢ sapply σ i ~~>{flags} sapply σ' i
}.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

#[export] Instance sred_Reflexive s s' flags Σ : Reflexive (@sred flags Σ s s').
Proof. intros σ. constructor. reflexivity. Qed.

#[export] Instance sred_Transitive s s' flags Σ : Transitive (@sred flags Σ s s').
Proof.
intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
Qed.

#[export] Instance red_sapply s s' flags Σ :
  Proper (sred flags Σ ==> eq ==> red flags Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

(** Extending the set of flags or the evar map preserves reductions. *)
#[export] Instance sred_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s s', eq ==> eq ==> impl) (@sred).
Proof.
intros f f' Hf Σ Σ' HΣ s s' σ σ' <- τ τ' <- [H]. constructor. intros i.
specialize (H i). rewrite Hf, HΣ in H. assumption.
Qed.

(***********************************************************************)
(** * Compatibility of reduction with thinnings *)
(***********************************************************************)

(** Compatibility of thinning with [red1]. *)
#[export] Instance red1_thin {s s' flags Σ} (δ : thinning s s') :
  Proper (red1 flags Σ ==> red1 flags Σ) (thin δ).
Proof.
intros t t' H. induction H in s', δ |- * ; simp_subst.
- apply red1_beta_alt ; auto. nf_subst. reflexivity.
- eapply red1_evar_expand ; auto. eassumption.
- now apply red1_lam_l.
- now apply red1_lam_r.
- now apply red1_prod_l.
- now apply red1_prod_r.
- now apply red1_app_l.
- now apply red1_app_r.
Qed.

(** Compatibility of thinning with [red]. *)
#[export] Instance red_thin {s s' flags Σ} (δ : thinning s s') :
  Proper (red flags Σ ==> red flags Σ) (thin δ).
Proof.
intros t t' H. induction H.
- reflexivity.
- now rewrite IHred, H0.
Qed.

(** Because thinnings are injective, reduction commutes with thinning.
    This commutation is expressed via inversion lemmas in the following. *)

(** Helper lemma for [red1_thicken]. *)
Lemma red1_thicken_aux Σ flags {s'} (t' u' : term s') :
  Σ ⊢ t' ~>{flags} u' ->
  forall s δ (t : term s),
    thin δ t = t' ->
    exists u, thin δ u = u' /\ Σ ⊢ t ~>{flags} u.
Proof.
intros H. depind H ; intros s' δ t Ht.
- apply thin_app_inv in Ht. destruct Ht as (f & arg0 & -> & Hf & <-).
  apply thin_lam_inv in Hf. destruct Hf as (ty0 & body0 & -> & <- & <-).
  exists (body0[x ::= arg0]). split ; [now nf_subst |]. now apply red1_beta.
- apply thin_evar_inv in Ht. subst. exists (wk def).
  split ; [now nf_subst |]. eapply red1_evar_expand ; eassumption.
- apply thin_lam_inv in Ht. destruct Ht as (ty0 & body0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (ty & <- & Hred).
  exists (Lam x ty body0). split ; [now nf_subst |].
  now apply red1_lam_l.
- apply thin_lam_inv in Ht. destruct Ht as (ty0 & body0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (body & <- & Hred).
  exists (Lam x ty0 body). split ; [now nf_subst |].
  now apply red1_lam_r.
- apply thin_prod_inv in Ht. destruct Ht as (a0 & b0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (a & <- & Hred).
  exists (Prod x a b0). split ; [now nf_subst |].
  now apply red1_prod_l.
- apply thin_prod_inv in Ht. destruct Ht as (a0 & b0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (b & <- & Hred).
  exists (Prod x a0 b). split ; [now nf_subst |].
  now apply red1_prod_r.
- apply thin_app_inv in Ht. destruct Ht as (f0 & arg0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (f & <- & Hred).
  exists (App f arg0). split ; [now nf_subst |].
  now apply red1_app_l.
- apply thin_app_inv in Ht. destruct Ht as (f0 & arg0 & -> & <- & <-).
  specialize (IHred1 _ _ _ eq_refl). destruct IHred1 as (arg & <- & Hred).
  exists (App f0 arg). split ; [now nf_subst |].
  now apply red1_app_r.
Qed.

(** Inversion lemma for [red1] starting from a thinning. *)
Lemma red1_thicken Σ flags {s s'} (δ : thinning s s') t u' :
  Σ ⊢ thin δ t ~>{flags} u' ->
  exists u,
    u' = thin δ u /\
    Σ ⊢ t ~>{flags} u.
Proof.
intros H. eapply red1_thicken_aux in H ; eauto.
destruct H as (u & <- & Hred). exists u. now split.
Qed.

(** Inversion lemma for [red] from a thinning. *)
Lemma red_thicken Σ flags {s s'} (δ : thinning s s') t u' :
  Σ ⊢ thin δ t ~~>{flags} u' ->
  exists u,
    u' = thin δ u /\
    Σ ⊢ t ~~>{flags} u.
Proof.
intros H. depind H.
- exists t0 ; split ; reflexivity.
- destruct IHred as (u2 & -> & Hred). apply red1_thicken in H0.
  destruct H0 as (u3 & -> & Hred'). exists u3.
  split ; [reflexivity |]. rewrite Hred, Hred'. reflexivity.
Qed.

(** Inversion lemma for [red1] between two thinnings. *)
Lemma red1_thicken' Σ flags {s s'} (δ : thinning s s') t u :
  Σ ⊢ thin δ t ~>{flags} thin δ u ->
  Σ ⊢ t ~>{flags} u.
Proof.
intros H. apply red1_thicken in H. destruct H as (u' & H1 & H2).
apply thin_inj in H1. now subst.
Qed.

(** Inversion lemma for [red] between two thinnings. *)
Lemma red_thicken' Σ flags {s s'} (δ : thinning s s') t u :
  Σ ⊢ thin δ t ~~>{flags} thin δ u ->
  Σ ⊢ t ~~>{flags} u.
Proof.
intros H. apply red_thicken in H. destruct H as (u' & H1 & H2).
apply thin_inj in H1. now subst.
Qed.

(***********************************************************************)
(** * Compatibility of reduction with substitutions *)
(***********************************************************************)

#[export] Instance red_scons {s s' x flags Σ} :
  Proper (red flags Σ ==> sred flags Σ ==> sred flags Σ) (@scons s s' x).
Proof.
intros t t' Ht σ σ' Hσ. constructor. intros i. depelim i ; simp_subst.
- assumption.
- now rewrite Hσ.
Qed.

#[export] Instance red_stcomp {s s' s'' flags Σ} :
  Proper (sred flags Σ ==> eq ==> sred flags Σ) (@stcomp s s' s'').
Proof.
intros σ σ' Hσ ρ ρ' <-. constructor. intros i. simp_subst.
now rewrite Hσ.
Qed.

#[export] Instance red_tscomp {s s' s'' flags Σ} ρ :
  Proper (sred flags Σ ==> sred flags Σ) (@tscomp s s' s'' ρ).
Proof.
intros σ σ' Hσ. constructor. intros i. simp_subst.
now rewrite Hσ.
Qed.

#[export] Instance red_sup {s s' x flags Σ} :
  Proper (sred flags Σ ==> sred flags Σ) (@sup s s' x).
Proof. intros σ σ' Hσ. unfold sup. now rewrite Hσ. Qed.

(** Compatibility of substitution with [red1]. *)
#[export] Instance red1_substitute_l {s s' Σ flags} (σ : subst s s') :
  Proper (red1 flags Σ ==> red1 flags Σ) (substitute σ).
Proof.
intros t t' H. induction H in s', σ |- * ; simp_subst.
- cbn. apply red1_beta_alt ; [assumption|]. f_equal. now simp_subst.
- eapply red1_evar_expand. eassumption.
- now apply red1_lam_l.
- now apply red1_lam_r.
- now apply red1_prod_l.
- now apply red1_prod_r.
- now apply red1_app_l.
- now apply red1_app_r.
Qed.

(** Substitution lemma for [red]. *)
#[export] Instance red_substitute {s s' flags Σ} :
  Proper (sred flags Σ ==> red flags Σ ==> red flags Σ) (@substitute s s').
Proof.
intros σ σ' Hσ t t' H. transitivity (substitute σ' t).
- clear t' H. induction t in s', σ, σ', Hσ |- * ; simp_subst.
  + reflexivity.
  + now rewrite Hσ.
  + f_equiv.
    * now apply IHt1.
    * apply IHt2. now f_equiv.
  + f_equiv.
    * now apply IHt1.
    * apply IHt2. now f_equiv.
  + f_equiv.
    * now apply IHt1.
    * now apply IHt2.
  + reflexivity.
- induction H.
  + reflexivity.
  + now rewrite IHred, H0.
Qed.

#[export] Instance red_scomp {s s' s'' flags Σ} :
  Proper (sred flags Σ ==> sred flags Σ ==> sred flags Σ) (@scomp s s' s'').
Proof.
intros σ σ' Hσ τ τ' Hτ. constructor. intros i. simp_subst.
now rewrite Hτ, Hσ.
Qed.
