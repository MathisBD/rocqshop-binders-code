(** This module proves the subject reduction (aka preservation) lemma:
    reducing a well-typed term doesn't change its type.

    We also prove inversion lemmas for typing derivations of the
    form [Σ ;; Γ ⊢ thin δ t : T], which are a consequence of subject reduction.
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Typing.BasicProperties.

(***********************************************************************)
(** * Technical meat of the proof *)
(***********************************************************************)

Section SubjectReduction.
Context (Σ : evar_map) (HΣ : typing_evar_map Σ).

(** [sr_prop Γ t T] means that reducing either [Γ] or [t] produces
    a valid typing judgement [Γ' ⊢ t' : T].

    Our goal is to show that [Γ ⊢ t : T] implies [sr_prop Γ t T]. *)
Definition sr_prop {s} Γ (t T : term s) :=
  (forall t', Σ ⊢ t ~> t' -> Σ ;; Γ ⊢ t' : T) /\
  (forall Γ', cred1 red_flags_all Σ Γ Γ' -> Σ ;; Γ' ⊢ t : T).

Lemma ctyping_red1 {s} (Γ Γ' : context ∅ s) :
  All_context (@sr_prop) Γ ->
  cred1 red_flags_all Σ Γ Γ' ->
  ctyping Σ Γ ->
  ctyping Σ Γ'.
Proof.
intros Hsr Hred HΓ. depind Hred.
- constructor.
  + now depelim HΓ.
  + depelim HΓ. depelim Hsr. now apply H.
- constructor.
  + eapply IHHred.
    * now depelim Hsr.
    * now depelim HΓ.
  + depelim Hsr. apply H ; auto.
Qed.

Lemma typing_lookup_context_red1 {s} (Γ Γ' : context ∅ s) i :
  All_context (@sr_prop) Γ ->
  ctyping Σ Γ ->
  cred1 red_flags_all Σ Γ Γ' ->
  Σ ;; Γ' ⊢ lookup_context i Γ : Type_.
Proof.
intros Hsr HΓ Hred. depind Hred.
- depelim Hsr. depelim HΓ. depelim i ; simp lookup_context ; simp_subst.
  + change Type_ with (thin (@tshift s x) Type_). apply typing_thin with Γ ; auto.
    apply typing_tshift. constructor ; auto. now apply H.
  + change Type_ with (thin (@tshift s x) Type_). apply typing_thin with Γ.
    * now apply typing_lookup_context.
    * apply typing_tshift. constructor ; auto. now apply H.
- depelim Hsr. depelim HΓ. depelim i ; simp lookup_context ; simp_subst.
  + change Type_ with (thin (@tshift s x) Type_). apply typing_thin with Γ' ; auto.
    * now apply H.
    * apply typing_tshift. constructor ; auto.
      --eapply ctyping_red1 ; eauto.
      --now apply H.
  + change Type_ with (thin (@tshift s x) Type_). apply typing_thin with Γ' ; auto.
    eapply typing_tshift. constructor ; auto.
    * eapply ctyping_red1 with (Γ := Γ) ; auto.
    * now apply H.
Qed.

(** Typing is preserved by beta reduction. *)
Lemma typing_beta {s} Γ x ty body arg (T : term s) :
  Σ ;; Γ ⊢ App (Lam x ty body) arg : T ->
  Σ ;; Γ ⊢ body[x ::= arg] : T.
Proof.
intros H. pose proof (HT := typing_validity _ _ _ HΣ H).
inv_typing in H. destruct H as (y & A & B & Hf & Harg & Hconv).
change_tag y with x.
apply typing_conv_type with (B[x ::= arg]) ; try easy.
clear T Hconv HT.

pose proof (HAB := typing_validity _ _ _ HΣ Hf).
inv_typing in HAB. destruct HAB as (HA & HB).

inv_typing in Hf. destruct Hf as (body_ty & Hconv & Hty & Hbody).
inv_conv in Hconv. destruct Hconv as (Hconv1 & Hconv2).

assert (H : Σ ;; Γ ⊢ body[x ::= arg] : body_ty[x ::= arg]).
{
  apply typing_substitute with (Cons Γ x ty) ; [assumption|].
  apply typing_scons.
  - assumption.
  - simp_subst. apply typing_conv_type with A ; auto.
  - apply typing_sid. eapply typing_context_validity ; eauto.
}

apply typing_conv_type with (body_ty[x ::= arg]).
- assumption.
- now rewrite Hconv2.
- change Type_ with (Type_[x ::= arg]). eapply typing_substitute with (Cons Γ x A).
  + assumption.
  + apply typing_scons ; simp_subst ; try assumption.
    apply typing_sid. eapply typing_context_validity ; eauto.
Qed.

Lemma sr_prop_type {s} (Γ : context ∅ s) :
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ Type_ Type_.
Proof.
intros HΓ HΓ'. split.
- intros t' Hred. depelim Hred.
- intros Γ' Hred. constructor. eapply ctyping_red1 with (Γ := Γ) ; auto.
Qed.

Lemma sr_prop_var {s} (Γ : context ∅ s) i :
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ (Var i) (lookup_context i Γ).
Proof.
intros HΓ HΓ'. split.
- intros t' Hred. depelim Hred.
- intros Γ' Hred. apply typing_conv_type with (lookup_context i Γ').
  + constructor ; auto. now eapply ctyping_red1 with (Γ := Γ).
  + apply lookup_context_cconv. symmetry. now apply cconv_of_cred1.
  + eapply typing_lookup_context_red1 ; eauto.
Qed.

Lemma sr_prop_lam {x s} (Γ : context ∅ s) ty body body_ty :
  Σ ;; Γ ⊢ ty : Type_ -> sr_prop Γ ty Type_ ->
  Σ ;; Cons Γ x ty ⊢ body : body_ty -> sr_prop (Cons Γ x ty) body body_ty ->
  sr_prop Γ (Lam x ty body) (Prod x ty body_ty).
Proof.
intros Hty Hty' Hbody Hbody'. split.
- intros t' Hred. depelim Hred.
  + apply typing_conv_type with (Prod x ty' body_ty).
    * constructor.
      --now apply Hty'.
      --apply Hbody' ; auto. now constructor.
    * now rewrite Hred.
    * constructor ; auto. eapply typing_validity ; eauto.
  + constructor ; auto. apply Hbody' ; auto.
- constructor.
  + now apply Hty'.
  + apply Hbody' ; auto. now constructor.
Qed.

Lemma sr_prop_prod {x s} (Γ : context ∅ s) a b :
  Σ ;; Γ ⊢ a : Type_ -> sr_prop Γ a Type_ ->
  Σ ;; Cons Γ x a ⊢ b : Type_ -> sr_prop (Cons Γ x a) b Type_ ->
  sr_prop Γ (Prod x a b) Type_.
Proof.
intros Ha Ha' Hb Hb'. split.
- intros t' Hred. depelim Hred.
  + constructor.
    * now apply Ha'.
    * apply Hb'. now constructor.
  + constructor ; auto. apply Hb' ; auto.
- intros Γ' Hred. constructor.
  + now apply Ha'.
  + apply Hb'. now constructor.
Qed.

Lemma sr_prop_app {s} (Γ : context ∅ s) f arg x A B :
  Σ ;; Γ ⊢ f : Prod x A B -> sr_prop Γ f (Prod x A B) ->
  Σ ;; Γ ⊢ arg : A -> sr_prop Γ arg A ->
  sr_prop Γ (App f arg) (B[x ::= arg]).
Proof.
intros Hf Hf' Harg Harg'.
split.
- intros t' Hred. depelim Hred.
  + change_tag x0 with x. apply typing_beta with ty ; try assumption.
    apply typing_app with A ; assumption.
  + apply typing_app with A ; try assumption. now apply Hf'.
  + apply typing_conv_type with (B[x ::= arg']).
    * apply typing_app with A ; try assumption. now apply Harg'.
    * now rewrite Hred.
    * apply typing_validity, typing_prod_inv in Hf ; [| assumption].
      destruct Hf as (_ & HA & HB).
      change Type_ with (Type_[x ::= arg]). eapply typing_substitute ; try eassumption.
      eapply typing_scons ; simp_subst ; eauto. apply typing_sid.
      now apply typing_context_validity in Harg.
- intros Γ' Hred. apply typing_app with A.
  + now apply Hf'.
  + now apply Harg'.
Qed.

Lemma sr_prop_evar {s} (Γ : context ∅ s) ev entry :
  Σ !! ev = Some entry ->
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ (Evar ev) (wk entry.(evar_type)).
Proof.
intros Hev HΓ HΓ'. split.
- intros t' Hred. depelim Hred. rewrite H in Hev. depelim Hev. cbn.
  simp_subst. eapply typing_thin.
  + apply HΣ in H. depelim H. eassumption.
  + constructor ; try easy. constructor.
- intros Γ' Hred. econstructor ; eauto. now eapply ctyping_red1 with (Γ := Γ).
Qed.

Lemma sr_prop_conv_type {s} Γ (t A B : term s) :
  Σ ;; Γ ⊢ t : A -> sr_prop Γ t A ->
  Σ ;; Γ ⊢ B : Type_ -> sr_prop Γ B Type_ ->
  Σ ⊢ A ≡ B ->
  sr_prop Γ t B.
Proof.
intros Ht Ht' HB HB' Hconv. split.
- intros t' Hred. apply typing_conv_type with A ; auto. now apply Ht'.
- intros Γ' Hred. apply typing_conv_type with A ; auto.
  + now apply Ht'.
  + now apply HB'.
Qed.

(** [typing] implies [sr_prop]. *)
Lemma sr_prop_all {s} Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  sr_prop Γ t T.
Proof.
intros Ht. depind Ht.
- apply All_context_and in H. destruct H as (H1 & H2). now apply sr_prop_type.
- apply All_context_and in H. subst. destruct H as (H1 & H2). now apply sr_prop_var.
- now apply sr_prop_lam.
- now apply sr_prop_prod.
- now apply sr_prop_app with A.
- apply All_context_and in H. destruct H as (H1 & H2). now apply sr_prop_evar.
- now apply sr_prop_conv_type with A.
Qed.

End SubjectReduction.

(***********************************************************************)
(** * Compatibility of typing with one-step reduction *)
(***********************************************************************)

Section TypingRed1.
  Context {s : scope} {flags : red_flags} {Σ : evar_map}.
  Hypothesis (HΣ : typing_evar_map Σ).

  (** One reduction step in the context preserves the typing derivation. *)
  Lemma typing_red1_context :
    Proper (cred1 flags Σ ==> eq ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' <- T T' <- Htyp.
  pose proof (H := sr_prop_all Σ HΣ Γ t T Htyp). apply H.
  now rewrite red_flags_incl_all in HΓ.
  Qed.

  (** One reduction step in the term preserves the typing derivation. *)
  Lemma typing_red1_term :
    Proper (eq ==> red1 flags Σ ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' Ht T T' <- Htyp.
  pose proof (H := sr_prop_all Σ HΣ Γ t T Htyp). apply H.
  now rewrite red_flags_incl_all in Ht.
  Qed.

  (** One reduction step in the type preserves the typing derivation. *)
  Lemma typing_red1_type :
    Proper (eq ==> eq ==> red1 flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' <- T T' HT Htyp.
  apply typing_conv_type with T.
  - assumption.
  - rewrite red_flags_incl_all in HT. now rewrite HT.
  - eapply typing_red1_term ; eauto. now apply typing_validity in Htyp.
  Qed.

End TypingRed1.

(***********************************************************************)
(** * Compatibility of typing with multi-step reduction *)
(***********************************************************************)

Section TypingRed.
  Context {s : scope} {flags : red_flags} {Σ : evar_map}.
  Hypothesis (HΣ : typing_evar_map Σ).

  Lemma typing_red_context :
    Proper (cred flags Σ ==> eq ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' <- T T' <- Htyp. induction HΓ using cred_ind_alt.
  - assumption.
  - eapply typing_red1_context ; eauto.
  Qed.

  Lemma typing_red_term :
    Proper (eq ==> red flags Σ ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' Ht T T' <- Htyp. induction Ht.
  - assumption.
  - eapply typing_red1_term ; eauto.
  Qed.

  Lemma typing_red_type :
    Proper (eq ==> eq ==> red flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' <- T T' HT Htyp. induction HT.
  - assumption.
  - eapply typing_red1_type ; eauto.
  Qed.

  (** Reduction in the context, term, and type preserves the typing derivation. *)
  #[export] Instance typing_red :
    Proper (cred flags Σ ==> red flags Σ ==> red flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' Ht T T' HT Htyp.
  enough (Σ ;; Γ ⊢ t' : T'). { revert H. apply typing_red_context ; auto. }
  enough (Σ ;; Γ ⊢ t : T'). { revert H. apply typing_red_term ; auto. }
  enough (Σ ;; Γ ⊢ t : T). { revert H. apply typing_red_type ; auto. }
  assumption.
  Qed.

  (** Reduction in the context or term preserves the typing derivation. *)
  #[export] Instance well_typed_red :
    Proper (cred flags Σ ==> red flags Σ ==> impl) (@well_typed Σ s).
  Proof.
  intros Γ Γ' HΓ t t' Ht (T & HT). exists T. now rewrite <-Ht, <-HΓ.
  Qed.

End TypingRed.

(***********************************************************************)
(** * Inversion lemmas for typing derivations on thinnings *)
(***********************************************************************)

(** It is surprisingly difficult to prove inversion lemmas for typing derivations
    of the form [Σ ;; Γ ⊢ thin δ t : T]. I proved the results below using
    subject reduction and validity of typing, which seems a bit overkill... *)

(** Helper lemma for [typing_thicken]. *)
Lemma typing_thicken_aux {s'} Σ Δ (t' T' : term s') (HΣ : typing_evar_map Σ) :
  Σ ;; Δ ⊢ t' : T' ->
  forall s Γ (δ : thinning s s') t,
    thin δ t = t' ->
    ttyping Σ Γ δ Δ ->
    exists T, Σ ⊢ T' ~~> thin δ T /\ Σ ;; Γ ⊢ t : T.
Proof.
intros Htyp s Γ δ t Ht Hδ. induction Htyp in s, Γ, δ, t, Ht, Hδ |- *.
- apply thin_type_inv in Ht. subst. exists Type_. simp_subst.
  split ; [reflexivity | constructor]. apply Hδ.
- subst. apply thin_var_inv in Ht. destruct Ht as (i' & -> & <-).
  exists (lookup_context i' Γ). split.
  + now rewrite (ttyping_prop Hδ).
  + constructor ; [apply Hδ | reflexivity].
- apply thin_lam_inv in Ht. destruct Ht as (ty0 & body0 & -> & <- & <-).
  destruct (IHHtyp1 _ _ _ _ eq_refl Hδ) as (T & HT & Hty).
  apply red_type_inv in HT. apply thin_type_inv in HT. subst.
  specialize (IHHtyp2 _ (Cons Γ x ty0) (ThinKeep x δ) _ eq_refl).
  forward IHHtyp2. { apply typing_ThinKeep ; auto. }
  destruct IHHtyp2 as (body_ty0 & Hred & Hbody).
  exists (Prod x ty0 body_ty0). split.
  + simp_subst. f_equiv. assumption.
  + constructor ; auto.
- apply thin_prod_inv in Ht. destruct Ht as (a0 & b0 & -> & <- & <-).
  destruct (IHHtyp1 _ _ _ _ eq_refl Hδ) as (T & HT & Ha).
  apply red_type_inv in HT. apply thin_type_inv in HT. subst.
  specialize (IHHtyp2 _ (Cons Γ x a0) (ThinKeep x δ) _ eq_refl).
  forward IHHtyp2. { apply typing_ThinKeep ; auto. }
  destruct IHHtyp2 as (T & HT & Hb). apply red_type_inv, thin_type_inv in HT. subst.
  exists Type_. split.
  + now simp_subst.
  + constructor ; auto.
- apply thin_app_inv in Ht. destruct Ht as (f0 & arg0 & -> & <- & <-).
  destruct (IHHtyp1 _ _ _ _ eq_refl Hδ) as (T & HT & Hf).
  destruct (IHHtyp2 _ _ _ _ eq_refl Hδ) as (T' & Hred & Harg).
  inv_red in HT. destruct HT as (a' & b' & HT & HA & HB).
  apply thin_prod_inv in HT. destruct HT as (a & b & -> & <- & <-).
  exists (b[x ::= arg0]). split.
  + rewrite HB. now nf_subst.
  + apply typing_app with a ; auto. apply typing_conv_type with T'.
    * assumption.
    * apply conv_thicken' with δ. rewrite <-HA, <-Hred. reflexivity.
    * apply typing_validity in Hf ; [| assumption]. apply typing_prod_inv in Hf.
      now apply Hf.
- apply thin_evar_inv in Ht. subst. exists (wk (evar_type entry)). split.
  + now simp_subst.
  + apply typing_evar with entry ; auto. apply Hδ.
- subst. destruct (IHHtyp1 _ _ _ _ eq_refl Hδ) as (A' & HA & Ht).
  rewrite HA in H. apply church_rosser in H. destruct H as (C & H1 & H2).
  apply red_thicken in H1. destruct H1 as (B' & -> & Hred).
  exists B'. split ; [assumption |]. apply typing_conv_type with A'.
  + assumption.
  + now rewrite Hred.
  + apply typing_validity in Ht ; [| assumption].
    eapply typing_red_term ; eauto.
Qed.

(** Inversion lemma for a typing derivation where the term is a thinning. *)
Lemma typing_thicken Σ {s s'} (δ : thinning s s') Γ Δ t T' (HΣ : typing_evar_map Σ) :
  Σ ;; Δ ⊢ thin δ t : T' ->
  ttyping Σ Γ δ Δ ->
  exists T,
    Σ ⊢ T' ~~> thin δ T /\
    Σ ;; Γ ⊢ t : T.
Proof.
intros Htyp Hδ. eapply typing_thicken_aux in Htyp ; eauto.
Qed.

(** Inversion lemma for a typing derivation where the term and type are thinnings. *)
Lemma typing_thicken' Σ {s s'} (δ : thinning s s') Γ Δ t T (HΣ : typing_evar_map Σ) :
  Σ ;; Δ ⊢ thin δ t : thin δ T ->
  ttyping Σ Γ δ Δ ->
  Σ ;; Γ ⊢ t : T.
Proof.
intros Ht Hδ.
assert (HT : Σ ;; Γ ⊢ T : Type_).
{
  apply typing_validity in Ht ; [| assumption]. eapply typing_thicken in Ht ; eauto.
  destruct Ht as (T' & Hred & HT). apply red_type_inv, thin_type_inv in Hred.
  subst. assumption.
}
eapply typing_thicken in Ht ; eauto.
destruct Ht as (U & Hred & Htyp). apply red_thicken' in Hred.
apply typing_conv_type with U.
- assumption.
- now rewrite Hred.
- assumption.
Qed.

(** If a thinning is well-typed, so is the original term. *)
Lemma well_typed_thicken Σ {s s'} (δ : thinning s s') Γ Δ t (HΣ : typing_evar_map Σ) :
  well_typed Σ Δ (thin δ t) ->
  ttyping Σ Γ δ Δ ->
  well_typed Σ Γ t.
Proof.
intros [T H] Hδ. apply typing_thicken with (Γ := Γ) in H.
- firstorder.
- assumption.
- assumption.
Qed.
