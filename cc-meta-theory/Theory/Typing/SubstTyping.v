(** This module defines the typing relation for renamings, thinnings,
    and substitutions. We also prove the compatibility of typing with
    thinnings and substitutions. *)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Typing.EvarMapTyping.

(***********************************************************************)
(** * Typing thinnings *)
(***********************************************************************)

(** [δ] is a well-typed thinning from context [Γ] to context [Δ] if:
    - [Γ] is well-typed.
    - [Δ] is well-typed.
    - for every index [i], [δ] maps the [i]-th type in [Γ] to the
      [ρ i]-th type in [Δ]. *)
Record ttyping (Σ : evar_map) {s s'} (Γ : context ∅ s) (δ : thinning s s')
(Δ : context ∅ s') : Prop := {
  ttyping_dom : ctyping Σ Γ ;
  ttyping_codom : ctyping Σ Δ ;
  ttyping_prop : forall i,
    thin δ (lookup_context i Γ) = lookup_context (tapply δ i) Δ
}.

Arguments ttyping_dom {Σ s s' Γ δ Δ}.
Arguments ttyping_codom {Σ s s' Γ δ Δ}.
Arguments ttyping_prop {Σ s s' Γ δ Δ}.

#[export] Instance ttyping_extend_evm :
  Proper (Vevm_incl ==> ∀ s s', eq ==> eq ==> eq ==> impl) (@ttyping).
Proof.
intros Σ Σ' HΣ s s' Γ ? <- δ ? <- Δ ? <- H. constructor.
- apply (ctyping_extend_evm HΣ). apply H.
- apply (ctyping_extend_evm HΣ). apply H.
- apply H.
Qed.

(***********************************************************************)
(** * Typing substitutions *)
(***********************************************************************)

(** [δ] is a well-typed substitution from context [Γ] to context [Δ] if:
    - [Γ] is well-typed.
    - [Δ] is well-typed.
    - for every index [i], [σ i] is well-typed in [Δ], with type [Γ_i[σ]] *)
Record styping (Σ : evar_map) {s s'} (Γ : context ∅ s) (σ : subst s s')
(Δ : context ∅ s') := {
  styping_dom : ctyping Σ Γ ;
  styping_codom : ctyping Σ Δ ;
  styping_prop : forall i,
    Σ ;; Δ ⊢ sapply σ i : substitute σ (lookup_context i Γ)
}.

Arguments styping_dom {Σ s s' Γ σ Δ}.
Arguments styping_codom {Σ s s' Γ σ Δ}.
Arguments styping_prop {Σ s s' Γ σ Δ}.

#[export] Instance styping_extend_evm :
  Proper (Vevm_incl ==> ∀ s s', eq ==> eq ==> eq ==> impl) (@styping).
Proof.
intros Σ Σ' HΣ s s' Γ ? <- ρ ? <- Δ ? <- H. constructor.
- apply (ctyping_extend_evm HΣ). apply H.
- apply (ctyping_extend_evm HΣ). apply H.
- intros i. rewrite <-HΣ. apply H.
Qed.

(***********************************************************************)
(** * Compatibility of typing with thinnings *)
(***********************************************************************)

Lemma typing_ThinNil Σ (Γ : context ∅ ∅) :
  ttyping Σ Γ ThinNil Γ.
Proof.
depelim Γ. constructor.
- constructor.
- constructor.
- intros i. depelim i.
Qed.

Lemma typing_ThinKeep {s s' x} Σ Γ Δ (δ : thinning s s') ty :
  Σ ;; Γ ⊢ ty : Type_ ->
  Σ ;; Δ ⊢ thin δ ty : Type_ ->
  ttyping Σ Γ δ Δ ->
  ttyping Σ (Cons Γ x ty) (ThinKeep x δ) (Cons Δ x (thin δ ty)).
Proof.
intros H1 H2 H3. constructor.
- constructor ; auto. apply H3.
- constructor ; auto. apply H3.
- intros i. depelim i ; simp lookup_context ; simp_subst.
  + reflexivity.
  + simp lookup_context. simp_subst. rewrite <-(ttyping_prop H3). now simp_subst.
Qed.

Lemma typing_ThinSkip {s s' x} Σ Γ Δ (δ : thinning s s') ty :
  Σ ;; Δ ⊢ ty : Type_ ->
  ttyping Σ Γ δ Δ ->
  ttyping Σ Γ (ThinSkip x δ) (Cons Δ x ty).
Proof.
intros H1 H2. constructor.
- apply H2.
- constructor ; auto. apply H2.
- intros i. simp_subst. simp lookup_context. simp_subst.
  rewrite <-(ttyping_prop H2). now simp_subst.
Qed.

Lemma typing_tid {s} Σ Γ :
  ctyping Σ Γ ->
  ttyping Σ Γ (@tid s) Γ.
Proof.
intros H. constructor ; try assumption. intros i. simp_subst. reflexivity.
Qed.

Lemma typing_tshift {s x} Σ Γ ty :
  ctyping Σ (Cons Γ x ty) ->
  ttyping Σ Γ (@tshift s x) (Cons Γ x ty).
Proof.
intros H. constructor.
- now depelim H.
- assumption.
- intros i. simp_subst. simp lookup_context. simp_subst. reflexivity.
Qed.

Lemma typing_tcomp {s s' s''} Σ Γ Δ Ε (δ1 : thinning s s') (δ2 : thinning s' s'') :
  ttyping Σ Γ δ1 Δ ->
  ttyping Σ Δ δ2 Ε ->
  ttyping Σ Γ (tcomp δ1 δ2) Ε.
Proof.
intros H1 H2. constructor.
- apply H1.
- apply H2.
- intros i. simp_subst. rewrite <-(ttyping_prop H2), <-(ttyping_prop H1).
  simp_subst. reflexivity.
Qed.

Lemma typing_thin {s s'} Σ Γ Δ (δ : thinning s s') (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  ttyping Σ Γ δ Δ ->
  Σ ;; Δ ⊢ thin δ t : thin δ T.
Proof.
intros Ht Hδ. induction Ht in s', δ, Hδ, Δ |- * ; simp thin.
- constructor. apply Hδ.
- subst. rewrite (ttyping_prop Hδ). constructor ; auto. apply Hδ.
- apply typing_lam ; auto using typing_ThinKeep.
- apply typing_prod ; auto using typing_ThinKeep.
- replace (thin δ (B[x ::= arg])) with ((thin (ThinKeep x δ) B)[x ::= thin δ arg])
    by now nf_subst.
  apply typing_app with (thin δ A).
  + now apply IHHt1.
  + now apply IHHt2.
- eapply typing_evar ; eauto.
  + apply Hδ.
  + now simp_subst.
- apply typing_conv_type with (A := thin δ A) ; auto. now rewrite H.
Qed.

Lemma well_typed_thin Σ {s s'} (δ : thinning s s') Γ Δ (t : term s) :
  well_typed Σ Γ t ->
  ttyping Σ Γ δ Δ ->
  well_typed Σ Δ (thin δ t).
Proof.
intros [T Ht] Hδ. exists (thin δ T). eapply typing_thin in Ht ; eauto.
Qed.

(***********************************************************************)
(** * Compatibility of typing with substitutions *)
(***********************************************************************)

Lemma typing_sid {s} Σ (Γ : context ∅ s) :
  ctyping Σ Γ ->
  styping Σ Γ sid Γ.
Proof. intros H. constructor ; auto. intros i. simp_subst. now constructor. Qed.

Lemma typing_sshift {s x} Σ (Γ : context ∅ s) ty :
  ctyping Σ (Cons Γ x ty) ->
  styping Σ Γ sshift (Cons Γ x ty).
Proof.
intros H. constructor ; auto.
- now depelim H.
- intros i. simp_subst. constructor ; auto. simp lookup_context. now nf_subst.
Qed.

Lemma typing_scons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') t σ ty :
  Σ ;; Γ ⊢ ty : Type_ ->
  Σ ;; Δ ⊢ t : substitute σ ty ->
  styping Σ Γ σ Δ ->
  styping Σ (Cons Γ x ty) (scons x t σ) Δ.
Proof.
intros H1 H2 H3. constructor.
- constructor ; auto. apply H3.
- apply H3.
- intros i. depelim i ; simp_subst ; simp lookup_context.
  + simp_subst. assumption.
  + simp_subst. apply (styping_prop H3).
Qed.

Lemma typing_stcomp {s s' s''} Σ Γ Δ E (σ : subst s s') (δ : thinning s' s'') :
  styping Σ Γ σ Δ ->
  ttyping Σ Δ δ E ->
  styping Σ Γ (stcomp σ δ) E.
Proof.
intros H1 H2. constructor.
- apply H1.
- apply H2.
- intros i. simp_subst. rewrite <-thin_substitute.
  eapply typing_thin ; [|eassumption]. apply H1.
Qed.

Lemma typing_sup {s s' x} Σ Γ Δ (σ : subst s s') ty :
  Σ ;; Γ ⊢ ty : Type_ ->
  Σ ;; Δ ⊢ substitute σ ty : Type_ ->
  styping Σ Γ σ Δ ->
  styping Σ (Cons Γ x ty) (sup x σ) (Cons Δ x (substitute σ ty)).
Proof.
intros H1 H2 H3. unfold sup. apply typing_scons.
- apply H1.
- constructor.
  + constructor ; auto. apply H3.
  + simp lookup_context. simp_subst. reflexivity.
- eapply typing_stcomp ; eauto. apply typing_tshift.
  constructor ; auto. apply H3.
Qed.

Lemma typing_substitute {s s'} Σ Γ Δ (σ : subst s s') t T :
  Σ ;; Γ ⊢ t : T ->
  styping Σ Γ σ Δ ->
  Σ ;; Δ ⊢ substitute σ t : substitute σ T.
Proof.
intros Ht Hσ. induction Ht in s', σ, Δ, Hσ |- * ; simp_subst.
- constructor. apply Hσ.
- subst. apply Hσ.
- apply typing_lam ; auto using typing_sup.
- apply typing_prod ; auto using typing_sup.
- replace (substitute (scons x _ _) _)
    with ((substitute (sup x σ) B)[x ::= substitute σ arg])
    by now simp_subst.
  apply typing_app with (substitute σ A).
  + now apply IHHt1.
  + now apply IHHt2.
- econstructor ; eauto. apply Hσ.
- eapply typing_conv_type ; eauto. now rewrite H.
Qed.

Lemma typing_tscomp {s s' s''} Σ Γ Δ E (δ : thinning s s') (σ : subst s' s'') :
  ttyping Σ Γ δ Δ ->
  styping Σ Δ σ E ->
  styping Σ Γ (tscomp δ σ) E.
Proof.
intros H1 H2. constructor.
- apply H1.
- apply H2.
- intros i. rewrite <-substitute_thin.
  replace (sapply (tscomp δ σ) i)
    with (substitute σ (Var (tapply δ i)))
    by now simp_subst.
  eapply typing_substitute ; eauto.
  rewrite (ttyping_prop H1). constructor ; auto. apply H2.
Qed.

Lemma typing_scomp {s s' s''} Σ Γ Δ E (σ1 : subst s s') (σ2 : subst s' s'') :
  styping Σ Γ σ1 Δ ->
  styping Σ Δ σ2 E ->
  styping Σ Γ (scomp σ1 σ2) E.
Proof.
intros H1 H2. constructor.
- apply H1.
- apply H2.
- intros i. simp_subst. rewrite <-substitute_substitute.
  eapply typing_substitute ; eauto. apply H1.
Qed.
