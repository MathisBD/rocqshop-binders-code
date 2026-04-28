(** This file proves confluence of reduction, using the parallel reduction method. *)

From MetaTheory Require Import Prelude Relations.
From MetaTheory Require Export Theory.Reduction.ContextReduction.

(***********************************************************************)
(** * Parallel reduction on terms *)
(***********************************************************************)

#[local] Reserved Notation "Σ ⊢ t >>{ f } u"
  (at level 50, no associativity, t at next level, u at next level).

Inductive pred1 (flags : red_flags) (Σ : evar_map) {s}
  : term s -> term s -> Prop :=

| pred1_beta x ty body body' arg arg' :
    flags.(beta) = true ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ arg >>{flags} arg' ->
    Σ ⊢ App (Lam x ty body) arg >>{flags} body'[x ::= arg']

| pred1_evar_expand ev ty def :
    Σ !! ev = Some (Vmk_evar_info ty (Some def)) ->
    Σ ⊢ Evar ev >>{flags} wk def

| pred1_type :
    Σ ⊢ Type_ >>{flags} Type_

| pred1_var i :
    Σ ⊢ Var i >>{flags} Var i

| pred1_lam x ty ty' body body' :
    Σ ⊢ ty >>{flags} ty' ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ Lam x ty body >>{flags} Lam x ty' body'

| pred1_prod x a a' b b' :
    Σ ⊢ a >>{flags} a' ->
    Σ ⊢ b >>{flags} b' ->
    Σ ⊢ Prod x a b >>{flags} Prod x a' b'

| pred1_app f f' arg arg' :
    Σ ⊢ f >>{flags} f' ->
    Σ ⊢ arg >>{flags} arg' ->
    Σ ⊢ App f arg >>{flags} App f' arg'

| pred1_evar ev :
    Σ ⊢ Evar ev >>{flags} Evar ev

where "Σ ⊢ t >>{ f } u" := (pred1 f Σ t u).

Derive Signature for pred1.

#[export] Instance pred1_Reflexive flags Σ s :
  Reflexive (@pred1 flags Σ s).
Proof.
intros t. induction t ; constructor ; assumption.
Qed.

(***********************************************************************)
(** * Parallel reduction on substitutions *)
(***********************************************************************)

Definition spred1 flags Σ {s s'} (σ σ' : subst s s') : Prop :=
  forall i, Σ ⊢ sapply σ i >>{flags} sapply σ' i.

#[export] Instance spred1_Reflexive flags Σ s s' :
  Reflexive (@spred1 flags Σ s s').
Proof. intros σ i. reflexivity. Qed.

(***********************************************************************)
(** * Relating parallel reduction and standard reduction *)
(***********************************************************************)

(** One-step reduction is included in parallel reduction. *)
Lemma pred1_of_red1 {s flags Σ} (t u : term s) :
  Σ ⊢ t ~>{flags} u -> Σ ⊢ t >>{flags} u.
Proof.
intros H. induction H.
- now apply pred1_beta.
- eapply pred1_evar_expand ; eassumption.
- now apply pred1_lam.
- now apply pred1_lam.
- now apply pred1_prod.
- now apply pred1_prod.
- now apply pred1_app.
- now apply pred1_app.
Qed.

(** Parallel reduction is included in standard reduction. *)
Lemma red_of_pred1 {s flags Σ} (t u : term s) :
  Σ ⊢ t >>{flags} u -> Σ ⊢ t ~~>{flags} u.
Proof.
intros H. induction H.
- rewrite <-red_beta. apply red_app_congr.
  + now apply red_lam_congr.
  + assumption.
  + assumption.
- eapply red_evar_expand ; eassumption.
- reflexivity.
- reflexivity.
- now apply red_lam_congr.
- now apply red_prod_congr.
- now apply red_app_congr.
- reflexivity.
Qed.

(** The reflexive closure of [pred1] is equal to [red]. *)
Lemma red_is_pred {s flags Σ} (t u : term s) :
  Σ ⊢ t ~~>{flags} u <-> refl_trans_clos (pred1 flags Σ) t u.
Proof.
split ; intros H ; induction H.
- reflexivity.
- apply refl_trans_step with t2 ; auto. now apply pred1_of_red1.
- reflexivity.
- rewrite IHrefl_trans_clos. now apply red_of_pred1.
Qed.

(***********************************************************************)
(** * Compatibility with thinning and substitution *)
(***********************************************************************)

Section Substitutivity.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma pred1_beta_alt {s} x (ty : term s) body body' arg arg' t :
    flags.(beta) = true ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ arg >>{flags} arg' ->
    t = body' [x ::= arg'] ->
    Σ ⊢ App (Lam x ty body) arg >>{flags} t.
  Proof. intros Hf H1 H2 ->. now apply pred1_beta. Qed.

  (** Thinning lemma for [pred1]. *)
  #[export] Instance pred1_thin {s s'} (δ : thinning s s') :
    Proper (pred1 flags Σ ==> pred1 flags Σ) (thin δ).
  Proof.
  intros t t' H. induction H in s', δ |- * ; simp_subst.
  - eapply pred1_beta_alt
      with (body' := thin (ThinKeep x δ) body')
           (arg' := thin δ arg') ;
    auto. simp_subst. reflexivity.
  - econstructor ; eassumption.
  - reflexivity.
  - reflexivity.
  - now apply pred1_lam.
  - now apply pred1_prod.
  - apply pred1_app.
    + apply IHpred1_1.
    + apply IHpred1_2.
  - reflexivity.
  Qed.

  #[export] Instance pred1_scons {x s s'} :
    Proper (pred1 flags Σ ==> spred1 flags Σ ==> spred1 flags Σ)
           (@scons s s' x).
  Proof.
  intros t t' Ht σ σ' Hσ i. depelim i ; simp_subst ; auto.
  Qed.

  #[export] Instance pred1_sup {x s s'} :
    Proper (spred1 flags Σ ==> spred1 flags Σ) (@sup s s' x).
  Proof.
  intros σ σ' H i. depelim i ; simp_subst.
  - reflexivity.
  - apply pred1_thin. apply H.
  Qed.

  (** Substitution lemma for [pred1]. *)
  #[export] Instance pred1_substitute {s s'} :
    Proper (spred1 flags Σ ==> pred1 flags Σ ==> pred1 flags Σ)
           (@substitute s s').
  Proof.
  intros σ σ' Hσ t t' Ht.
  induction Ht in s', σ, σ', Hσ |- * ; simp_subst.
  - apply pred1_beta_alt
      with (body' := substitute (sup x σ') body')
           (arg' := substitute σ' arg').
    + assumption.
    + apply IHHt1. now apply pred1_sup.
    + now apply IHHt2.
    + now simp_subst.
  - econstructor ; eauto.
  - reflexivity.
  - apply Hσ.
  - apply pred1_lam ; auto. apply IHHt2. now apply pred1_sup.
  - apply pred1_prod ; auto. apply IHHt2. now apply pred1_sup.
  - apply pred1_app ; auto.
  - reflexivity.
  Qed.

End Substitutivity.

(***********************************************************************)
(** * Joinability for parallel reduction *)
(***********************************************************************)

(** Two terms are joinable if they have a common reduct for [pred1]. *)
Definition joinable flags Σ {s} (t1 t2 : term s) : Prop :=
  exists u, Σ ⊢ t1 >>{flags} u /\ Σ ⊢ t2 >>{flags} u.

(** Two substitutions are joinable if they are pointwise joinable. *)
Definition joinable_subst flags Σ {s s'} (σ1 σ2 : subst s s') : Prop :=
  exists σ, spred1 flags Σ σ1 σ /\ spred1 flags Σ σ2 σ.

Section JoinabilityLemmas.
  Context {flags : red_flags} {Σ : evar_map}.

  #[export] Instance joinable_Reflexive s :
    Reflexive (@joinable flags Σ s).
  Proof. intros t. exists t. now split. Qed.

  #[export] Instance joinable_Symmetric s :
    Symmetric (@joinable flags Σ s).
  Proof. intros t1 t2. unfold joinable. firstorder. Qed.

  #[export] Instance joinable_subst_Reflexive s s' :
    Reflexive (@joinable_subst flags Σ s s').
  Proof. intros σ. exists σ. split ; reflexivity. Qed.

  #[export] Instance joinable_subst_Symmetric s s' :
    Symmetric (@joinable_subst flags Σ s s').
  Proof. intros σ1 σ2 (σ & H1 & H2). exists σ. firstorder. Qed.

  Lemma joinable_scons {x s s'} t1 t2 (σ1 σ2 : subst s s') :
    joinable flags Σ t1 t2 ->
    joinable_subst flags Σ σ1 σ2 ->
    joinable_subst flags Σ (scons x t1 σ1) (scons x t2 σ2).
  Proof.
  intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (scons x t σ).
  split ; now apply pred1_scons.
  Qed.

  Lemma joinable_substitute {s s'} (t1 t2 : term s) (σ1 σ2 : subst s s') :
    joinable flags Σ t1 t2 ->
    joinable_subst flags Σ σ1 σ2 ->
    joinable flags Σ (substitute σ1 t1) (substitute σ2 t2).
  Proof.
  intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (substitute σ t).
  split ; now apply pred1_substitute.
  Qed.

  Lemma joinable_lam {s x} (ty1 ty2 : term s) body1 body2 :
    joinable flags Σ ty1 ty2 ->
    joinable flags Σ body1 body2 ->
    joinable flags Σ (Lam x ty1 body1) (Lam x ty2 body2).
  Proof.
  intros (ty & Hty1 & Hty2) (body & Hbody1 & Hbody2).
  exists (Lam x ty body). split ; apply pred1_lam ; assumption.
  Qed.

  Lemma joinable_prod {s x} (a1 a2 : term s) b1 b2 :
    joinable flags Σ a1 a2 ->
    joinable flags Σ b1 b2 ->
    joinable flags Σ (Prod x a1 b1) (Prod x a2 b2).
  Proof.
  intros (a & Ha1 & Ha2) (b & Hb1 & Hb2).
  exists (Prod x a b). split ; apply pred1_prod ; assumption.
  Qed.

  Lemma joinable_app {s} (f1 f2 arg1 arg2 : term s) :
    joinable flags Σ f1 f2 ->
    joinable flags Σ arg1 arg2 ->
    joinable flags Σ (App f1 arg1) (App f2 arg2).
  Proof.
  intros (f & Hf1 & Hf2) (arg & Harg1 & Harg2).
  exists (App f arg). split ; apply pred1_app ; assumption.
  Qed.

  Lemma joinable_beta_l {s x} ty2 body1 body2
        (arg1 arg2 : term s) :
    flags.(beta) = true ->
    joinable flags Σ body1 body2 ->
    joinable flags Σ arg1 arg2 ->
    joinable flags Σ (body1[x ::= arg1]) (App (Lam x ty2 body2) arg2 ).
  Proof.
  intros Hf (body & Hbody1 & Hbody2) (arg & Harg1 & Harg2).
  exists (body[x ::= arg]). split.
  - apply pred1_substitute.
    + now apply pred1_scons.
    + assumption.
  - eapply pred1_beta ; eauto.
  Qed.

End JoinabilityLemmas.

(***********************************************************************)
(** * Diamond property for parallel reduction *)
(***********************************************************************)

Section DiamondPred1.
  Context {flags : red_flags} {Σ : evar_map}.

  (** Helper tactic to solve goals of the form [term_size _ < term_size _]. *)
  #[local] Ltac solve_size :=
    try solve [ assumption
              | (repeat first [ progress simp term_size | progress cbn ]) ; lia ].

  (** [pred1] has the diamond property. *)
  Lemma pred1_diamond {s} (t : term s) :
    diamond (pred1 flags Σ) (pred1 flags Σ) t.
  Proof.
  (* The proof is by induction on the size of [t], then inspecting
     the shape of both reductions from [t]. *)
  remember (term_size t) as n. revert s t Heqn. induction n using Wf_nat.lt_wf_ind.
  intros s t -> u1 u2 Hu1 Hu2.
  assert (IH : forall s (x : term s),
    term_size x < term_size t -> diamond (pred1 flags Σ) (pred1 flags Σ) x) by firstorder.
  clear H. change (joinable flags Σ u1 u2).
  depelim Hu1 ; depelim Hu2 ; try reflexivity.
  - apply joinable_substitute ; [| apply joinable_scons].
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
    + reflexivity.
  - depelim Hu2_1. eapply joinable_beta_l.
    + assumption.
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
  - rewrite H0 in H. depelim H. reflexivity.
  - exists (wk def). split ; [reflexivity |]. econstructor ; eassumption.
  - apply joinable_lam.
    + apply IH with ty ; solve_size.
    + apply IH with body ; solve_size.
  - apply joinable_prod.
    + apply IH with a ; solve_size.
    + apply IH with b ; solve_size.
  - depelim Hu1_1. symmetry. eapply joinable_beta_l.
    + assumption.
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
  - apply joinable_app.
    + apply IH with f ; solve_size.
    + apply IH with arg ; solve_size.
  - exists (wk def). split ; [|reflexivity]. econstructor ; eassumption.
  Qed.

End DiamondPred1.

(***********************************************************************)
(** * Main result: confluence of [red], [sred], and [cred] *)
(***********************************************************************)

Section Confluence.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma red_confluence {s} (t u1 u2 : term s) :
    Σ ⊢ t ~~>{flags} u1 ->
    Σ ⊢ t ~~>{flags} u2 ->
    exists v, Σ ⊢ u1 ~~>{flags} v /\ Σ ⊢ u2 ~~>{flags} v.
  Proof.
  intros H1 H2. setoid_rewrite red_is_pred.
  rewrite red_is_pred in H1, H2.
  eapply diamond_confluence with (R := @pred1 flags Σ s) ; eauto using pred1_diamond.
  Qed.

  Lemma sred_confluence {s s'} (σ τ1 τ2 : subst s s') :
    sred flags Σ σ τ1 ->
    sred flags Σ σ τ2 ->
    exists σ', sred flags Σ τ1 σ' /\ sred flags Σ τ2 σ'.
  Proof.
  intros H1 H2. induction s in s', σ, τ1, τ2, H1, H2 |- *.
  - exists (subst_of_thin wk_idx). split ; constructor ; intros i ; depelim i.
  - specialize (IHs s' (tscomp tshift σ) (tscomp tshift τ1) (tscomp tshift τ2)).
    forward IHs. { now rewrite H1. }
    forward IHs. { now rewrite H2. }
    destruct IHs as (σ' & Hσ1 & Hσ2).
    assert (exists t,
      Σ ⊢ sapply τ1 I0 ~~>{flags} t /\
      Σ ⊢ sapply τ2 I0 ~~>{flags} t) as (t & Ht1 & Ht2).
    {
      apply red_confluence with (sapply σ I0).
      - now rewrite H1.
      - now rewrite H2.
    }
    exists (scons x t σ'). split ; constructor ; intros i ; depelim i ; simp_subst.
    + apply Ht1.
    + pose proof (H := sred_prop _ _ _ _ Hσ1 i). simp_subst in H. exact H.
    + apply Ht2.
    + pose proof (H := sred_prop _ _ _ _ Hσ2 i). simp_subst in H. exact H.
  Qed.

  (** Confluence for [cred] follows from confluence for [red]. *)
  Lemma cred_confluence {s} (Γ Γ1 Γ2 : context ∅ s) :
    cred flags Σ Γ Γ1 ->
    cred flags Σ Γ Γ2 ->
    exists Γ', cred flags Σ Γ1 Γ' /\ cred flags Σ Γ2 Γ'.
  Proof.
  intros H1 H2. induction s in Γ, Γ1, Γ2, H1, H2 |- *.
  - depelim Γ ; depelim Γ1 ; depelim Γ2. exists Nil. split ; constructor.
  - depelim H1. depelim H2.
    destruct (IHs _ _ _ H1 H2) as (Γ1 & HΓ & HΓ').
    assert (exists ty1, Σ ⊢ ty' ~~>{flags} ty1 /\ Σ ⊢ ty'0 ~~>{flags} ty1) as (ty1 & Hty1 & Hty2).
    { now apply red_confluence with ty. }
    exists (Cons Γ1 x ty1). split ; constructor ; auto.
  Qed.

End Confluence.