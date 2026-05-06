(** This module defines:
    - The one-step strong reduction relation [red1] on terms.
    - The strong reduction relation [red] on terms.

    We prove some basic properties, notably:
    - Congruence lemmas.
    - Inversion lemmas.
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.RedFlags.
From MetaTheory Require Export Data.EvarMap Theory.SigmaCalculus.

(***********************************************************************)
(** * One-step reduction relation [red1] *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ~>{ f } u"
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' '[hv' Σ  ⊢  t '/  ' ~>{ f } ']' '/    ' u ']'").

(** Strong one-step reduction relation. This relation is _not_ deterministic. *)
Inductive red1 (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| red1_beta x ty body arg :
    flags.(beta) = true ->
    Σ ⊢ App (Lam x ty body) arg ~>{flags} body[x ::= arg]

(** Evar expansion. *)
| red1_evar_expand ev ty def :
    Σ !! ev = Some (Vmk_evar_info ty (Some def)) ->
    Σ ⊢ Evar ev ~>{flags} wk def

(** Congrence rules for [Lam]. *)
| red1_lam_l x ty ty' body :
    Σ ⊢ ty ~>{flags} ty' -> Σ ⊢ Lam x ty body ~>{flags} Lam x ty' body
| red1_lam_r x ty body body' :
    Σ ⊢ body ~>{flags} body' -> Σ ⊢ Lam x ty body ~>{flags} Lam x ty body'

(** Congruence rules for [Prod]. *)
| red1_prod_l x a a' b :
    Σ ⊢ a ~>{flags} a' -> Σ ⊢ Prod x a b ~>{flags} Prod x a' b
| red1_prod_r x a b b' :
    Σ ⊢ b ~>{flags} b' -> Σ ⊢ Prod x a b ~>{flags} Prod x a b'

(** Congruence rules for [App]. *)
| red1_app_l f f' arg :
    Σ ⊢ f ~>{flags} f' -> Σ ⊢ App f arg ~>{flags} App f' arg
| red1_app_r f arg arg' :
    Σ ⊢ arg ~>{flags} arg' -> Σ ⊢ App f arg ~>{flags} App f arg'

where "Σ ⊢ t ~>{ f } u" := (red1 f Σ t u).

Derive Signature for red1.

(** [Σ ⊢ t ~> u] is one-step reduction with all reduction flags enabled. *)
Notation "Σ ⊢ t ~> u" := (red1 red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ~> '/    ' u ']'").

(** [Σ ⊢ t ~>ev u] is one-step reduction with no reduction flags enabled:
    only evar expansion is allowed. *)
Notation "Σ ⊢ t ~>ev u" := (red1 red_flags_none Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ~>ev '/    ' u ']'").

(***********************************************************************)
(** * Reduction relation [red] *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ~~>{ f } u"
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' '[hv' Σ  ⊢  t '/  ' ~~>{ f } ']' '/    ' u ']'").

(** Strong reduction relation, defined as the reflexive-transitive closure of [red1]. *)
Inductive red (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=
| red_refl t : Σ ⊢ t ~~>{flags} t
| red_step t1 t2 t3 : Σ ⊢ t1 ~~>{flags} t2 -> Σ ⊢ t2 ~>{flags} t3 -> Σ ⊢ t1 ~~>{flags} t3

where "Σ ⊢ t ~~>{ f } u" := (red f Σ t u).

Derive Signature for red.

(** [Σ ⊢ t ~~> u] is reduction with all reduction flags enabled. *)
Notation "Σ ⊢ t ~~> u" := (red red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ~~> '/    ' u ']'").

(** [Σ ⊢ t ~~>ev u] is reduction with no reduction flags enabled:
    only evar expansion is allowed. *)
Notation "Σ ⊢ t ~~>ev u" := (red red_flags_none Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ~~>ev '/    ' u ']'").

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

#[export] Instance red_Reflexive s flags Σ : Reflexive (@red flags Σ s).
Proof. intros t. apply red_refl. Qed.

#[export] Instance red_Transitive s flags Σ : Transitive (@red flags Σ s).
Proof.
intros t1 t2 t3 H1 H2. induction H2.
- assumption.
- apply red_step with t2 ; auto.
Qed.

#[export] Instance red_of_red1 s flags Σ :
  subrelation (@red1 flags Σ s) (@red flags Σ s).
Proof. intros t u H. apply red_step with t ; auto. apply red_refl. Qed.

Lemma red_same s flags Σ (t u : term s) :
  t = u -> Σ ⊢ t ~~>{flags} u.
Proof. intros ->. reflexivity. Qed.

(***********************************************************************)
(** * Congruence lemmas for [red1] *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope} (flags : red_flags) (Σ : evar_map).

  Lemma red1_beta_alt x (ty : term s) body arg t :
    flags.(beta) = true ->
    t = body[x ::= arg] ->
    Σ ⊢ App (Lam x ty body) arg ~>{flags} t.
  Proof. intros H ->. now apply red1_beta. Qed.

  #[export] Instance red1_lam_congr_l x :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@Lam s x).
  Proof. intros ty ty' Hty body body' <-. now apply red1_lam_l. Qed.

  #[export] Instance red1_lam_congr_r x :
    Proper (eq ==> red1 flags Σ ==> red1 flags Σ) (@Lam s x).
  Proof. intros ty ty' <- body body' Hbody. now apply red1_lam_r. Qed.

  #[export] Instance red1_prod_congr_l x :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@Prod s x).
  Proof. intros ty ty' Hty body body' <-. now apply red1_prod_l. Qed.

  #[export] Instance red1_prod_congr_r x :
    Proper (eq ==> red1 flags Σ ==> red1 flags Σ) (@Prod s x).
  Proof. intros ty ty' <- body body' Hbody. now apply red1_prod_r. Qed.

  #[export] Instance red1_app_congr_l :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@App s).
  Proof. intros f f' Hf arg arg' <-. now apply red1_app_l. Qed.

  #[export] Instance red1_app_congr_r :
    Proper (eq ==> red1 flags Σ ==> red1 flags Σ) (@App s).
  Proof. intros f f' <- arg arg' Harg. now apply red1_app_r. Qed.

  #[export] Instance red1_apps_congr_l :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@apps s).
  Proof.
  intros f f' Hf args args' <-. induction args in f, f', Hf |- *.
  - now rewrite !apps_nil.
  - rewrite !apps_cons. apply IHargs. now apply red1_app_congr_l.
  Qed.

  #[export] Instance red1_apps_congr_r :
    Proper (eq ==> OnOne2 (red1 flags Σ) ==> red1 flags Σ) (@apps s).
  Proof.
  intros f f' <- args args' Hargs. induction Hargs in f |- *.
  - rewrite !apps_cons. now apply red1_apps_congr_l ; [apply red1_app_congr_r |].
  - rewrite !apps_cons. apply IHHargs.
  Qed.

End CongruenceLemmas.

(** Extending the set of flags or the evar map preserves reductions. *)
#[export] Instance red1_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@red1).
Proof.
intros f f' Hf Σ Σ' HΣ s t t' <- u u' <- H. induction H.
- constructor. now apply Hf.
- econstructor. pose proof (Hev := Vevm_incl_prop _ _ HΣ ev).
  rewrite H in Hev. depelim Hev ; eassumption.
- apply red1_lam_congr_l ; firstorder.
- apply red1_lam_congr_r ; firstorder.
- apply red1_prod_congr_l ; firstorder.
- apply red1_prod_congr_r ; firstorder.
- apply red1_app_congr_l ; firstorder.
- apply red1_app_congr_r ; firstorder.
Qed.

(***********************************************************************)
(** * Congruence lemmas for [red] *)
(***********************************************************************)

Section CongruenceLemmas.
  Context (flags : red_flags) (Σ : evar_map) {s : scope}.

  Lemma red_beta x (ty : term s) body arg :
    flags.(beta) = true ->
    Σ ⊢ App (Lam x ty body) arg ~~>{flags} body[x ::= arg].
  Proof. intros H. now rewrite red1_beta. Qed.

  Lemma red_evar_expand ev ty def :
    Σ !! ev = Some (Vmk_evar_info ty (Some def)) ->
    Σ ⊢ @Evar s ev ~~>{flags} wk def.
  Proof. intros H. rewrite red1_evar_expand ; eauto. reflexivity. Qed.

  #[export] Instance red_lam_congr x :
    Proper (red flags Σ ==> red flags Σ ==> red flags Σ) (@Lam s x).
  Proof.
  intros ty ty' Hty body body' Hbody. transitivity (Lam x ty body').
  - clear Hty. induction Hbody.
    + reflexivity.
    + now rewrite <-H.
  - clear Hbody. induction Hty.
    + reflexivity.
    + now rewrite <-H.
  Qed.

  #[export] Instance red_prod_congr x :
    Proper (red flags Σ ==> red flags Σ ==> red flags Σ) (@Prod s x).
  Proof.
  intros a a' Ha b b' Hb. transitivity (Prod x a b').
  - clear Ha. induction Hb.
    + reflexivity.
    + now rewrite <-H.
  - clear Hb. induction Ha.
    + reflexivity.
    + now rewrite <-H.
  Qed.

  #[export] Instance red_app_congr :
    Proper (red flags Σ ==> red flags Σ ==> red flags Σ) (@App s).
  Proof.
  intros f f' Hf arg arg' Harg. transitivity (App f' arg).
  - clear Harg. induction Hf.
    + reflexivity.
    + now rewrite <-H.
  - clear f Hf. induction Harg.
    + reflexivity.
    + now rewrite <-H.
  Qed.

  Lemma red_apps_congr_l :
    Proper (red flags Σ ==> eq ==> red flags Σ) (@apps s).
  Proof.
  intros f f' Hf args args' <-. induction Hf.
  - reflexivity.
  - now rewrite <-H.
  Qed.

  #[export] Instance red_apps_congr :
    Proper (red flags Σ ==> Forall2 (red flags Σ) ==> red flags Σ) (@apps s).
  Proof.
  intros f f' Hf args args' Hargs. transitivity (apps f' args).
  - now apply red_apps_congr_l.
  - clear f Hf. induction Hargs in f' |- *.
    + reflexivity.
    + rewrite !apps_cons. rewrite IHHargs.
      apply red_apps_congr_l ; [| reflexivity]. now rewrite H.
  Qed.

End CongruenceLemmas.

(** Generalization of the beta reduction rule to an iterated lambda product. *)
Lemma red_beta_context flags Σ {s s'} (Γ : context s s') (body : term s') args :
  flags.(beta) = true ->
  List.length args = context_length Γ ->
  Σ ⊢ apps (lam_context Γ body) args
    ~~>{flags} substitute (context_subst Γ args) body.
Proof.
intros Hbeta Hlen. induction Γ in body, args, Hbeta, Hlen |- *.
- simp lam_context context_subst. simp_subst. simp context_length in Hlen.
  destruct args ; [| depelim Hlen]. reflexivity.
- simp lam_context context_subst. destruct (snoc args) as [[ts t] |] eqn:Hargs.
  + apply snoc_Some in Hargs. subst. rewrite apps_app. simp apps.
    rewrite IHΓ.
    * simp_subst. rewrite red_beta by assumption. simp_subst. reflexivity.
    * assumption.
    * rewrite length_app in Hlen. cbn in Hlen. simp context_length in Hlen. lia.
  + apply snoc_None in Hargs. subst. cbn in Hlen. simp context_length in Hlen. depelim Hlen.
Qed.

(** Extending the set of flags or the evar map preserves reductions. *)
#[export] Instance red_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@red).
Proof.
intros f f' Hf Σ Σ' HΣ s t t' <- u u' <- H. induction H.
- reflexivity.
- rewrite IHred by assumption. rewrite HΣ, Hf in H0. now rewrite H0.
Qed.

(***********************************************************************)
(** * Inversion lemmas for [red] *)
(***********************************************************************)

Section InversionLemmas.
  Context (flags : red_flags) (Σ : evar_map) {s : scope}.

  Lemma red_type_inv (t : term s) :
    Σ ⊢ Type_ ~~>{flags} t -> t = Type_.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_var_inv (i : index s) (t : term s) :
    Σ ⊢ Var i ~~>{flags} t -> t = Var i.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_lam_inv x (ty : term s) body t :
    Σ ⊢ Lam x ty body ~~>{flags} t ->
    exists ty' body',
      t = Lam x ty' body' /\
      Σ ⊢ ty ~~>{flags} ty' /\
      Σ ⊢ body ~~>{flags} body'.
  Proof.
  intros Hred. depind Hred.
  - exists ty, body. now split3.
  - destruct IHHred as (ty' & body' & -> & Hty1 & Hbody1). depelim H.
    + exists ty'0, body'. split3 ; [reflexivity | | assumption].
      rewrite Hty1. now apply red_of_red1.
    + exists ty', body'0. split3 ; [reflexivity | assumption |].
      rewrite Hbody1. now apply red_of_red1.
  Qed.

  Lemma red_lam_inv' x (ty ty' : term s) body body' :
    Σ ⊢ Lam x ty body ~~>{flags} Lam x ty' body' ->
    Σ ⊢ ty ~~>{flags} ty' /\
    Σ ⊢ body ~~>{flags} body'.
  Proof.
  intros H. apply red_lam_inv in H. destruct H as (? & ? & Heq & H1 & H2).
  depelim Heq. now split.
  Qed.

  Lemma red_prod_inv x (a : term s) b t :
    Σ ⊢ Prod x a b ~~>{flags} t ->
    exists a' b',
      t = Prod x a' b' /\
      Σ ⊢ a ~~>{flags} a' /\
      Σ ⊢ b ~~>{flags} b'.
  Proof.
  intros Hred. depind Hred.
  - exists a, b. now split3.
  - destruct IHHred as (a' & b' & -> & Ha1 & Hb1). depelim H.
    + exists a'0, b'. split3 ; [reflexivity | | assumption].
      rewrite Ha1. now apply red_of_red1.
    + exists a', b'0. split3 ; [reflexivity | assumption |].
      rewrite Hb1. now apply red_of_red1.
  Qed.

  Lemma red_prod_inv' x (a a' : term s) b b' :
    Σ ⊢ Prod x a b ~~>{flags} Prod x a' b' ->
    Σ ⊢ a ~~>{flags} a' /\
    Σ ⊢ b ~~>{flags} b'.
  Proof.
  intros H. apply red_prod_inv in H. destruct H as (? & ? & Heq & H1 & H2).
  depelim Heq. now split.
  Qed.

End InversionLemmas.

Ltac2 inv_red (h : ident) : unit :=
  lazy_match! Constr.type (Control.hyp h) with
  | _ ⊢ Lam _ _ _ ~~>{_} Lam _ _ _ => apply red_lam_inv' in $h
  | _ ⊢ Lam _ _ _ ~~>{_} _ => apply red_lam_inv in $h
  | _ ⊢ Prod _ _ _ ~~>{_} Prod _ _ _ => apply red_prod_inv' in $h
  | _ ⊢ Prod _ _ _ ~~>{_} _ => apply red_prod_inv in $h
  | _ ⊢ _ ~~>{_} _ => tactic_failure! "Can't invert this reduction derivation"
  | ?x => tactic_failure! "Not a reduction derivation: %t" x
  end.

(** [inv_red in H] tries to invert the reduction derivation [H : Σ ⊢ t ~~>{flags} t'].
    Also accepts several arguments e.g. [inv_red in H1, H2, H3]. *)
Tactic Notation "inv_red" "in" ne_ident_list_sep(Hs, ",") :=
  let f := ltac2:(hs |-
    let hs := Option.get (Ltac1.to_list hs) in
    List.iter (fun h => inv_red (Option.get (Ltac1.to_ident h))) hs)
  in f Hs.
