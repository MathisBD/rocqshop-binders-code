From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.Context Theory.Conversion.ContextConversion.

(***********************************************************************)
(** * Lifting a typing-like relation on a context *)
(***********************************************************************)

Section All_context.
  Context (P : forall s, context ∅ s -> term s -> term s -> Prop).

  Inductive All_context : forall {s}, context ∅ s -> Prop :=
  | All_context_nil : All_context Nil
  | All_context_cons {s} (Γ : context ∅ s) x ty :
      All_context Γ ->
      P s Γ ty Type_ ->
      All_context (Cons Γ x ty).
End All_context.

Derive Signature for All_context.

Lemma All_context_consequence
  (P Q : forall s, context ∅ s -> term s -> term s -> Prop) :
  (forall s Γ t T, P s Γ t T -> Q s Γ t T) ->
  forall s (Γ : context ∅ s), All_context P Γ -> All_context Q Γ.
Proof.
intros Himpl s Γ H. induction H ; econstructor ; eauto.
Qed.

Lemma All_context_and
 {P Q : forall s, context ∅ s -> term s -> term s -> Prop}
 {s} {Γ : context ∅ s} :
  All_context (fun s Γ t T => P s Γ t T /\ Q s Γ t T) Γ ->
  (All_context P Γ /\ All_context Q Γ).
Proof.
induction Γ.
- constructor ; constructor.
- intros H. depelim H. apply IHΓ in H. split ; now constructor.
Qed.

(***********************************************************************)
(** * Typing relation on terms *)
(***********************************************************************)

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ, t, T at next level,
   format "'[hv' Σ  ;;  Γ  ⊢  t '/       ' :  T ']'").

Reserved Notation "'ctyping' Σ"
  (at level 9, no associativity, Σ at next level).

Unset Elimination Schemes.

Inductive typing (Σ : evar_map) {s} (Γ : context ∅ s) : term s -> term s -> Prop :=

| typing_type :
    ctyping Σ Γ ->
    Σ ;; Γ ⊢ Type_ : Type_

| typing_var i ty :
    ctyping Σ Γ ->
    lookup_context i Γ = ty ->
    Σ ;; Γ ⊢ Var i : ty

| typing_lam x ty body body_ty :
    Σ ;; Γ ⊢ ty : Type_ ->
    Σ ;; Cons Γ x ty ⊢ body : body_ty ->
    Σ ;; Γ ⊢ Lam x ty body : Prod x ty body_ty

| typing_prod x a b :
    Σ ;; Γ ⊢ a : Type_ ->
    Σ ;; Cons Γ x a ⊢ b : Type_ ->
    Σ ;; Γ ⊢ Prod x a b : Type_

| typing_app f arg x A B :
    Σ ;; Γ ⊢ f : Prod x A B ->
    Σ ;; Γ ⊢ arg : A ->
    Σ ;; Γ ⊢ App f arg : B[x ::= arg]

| typing_evar ev entry ty :
    ctyping Σ Γ ->
    Σ !! ev = Some entry ->
    wk entry.(evar_type) = ty ->
    Σ ;; Γ ⊢ Evar ev : ty

| typing_conv_type t A B :
    Σ ;; Γ ⊢ t : A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : Type_ ->
    Σ ;; Γ ⊢ t : B

where "Σ ;; Γ ⊢ t : T" := (typing Σ Γ t T)
   and "'ctyping' Σ" := (All_context (@typing Σ)).

Set Elimination Schemes.

Derive Signature for typing.

(***********************************************************************)
(** * Induction principle for [typing] *)
(***********************************************************************)

(** Because [typing] is nested over [All_context], we need to prove
    a custom induction principle. *)
Lemma typing_ind (Σ : evar_map)
  (P : forall s, context ∅ s -> term s -> term s -> Prop)
  (Htype : forall s Γ,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    P s Γ Type_ Type_)
  (Hvar : forall s Γ i ty,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    lookup_context i Γ = ty ->
    P s Γ (Var i) ty)
  (Hlam : forall s Γ x ty body body_ty,
    Σ ;; Γ ⊢ ty : Type_ -> P s Γ ty Type_ ->
    Σ ;; Cons Γ x ty ⊢ body : body_ty -> P (s ▷ x) (Cons Γ x ty) body body_ty ->
    P s Γ (Lam x ty body) (Prod x ty body_ty))
  (Hprod : forall s Γ x a b,
    Σ ;; Γ ⊢ a : Type_ -> P s Γ a Type_ ->
    Σ ;; Cons Γ x a ⊢ b : Type_ -> P (s ▷ x) (Cons Γ x a) b Type_ ->
    P s Γ (Prod x a b) Type_)
  (Happ : forall s Γ f arg x A B,
    Σ ;; Γ ⊢ f : Prod x A B -> P s Γ f (Prod x A B) ->
    Σ ;; Γ ⊢ arg : A -> P s Γ arg A ->
    P s Γ (App f arg) (B[x ::= arg]))
  (Hevar : forall s Γ ev entry,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    Σ !! ev = Some entry ->
    P s Γ (Evar ev) (wk entry.(evar_type)))
  (Hconv_type : forall s Γ t A B,
    Σ ;; Γ ⊢ t : A -> P s Γ t A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : Type_ -> P s Γ B Type_ ->
    P s Γ t B) :
  forall s Γ t T, Σ ;; Γ ⊢ t : T -> P s Γ t T.
Proof.
fix IH 5. intros s Γ t T H. depelim H.
- apply Htype. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- apply Hvar ; auto. subst. clear i. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- apply Hlam ; auto.
- apply Hprod ; auto.
- eapply Happ ; eauto.
- subst. apply Hevar ; auto. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- eapply Hconv_type ; eauto.
Qed.

(***********************************************************************)
(** * Basic properties of [typing] *)
(***********************************************************************)

(** In a typing derivation [Σ ;; Γ ⊢ t : T] the context [Γ] is itself well-typed. *)
Lemma typing_context_validity {s} Σ Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  ctyping Σ Γ.
Proof.
intros H. induction H ; auto.
all: revert H ; now apply All_context_consequence.
Qed.

(** This rule is nicer to use than [typing_prod]. *)
Lemma typing_prod_alt Σ {s x} (Γ : context ∅ s) (A : term s) B :
  Σ ;; Cons Γ x A ⊢ B : Type_ ->
  Σ ;; Γ ⊢ Prod x A B : Type_.
Proof.
intros H. constructor.
- apply typing_context_validity in H. depelim H. assumption.
- assumption.
Qed.

(** Iterated version of [typing_prod_alt]. *)
Lemma typing_prod_context_alt Σ {s s'} (Γ : context ∅ s) (Γ' : context s s') (T : term s') :
  Σ ;; (Γ ++ Γ') ⊢ T : Type_ ->
  Σ ;; Γ ⊢ prod_context Γ' T : Type_.
Proof.
intros H. depind Γ' ; simp prod_context app_context in *.
apply IHΓ', typing_prod_alt. assumption.
Qed.

(** This rule is nicer to use than [typing_lam]. *)
Lemma typing_lam_alt Σ {s x} (Γ : context ∅ s) (ty : term s) body body_ty :
  Σ ;; Cons Γ x ty ⊢ body : body_ty ->
  Σ ;; Γ ⊢ Lam x ty body : Prod x ty body_ty.
Proof.
intros H. constructor.
- apply typing_context_validity in H. depelim H. assumption.
- assumption.
Qed.

(** Iterated version of [typing_lam_alt]. *)
Lemma typing_lam_context_alt Σ {s s'} (Γ : context ∅ s) (Γ' : context s s') (body body_ty : term s') :
  Σ ;; (Γ ++ Γ') ⊢ body : body_ty ->
  Σ ;; Γ ⊢ lam_context Γ' body : prod_context Γ' body_ty.
Proof.
intros H. depind Γ' ; simp prod_context lam_context app_context in *.
apply IHΓ', typing_lam_alt. assumption.
Qed.

#[export] Instance typing_extend_evm :
  Proper (Vevm_incl ==> ∀ s, eq ==> eq ==> eq ==> impl) (@typing).
Proof.
intros Σ Σ' HΣ s Γ ? <- t ? <- T ? <- H. induction H.
- constructor. revert H. apply All_context_consequence. firstorder.
- constructor ; auto. revert H. apply All_context_consequence. firstorder.
- constructor ; auto.
- constructor ; auto.
- eapply typing_app ; eauto.
- pose proof (Hev := Vevm_incl_prop _ _ HΣ ev). rewrite H0 in Hev. depelim Hev.
  + cbn. eapply typing_evar ; eauto.
    revert H. apply All_context_consequence. firstorder.
  + cbn. eapply typing_evar ; eauto.
    revert H. apply All_context_consequence. firstorder.
- apply typing_conv_type with A ; auto. now rewrite <-HΣ.
Qed.

(** Unfortunaly this can't be a [Proper] instance because [ctyping]
    is a notation. *)
Lemma ctyping_extend_evm {s Σ1 Σ2} {Γ : context ∅ s} :
  Σ1 ⊑ Σ2 ->
  ctyping Σ1 Γ ->
  ctyping Σ2 Γ.
Proof.
intros HΣ H. induction H.
- constructor.
- constructor.
  + assumption.
  + now rewrite <-HΣ.
Qed.

(***********************************************************************)
(** * Inverting typing derivations *)
(***********************************************************************)

Lemma typing_type_inv {s} Σ Γ T :
  Σ ;; Γ ⊢ Type_ : T ->
  Σ ⊢ T ≡ @Type_ s.
Proof.
intros H. depind H.
- reflexivity.
- now rewrite <-H0.
Qed.

Lemma typing_var_inv {s} Σ Γ (i : index s) T :
  Σ ;; Γ ⊢ Var i : T ->
  Σ ⊢ T ≡ lookup_context i Γ.
Proof.
intros H. depind H.
- now subst.
- now rewrite <-H0.
Qed.

Lemma typing_lam_inv_aux {s x} Σ Γ (t : term s) T :
  Σ ;; Γ ⊢ t : T ->
  forall ty body, t = Lam x ty body ->
  exists body_ty,
    Σ ⊢ T ≡ Prod x ty body_ty /\
    Σ ;; Γ ⊢ ty : Type_ /\
    Σ ;; Cons Γ x ty ⊢ body : body_ty.
Proof.
intros H. induction H ; intros ty' body' Ht ; depelim Ht.
- exists body_ty. now split3.
- destruct (IHtyping1 ty' body' eq_refl) as (body_ty' & HA & Hty & Hbody).
  exists body_ty'. split3 ; auto. now rewrite <-H0.
Qed.

Lemma typing_lam_inv {s x} Σ Γ (ty : term s) body T :
  Σ ;; Γ ⊢ Lam x ty body : T ->
  exists body_ty,
    Σ ⊢ T ≡ Prod x ty body_ty /\
    Σ ;; Γ ⊢ ty : Type_ /\
    Σ ;; Cons Γ x ty ⊢ body : body_ty.
Proof. intros H. eapply typing_lam_inv_aux in H ; eauto. Qed.

Lemma typing_prod_inv_aux {s x} Σ Γ (t : term s) T :
  Σ ;; Γ ⊢ t : T ->
  forall a b, t = Prod x a b ->
    Σ ⊢ T ≡ Type_ /\
    Σ ;; Γ ⊢ a : Type_ /\
    Σ ;; Cons Γ x a ⊢ b : Type_.
Proof.
intros H. induction H ; intros a' b' Ht ; depelim Ht.
- now split3.
- destruct (IHtyping1 a' b' eq_refl) as (HA & Ha & Hb).
  split3 ; auto. now rewrite <-H0.
Qed.

Lemma typing_prod_inv {s x} Σ Γ (a : term s) b T :
  Σ ;; Γ ⊢ Prod x a b : T ->
  Σ ⊢ T ≡ Type_ /\ Σ ;; Γ ⊢ a : Type_ /\ Σ ;; Cons Γ x a ⊢ b : Type_.
Proof. intros H. eapply typing_prod_inv_aux in H ; eauto. Qed.

Lemma typing_prod_inv' Σ {s x} (Γ : context ∅ s) (A : term s) B :
  Σ ;; Γ ⊢ Prod x A B : Type_ ->
  Σ ;; Γ ⊢ A : Type_ /\
  Σ ;; Cons Γ x A ⊢ B : Type_.
Proof.
intros H. apply typing_prod_inv in H. destruct H as (_ & H1 & H2). firstorder.
Qed.

Lemma typing_prod_context_inv Σ {s s'} (Γ : context ∅ s) (Γ' : context s s') T :
  Σ ;; Γ ⊢ prod_context Γ' T : Type_ ->
  Σ ;; (Γ ++ Γ') ⊢ T : Type_.
Proof.
intros H. depind Γ' ; simp app_context prod_context in *.
apply IHΓ' in H. now apply typing_prod_inv' in H.
Qed.

Lemma typing_app_inv_aux {s} Σ Γ t (T : term s) :
  Σ ;; Γ ⊢ t : T ->
  forall f arg, t = App f arg ->
  exists x A B,
    Σ ;; Γ ⊢ f : Prod x A B /\
    Σ ;; Γ ⊢ arg : A /\
    Σ ⊢ T ≡ B[x ::= arg].
Proof.
intros H. induction H ; intros f' arg' Ht ; depelim Ht.
- exists x, A, B. now split3.
- destruct (IHtyping1 f' arg' eq_refl) as (x & A' & B' & Hf & H2 & H3).
  exists x, A', B'. split3 ; auto. now rewrite <-H0, H3.
Qed.

Lemma typing_app_inv {s} Σ Γ f arg (T : term s) :
  Σ ;; Γ ⊢ App f arg : T ->
  exists x A B,
    Σ ;; Γ ⊢ f : Prod x A B /\
    Σ ;; Γ ⊢ arg : A /\
    Σ ⊢ T ≡ B[x ::= arg].
Proof. intros H. eapply typing_app_inv_aux ; eauto. Qed.

Lemma typing_evar_inv {s} Σ Γ ev (T : term s) :
  Σ ;; Γ ⊢ Evar ev : T ->
  exists entry,
    Σ !! ev = Some entry /\
    Σ ⊢ T ≡ wk entry.(evar_type).
Proof.
intros H. depind H.
- exists entry. now split.
- destruct IHtyping1 as (entry & H2 & H3). exists entry.
  split ; auto. now rewrite <-H0.
Qed.

(***********************************************************************)
(** * [inv_typing] tactic *)
(***********************************************************************)

Ltac2 inv_typing (h : ident) : unit :=
  lazy_match! Constr.type (Control.hyp h) with
  | _ ;; _ ⊢ Type_ : _ => apply typing_type_inv in $h
  | _ ;; _ ⊢ Var _ : _ => apply typing_var_inv in $h
  | _ ;; _ ⊢ Prod _ _ _ : Type_ => apply typing_prod_inv' in $h
  | _ ;; _ ⊢ Prod _ _ _ : _ => apply typing_prod_inv in $h
  | _ ;; _ ⊢ prod_context _ _ : Type_ => apply typing_prod_context_inv in $h
  | _ ;; _ ⊢ Lam _ _ _ : _ => apply typing_lam_inv in $h
  | _ ;; _ ⊢ App _ _ : _ => apply typing_app_inv in $h
  | _ ;; _ ⊢ Evar _ : _ => apply typing_evar_inv in $h
  | _ ;; _ ⊢ _ : _ => tactic_failure! "Can't invert this typing derivation"
  | ?x => tactic_failure! "Not a typing derivation: %t" x
  end.

(** [inv_typing in H] tries to invert the typing derivation [H : Σ ;; Γ ⊢ t : T].
    Also accepts several arguments e.g. [inv_typing in H1, H2, H3]. *)
Tactic Notation "inv_typing" "in" ne_ident_list_sep(Hs, ",") :=
  let f := ltac2:(hs |-
    let hs := Option.get (Ltac1.to_list hs) in
    List.iter (fun h => inv_typing (Option.get (Ltac1.to_ident h))) hs)
  in f Hs.

(***********************************************************************)
(** * Well-typed judgement *)
(***********************************************************************)

Definition well_typed (Σ : evar_map) {s} (Γ : context ∅ s) (t : term s) : Prop :=
  exists T, Σ ;; Γ ⊢ t : T.

#[export] Instance well_typed_extend_evm :
  Proper (Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@well_typed).
Proof.
intros Σ Σ' HΣ s Γ ? <- t ? <- (T & Ht). exists T. now rewrite <-HΣ.
Qed.

(***********************************************************************)
(** * Inversion lemmas for [well_typed] *)
(***********************************************************************)

Lemma well_typed_lam {s x} Σ (Γ : context ∅ s) ty body :
  well_typed Σ Γ (Lam x ty body) ->
  well_typed Σ Γ ty /\ well_typed Σ (Cons Γ x ty) body.
Proof.
intros (T & H). apply typing_lam_inv in H. firstorder.
Qed.

Lemma well_typed_prod {s x} Σ (Γ : context ∅ s) a b :
  well_typed Σ Γ (Prod x a b) ->
  well_typed Σ Γ a /\ well_typed Σ (Cons Γ x a) b.
Proof.
intros (T & H). apply typing_prod_inv in H. firstorder.
Qed.

Lemma well_typed_app {s} Σ (Γ : context ∅ s) f arg :
  well_typed Σ Γ (App f arg) ->
  well_typed Σ Γ f /\ well_typed Σ Γ arg.
Proof.
intros (T & H). apply typing_app_inv in H.
destruct H as (f_ty & A & B & Hf & Harg & _). firstorder.
Qed.

Lemma well_typed_apps {s} Σ Γ (t : term s) (us : list (term s)) :
  well_typed Σ Γ (apps t us) ->
  well_typed Σ Γ t /\ Forall (well_typed Σ Γ) us.
Proof.
intros H. induction us in t, H |- *.
- rewrite apps_nil in H. now split.
- rewrite apps_cons in H. apply IHus in H.
  destruct H as (H1 & H2). apply well_typed_app in H1.
  split ; [| constructor] ; firstorder.
Qed.