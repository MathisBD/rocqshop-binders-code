From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Conversion.SubstConversion.

(***********************************************************************)
(** * Conversion relation on contexts *)
(***********************************************************************)

(** [cconv flags flags Σ Γ Γ'] means that contexts [Γ] and [Γ'] are convertible
    in evar-map [Σ]. *)
Inductive cconv (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cconv_nil : cconv flags Σ Nil Nil

| cconv_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ≡{flags} ty' ->
    cconv flags Σ Γ Γ' ->
    cconv flags Σ (Cons Γ x ty) (Cons Γ' x ty').

Derive Signature for cconv.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

#[export] Instance cconv_Reflexive s flags Σ :
  Reflexive (@cconv flags Σ s).
Proof.
intros Γ. induction Γ ; constructor.
- reflexivity.
- assumption.
Qed.

#[export] Instance cconv_Symmetric s flags Σ :
  Symmetric (@cconv flags Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now symmetry.
- assumption.
Qed.

#[export] Instance cconv_Transitive s flags Σ :
  Transitive (@cconv flags Σ s).
Proof.
intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
- reflexivity.
- constructor.
+ now rewrite H.
  + now apply IHcconv.
Qed.

#[export] Instance cconv_of_cred1 s flags Σ :
  subrelation (@cred1 flags Σ s) (@cconv flags Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

#[export] Instance cconv_of_cred s flags Σ :
  subrelation (@cred flags Σ s) (@cconv flags Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- assumption.
Qed.

(** Due to technical limitations of setoid rewriting we need to split
    the [Proper] instance for [Cons] in two parts. *)

#[export] Instance ccons_congr_Cons_1 s flags Σ :
  Proper (cconv flags Σ ==> ∀ x, eq ==> cconv flags Σ) (@Cons ∅ s).
Proof. intros Γ Γ' HΓ x ty ? <-. now constructor. Qed.

#[export] Instance ccons_congr_Cons_2 s flags Σ Γ x :
  Proper (conv flags Σ ==> cconv flags Σ) (@Cons ∅ s Γ x).
Proof. intros ty ty' Hty. now constructor. Qed.

#[export] Instance cconv_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@cconv).
Proof.
intros f f' Hf Σ Σ' HΣ s Γ ? <- Γ' ? <- HΓ. induction HΓ ; constructor.
- now rewrite <-Hf, <-HΣ.
- firstorder.
Qed.

(***********************************************************************)
(** * Church-Rosser lemma *)
(***********************************************************************)

(** Because a context is a finite collection of terms, the Church-Rosser
    property for contexts follows from the Church-Rosser property for terms. *)
Lemma church_rosser_context {s flags Σ} (Γ Γ' : context ∅ s) :
  cconv flags Σ Γ Γ' ->
  exists Δ, cred flags Σ Γ Δ /\ cred flags Σ Γ' Δ.
Proof.
intros H. induction H.
- exists Nil. now split.
- apply church_rosser in H. destruct H as (u & Hu1 & Hu2).
  destruct IHcconv as (Δ & HΔ1 & HΔ2).
  exists (Cons Δ x u). split.
  + now constructor.
  + now constructor.
Qed.

(***********************************************************************)
(** * Lemmas about context conversion *)
(***********************************************************************)

#[export] Instance lookup_context_cconv {s flags Σ} (i : index s) :
  Proper (cconv flags Σ ==> conv flags Σ) (@lookup_context s i).
Proof.
intros Γ Γ' HΓ. induction HΓ ; depelim i ; simp lookup_context ; simp_subst.
- now rewrite H.
- now rewrite IHHΓ.
Qed.
