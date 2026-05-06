From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Reduction.Confluence.

(***********************************************************************)
(** * Conversion relation on terms *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ≡{ f } u"
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' '[hv' Σ  ⊢  t '/  ' ≡{ f } ']' '/    ' u ']'").

(** We define conversion as the reflexive-symmetric-transitive closure of
    one-step reduction. *)
Inductive conv (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=
| conv_of_red1 t1 t2 :
    Σ ⊢ t1 ~>{flags} t2 -> Σ ⊢ t1 ≡{flags} t2
| conv_refl t :
    Σ ⊢ t ≡{flags} t
| conv_sym t1 t2 :
    Σ ⊢ t1 ≡{flags} t2 -> Σ ⊢ t2 ≡{flags} t1
| conv_trans t1 t2 t3 :
    Σ ⊢ t1 ≡{flags} t2 ->
    Σ ⊢ t2 ≡{flags} t3 ->
    Σ ⊢ t1 ≡{flags} t3

where "Σ ⊢ t ≡{ f } u" := (conv f Σ t u).

Derive Signature for conv.

(** [Σ ⊢ t ≡ u] is conversion with all reduction flags enabled. *)
Notation "Σ ⊢ t ≡ u" := (conv red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ≡ '/    ' u ']'").

(** [Σ ⊢ t ≡ev u] is conversion with no reduction flags enabled:
    only evar expansion is allowed. *)
Notation "Σ ⊢ t ≡ev u" := (conv red_flags_none Σ t u)
  (at level 50, no associativity, t at next level, u at next level,
   format "'[hv' Σ  ⊢  t  ≡ev '/    ' u ']'").

(***********************************************************************)
(** * Typeclass instances for setoid rewriting *)
(***********************************************************************)

#[export] Instance conv_Reflexive s flags Σ :
  Reflexive (@conv flags Σ s).
Proof. intros t. apply conv_refl. Qed.

#[export] Instance conv_Symmetric s flags Σ :
  Symmetric (@conv flags Σ s).
Proof. intros t1 t2. apply conv_sym. Qed.

#[export] Instance conv_Transitive s flags Σ :
  Transitive (@conv flags Σ s).
Proof. intros t. apply conv_trans. Qed.

Lemma conv_of_red {s flags Σ} (t u : term s) :
  Σ ⊢ t ~~>{flags} u -> Σ ⊢ t ≡{flags} u.
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHred. now apply conv_of_red1.
Qed.

#[export] Instance subrelation_red1_conv s flags Σ :
  subrelation (@red1 flags Σ s) (@conv flags Σ s).
Proof. intros t u H. now apply conv_of_red1. Qed.

#[export] Instance subrelation_red1_conv_flip s flags Σ :
  subrelation (Basics.flip (@red1 flags Σ s)) (@conv flags Σ s).
Proof.
intros t u H. unfold Basics.flip in H. symmetry.
now apply conv_of_red1.
Qed.

#[export] Instance subrelation_red_conv s flags Σ :
  subrelation (@red flags Σ s) (@conv flags Σ s).
Proof. intros t u H. now apply conv_of_red. Qed.

#[export] Instance subrelation_red_conv_flip s flags Σ :
  subrelation (Basics.flip (@red flags Σ s)) (@conv flags Σ s).
Proof.
intros t u H. unfold Basics.flip in H. symmetry.
now apply conv_of_red.
Qed.

#[export] Instance conv_extend_flags_evm :
  Proper (red_flags_incl ==> Vevm_incl ==> ∀ s, eq ==> eq ==> impl) (@conv).
Proof.
intros f f' Hf Σ Σ' HΣ s t ? <- t' ? <- H. induction H.
- rewrite Hf, HΣ in H. now rewrite H.
- reflexivity.
- now symmetry.
- etransitivity ; eauto.
Qed.

(***********************************************************************)
(** * Church-Rosser lemma *)
(***********************************************************************)

(** The church-rosser lemma is a direct consequence of the confluence
    property of [red]. *)
Lemma church_rosser {s flags Σ} (t1 t2 : term s) :
  Σ ⊢ t1 ≡{flags} t2 ->
  exists u, Σ ⊢ t1 ~~>{flags} u /\ Σ ⊢ t2 ~~>{flags} u.
Proof.
intros H. depind H.
- exists t2. split ; [now apply red_of_red1 | reflexivity].
- exists t. now split.
- destruct IHconv as (u & H1 & H2). exists u. now split.
- destruct IHconv1 as (u1 & H1 & H2).
  destruct IHconv2 as (u2 & H3 & H4).
  destruct (red_confluence t2 u1 u2 H2 H3) as (u & H5 & H6).
  exists u. split ; etransitivity ; eassumption.
Qed.

(***********************************************************************)
(** * Congruence lemmas *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope} {flags : red_flags} {Σ : evar_map}.

  Lemma conv_beta x (ty : term s) body arg :
    flags.(beta) = true ->
    Σ ⊢ App (Lam x ty body) arg ≡{flags} body[x ::= arg].
  Proof. intros H. now rewrite red_beta. Qed.

  #[export] Instance conv_lam_congr x :
    Proper (conv flags Σ ==> conv flags Σ ==> conv flags Σ) (@Lam s x).
  Proof.
  intros ty ty' Hty body body' Hbody.
  transitivity (Lam x ty' body).
  - clear Hbody. induction Hty.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Hty. induction Hbody.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  #[export] Instance conv_prod_congr x :
    Proper (conv flags Σ ==> conv flags Σ ==> conv flags Σ) (@Prod s x).
  Proof.
  intros a a' Ha b b' Hb.
  transitivity (Prod x a' b).
  - clear Hb. induction Ha.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Ha. induction Hb.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  #[export] Instance conv_app_congr :
    Proper (conv flags Σ ==> conv flags Σ ==> conv flags Σ) (@App s).
  Proof.
  intros f f' Hf arg arg' Harg. transitivity (App f' arg).
  - clear arg' Harg. induction Hf.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Hf. induction Harg.
    + now rewrite H.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  Lemma conv_apps_congr_l :
    Proper (conv flags Σ ==> eq ==> conv flags Σ) (@apps s).
  Proof.
  intros f f' Hf args args' <-. induction Hf.
  - now rewrite H.
  - reflexivity.
  - now symmetry.
  - etransitivity ; eauto.
  Qed.

  #[export] Instance conv_apps_congr :
    Proper (conv flags Σ ==> Forall2 (conv flags Σ) ==> conv flags Σ) (@apps s).
  Proof.
  intros f f' Hf args args' Hargs. transitivity (apps f' args).
  - now apply conv_apps_congr_l.
  - clear f Hf. induction Hargs in f' |- *.
    + reflexivity.
    + rewrite !apps_cons. rewrite IHHargs.
      apply conv_apps_congr_l ; [| reflexivity]. now rewrite H.
  Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas *)
(***********************************************************************)

(** We prove inversion lemmas for lambda abstractions and products
    (aka injectivity of π-types). These lemmas follow from the Church-Rosser
    property, and from the fact that reducing a lambda abstraction
    (resp. a product) can only produce another lambda abstraction
    (resp. product). *)

Section InversionLemmas.
  Context {s : scope} {flags : red_flags} {Σ : evar_map}.

  Lemma conv_lam_inv x (ty ty' : term s) body body' :
    Σ ⊢ Lam x ty body ≡{flags} Lam x ty' body' ->
    Σ ⊢ ty ≡{flags} ty' /\ Σ ⊢ body ≡{flags} body'.
  Proof.
  intros H. apply church_rosser in H.
  destruct H as (t & H1 & H2).
  inv_red in H1, H2.
  destruct H1 as (ty1' & body1' & -> & Hty1 & Hbody1).
  destruct H2 as (ty2' & body2' & Heq & Hty2 & Hbody2).
  depelim Heq. split.
  - transitivity ty1'.
    + apply conv_of_red, Hty1.
    + symmetry. apply conv_of_red, Hty2.
  - transitivity body1'.
    + apply conv_of_red, Hbody1.
    + symmetry. apply conv_of_red, Hbody2.
  Qed.

  Lemma conv_prod_inv x (a a' : term s) b b' :
    Σ ⊢ Prod x a b ≡{flags} Prod x a' b' ->
    Σ ⊢ a ≡{flags} a' /\ Σ ⊢ b ≡{flags} b'.
  Proof.
  intros H. apply church_rosser in H.
  destruct H as (t & H1 & H2).
  inv_red in H1, H2.
  destruct H1 as (a1' & b1' & -> & Ha1 & Hb1).
  destruct H2 as (a2' & b2' & Heq & Ha2 & Hb2).
  depelim Heq. split.
  - transitivity a1'.
    + apply conv_of_red, Ha1.
    + symmetry. apply conv_of_red, Ha2.
  - transitivity b1'.
    + apply conv_of_red, Hb1.
    + symmetry. apply conv_of_red, Hb2.
  Qed.

End InversionLemmas.

(***********************************************************************)
(** * [inv_conv] tactic *)
(***********************************************************************)

Ltac2 inv_conv (h : ident) : unit :=
  lazy_match! Constr.type (Control.hyp h) with
  | _ ⊢ Lam _ _ _ ≡{_} Lam _ _ _ => apply conv_lam_inv in $h
  | _ ⊢ Prod _ _ _ ≡{_} Prod _ _ _ => apply conv_prod_inv in $h
  | _ ⊢ _ ≡{_} _ => tactic_failure! "Can't invert this conversion derivation"
  | ?x => tactic_failure! "Not a conversion derivation: %t" x
  end.

(** [inv_conv in H] tries to invert the conversion derivation [H : Σ ⊢ t ≡{flags} t'].
    Also accepts several arguments e.g. [inv_conv in H1, H2, H3]. *)
Tactic Notation "inv_conv" "in" ne_ident_list_sep(Hs, ",") :=
  let f := ltac2:(hs |-
    let hs := Option.get (Ltac1.to_list hs) in
    List.iter (fun h => inv_conv (Option.get (Ltac1.to_ident h))) hs)
  in f Hs.
