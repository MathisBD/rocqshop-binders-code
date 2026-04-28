From MetaTheory Require Import Prelude.
From MetaTheory Require Export Theory.Typing.TermTyping.

(***********************************************************************)
(** * Typing evar-maps *)
(***********************************************************************)

Inductive typing_evar_info (Σ : evar_map) : evar_info -> Prop :=

| typing_evar_undefined ty :
    Σ ;; Nil ⊢ ty : Type_ ->
    typing_evar_info Σ (Vmk_evar_info ty None)

| typing_evar_defined ty def :
    Σ ;; Nil ⊢ ty : Type_ ->
    Σ ;; Nil ⊢ def : ty ->
    typing_evar_info Σ (Vmk_evar_info ty (Some def)).

Derive Signature for typing_evar_info.

(** An evar-map is well-typed if all its evars have well-typed evar-infos.
    We do _not_ enforce that the evar-map is acyclic. *)
Definition typing_evar_map (Σ : evar_map) :=
  forall ev entry, Σ !! ev = Some entry -> typing_evar_info Σ entry.

(** We mark [typing_evar_map] because there is a variable
    [HΣ : typing_evar_map Σ] in the proof context most of the time,
    which can be picked up by typeclass resolution. *)
Existing Class typing_evar_map.

(***********************************************************************)
(** * Properties of evar-map typing *)
(***********************************************************************)

#[export] Instance typing_evar_info_incl :
  Proper (Vevm_incl ==> eq ==> impl) typing_evar_info.
Proof.
intros Σ Σ' HΣ info ? <- H. depelim H.
- constructor. now rewrite <-HΣ.
- constructor ; now rewrite <-HΣ.
Qed.

Lemma typing_evar_type Σ entry :
  typing_evar_info Σ entry ->
  Σ ;; Nil ⊢ entry.(evar_type) : Type_.
Proof.
intros H. destruct H ; cbn ; assumption.
Qed.

Lemma typing_set_evar Σ x info :
  einfo_incl (Σ !! x) (Some info) ->
  typing_evar_info Σ info ->
  typing_evar_map Σ ->
  typing_evar_map (Σ[ x with info ]).
Proof.
intros Hx Hinfo HΣ y entry Hy.
assert (Σ ⊑ set_evar Σ x info) as <-. { now rewrite set_evar_incl. }
destruct (evar_id_eqb_spec x y).
- subst. rewrite set_evar_same in Hy. now depelim Hy.
- rewrite set_evar_other in Hy by assumption. apply HΣ in Hy. assumption.
Qed.
