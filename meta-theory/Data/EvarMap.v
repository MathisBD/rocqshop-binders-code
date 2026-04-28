(** This module defines evar maps.
    An advantage of the definition of evar maps as done here is _extensionality_:
    to prove that two evars maps are equal, it suffices to prove pointwise equality.

    Common notations on evar-maps:
    - [Σ !! ev] looks up the evar info for [ev] in the evar-map [ev].
    - [Σ[ ev with info ]] sets the evar-info associated with [ev] to [info]
      in the evar-map [Σ].
    - [Σ ⊑ Σ'] means that the evar-map [Σ] is included in the evar-map [Σ'].
*)

From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.Term.

(***********************************************************************)
(** * Evar info *)
(***********************************************************************)

(** [evar_info] records the information pertaining to an evar: its type
    and optionally its definition. *)
Record evar_info := Vmk_evar_info {
  evar_type : term ∅ ;
  evar_def : option (term ∅)
}.

Derive NoConfusion NoConfusionHom for evar_info.

(***********************************************************************)
(** * Evar-map definition and basic operations *)
(***********************************************************************)

(** The view of the evar map used in proofs.

    We say that an evar is:
    - "absent" if its entry is [None].
    - "present" if its entry is [Some _].
    - "undefined" if it is present and has no definition.
    - "defined" if it is present and has a definition.*)
Record evar_map := {
  evar_map_func : evar_id -> option evar_info
}.

(** Lookup the information for an evar in an evar-map. *)
Definition lookup_evar (Σ : evar_map) (ev : evar_id) : option evar_info :=
  evar_map_func Σ ev.

Notation "Σ !! ev" := (lookup_evar Σ ev)
  (no associativity, at level 40, format "Σ  !!  ev").

(** [set_evar Σ ev info] replaces the evar info of [ev] with [info] in
    the evar-map [Σ]. *)
Definition set_evar (Σ : evar_map) (ev : evar_id) (info : evar_info) : evar_map := {|
  evar_map_func := fun ev' => if evar_id_eqb ev ev' then Some info else Σ !! ev'
|}.

Notation "Σ [ ev 'with' info ]" := (set_evar Σ ev info)
  (at level 10, format "Σ [  ev  'with'  info  ]").

Lemma set_evar_same Σ x info :
  Σ[ x with info ] !! x = Some info.
Proof.
unfold set_evar, lookup_evar. cbn. now rewrite evar_id_eqb_same.
Qed.

Lemma set_evar_other Σ x y info :
  x <> y ->
  Σ[ x with info ] !! y = Σ !! y.
Proof.
intros H. unfold set_evar, lookup_evar. cbn.
now rewrite evar_id_eqb_diff by assumption.
Qed.

(** Check if an evar is present in an evar-map. *)
Definition is_evar_present (Σ : evar_map) (ev : evar_id) : Prop :=
  match Σ !! ev with Some _ => True | _ => False end.

(** Check if an evar is undefined (but still present) in an evar-map. *)
Definition is_evar_undefined (Σ : evar_map) (ev : evar_id) : Prop :=
  match Σ !! ev with
  | Some {| evar_type := _ ; evar_def := None |} => True
  | _ => False
  end.

(** Check if an evar is defined in an evar-map. *)
Definition is_evar_defined (Σ : evar_map) (ev : evar_id) : Prop :=
  match Σ !! ev with
  | Some {| evar_type := _ ; evar_def := Some _ |} => True
  | _ => False
  end.

(***********************************************************************)
(** * Inclusion on evar-maps *)
(***********************************************************************)

(** Inclusion on (optional) evar infos. [None] means that the corresponding
    evar is absent from the evar-map. *)
Inductive einfo_incl : option evar_info -> option evar_info -> Prop :=
(** If the first evar is absent from the evar map,
    the second evar can have any entry associated to it. *)
| einfo_incl_absent info_opt :
    einfo_incl None info_opt
(** If the first evar is undefined, the second evar must be present and have the same type. *)
| einfo_incl_undef ty def_opt :
    einfo_incl (Some (Vmk_evar_info ty None)) (Some (Vmk_evar_info ty def_opt))
(** If the first evar is defined, the second evar must be defined and have the same type
    and definition. *)
| einfo_incl_def ty def :
    einfo_incl (Some (Vmk_evar_info ty (Some def))) (Some (Vmk_evar_info ty (Some def))).

Derive Signature for einfo_incl.

#[export] Instance einfo_incl_Reflexive : Reflexive einfo_incl.
Proof. intros [[ty [def | ]] | ] ; constructor. Qed.

#[export] Instance einfo_incl_Transitive : Transitive einfo_incl.
Proof.
intros e1 e2 e3 H1 H2. depelim H1 ; depelim H2 ; constructor.
Qed.

(** Inclusion on evar maps, also written [Σ ⊑ Σ']. *)
Record Vevm_incl (Σ Σ' : evar_map) : Prop := {
  Vevm_incl_prop : forall ev, einfo_incl (Σ !! ev) (Σ' !! ev)
}.

Notation "Σ1 ⊑ Σ2" := (Vevm_incl Σ1 Σ2)
  (at level 30, no associativity).

#[export] Instance evm_incl_Reflexive : Reflexive Vevm_incl.
Proof. intros Σ. constructor. intros ev. reflexivity. Qed.

#[export] Instance evm_incl_Transitive : Transitive Vevm_incl.
Proof.
intros Σ1 Σ2 Σ3 H1 H2. constructor. intros ev. transitivity (Σ2 !! ev).
- apply H1.
- apply H2.
Qed.

Lemma set_evar_incl Σ x info :
  Σ ⊑ Σ[ x with info ] <->
  einfo_incl (Σ !! x) (Some info).
Proof.
split.
- intros [H]. specialize (H x). now rewrite set_evar_same in H.
- intros H. constructor. intros y. destruct (evar_id_eqb_spec x y).
  + subst. rewrite set_evar_same. assumption.
  + rewrite set_evar_other by assumption. reflexivity.
Qed.

(***********************************************************************)
(** * [evm_ext] tactic *)
(***********************************************************************)

(** Extensionality lemma for evar maps. *)
Lemma evm_ext (Σ Σ' : evar_map) :
  (forall ev, Σ !! ev = Σ' !! ev) ->
  Σ = Σ'.
Proof.
intros H. destruct Σ as [Σf]. destruct Σ' as [Σf']. f_equal.
fun_ext ev. apply H.
Qed.

(** [evm_ext] is the analog of [fun_ext] but for evar-maps. *)
Tactic Notation "evm_ext" ident(x) :=
  apply evm_ext ; intro x.