(** This module defines _reduction flags_ which control which rules
    are allowed when reducing terms or checking for convertibility.
*)

From MetaTheory Require Import Prelude.

(***********************************************************************)
(** * Reduction flags *)
(***********************************************************************)

(** Reduction flags [red_flags] control which rules are allowed in reduction:
    - [beta] controls beta reduction (function application).
*)
Record red_flags := {
  beta : bool
}.

(** All reduction rules enabled. *)
Definition red_flags_all : red_flags :=
  {| beta := true  |}.

(** All reduction rules disabled. *)
Definition red_flags_none : red_flags :=
  {| beta := false |}.

(***********************************************************************)
(** * Inclusion on reduction flags *)
(***********************************************************************)

Record red_flags_incl (f1 f2 : red_flags) : Prop := {
  red_flags_incl_beta : f1.(beta) = true -> f2.(beta) = true
}.

#[export] Instance red_flags_incl_Reflexive : Reflexive red_flags_incl.
Proof. intros f. constructor ; auto. Qed.

#[export] Instance red_flags_incl_Transitive : Transitive red_flags_incl.
Proof.
intros f1 f2 f3 H1 H2. constructor ; intros H ; now apply H1, H2 in H.
Qed.

Lemma red_flags_incl_none f :
  red_flags_incl red_flags_none f.
Proof. constructor ; cbn ; intros H ; depelim H. Qed.

Lemma red_flags_incl_all f :
  red_flags_incl f red_flags_all.
Proof. constructor ; cbn ; auto. Qed.