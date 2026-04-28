(** This module develops a basic theory of binary relations.
    Most notably we prove that the diamond property implies confluence. *)

From MetaTheory Require Import Prelude.

(***********************************************************************)
(** * Reflexive-transitive closure of a relation *)
(***********************************************************************)

(** [refl_trans_clos R] is the reflexive-transitive closure of [R]. *)
Inductive refl_trans_clos {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_trans_refl x : refl_trans_clos R x x
| refl_trans_step x y z :
    refl_trans_clos R x y -> R y z -> refl_trans_clos R x z.

Derive Signature for refl_trans_clos.

(** The closure is reflexive. *)
#[export] Instance refl_trans_clos_Reflexive {A} (R : A -> A -> Prop) :
  Reflexive (refl_trans_clos R).
Proof. intros x. apply refl_trans_refl. Qed.

(** The closure is transitive. *)
#[export] Instance refl_trans_clos_Transitive {A} (R : A -> A -> Prop) :
  Transitive (refl_trans_clos R).
Proof.
intros x y z H1 H2. induction H2 in x, H1 |- *.
- assumption.
- eapply refl_trans_step.
  + eapply IHrefl_trans_clos. assumption.
  + assumption.
Qed.

(** The closure contains the relation [R]. *)
Lemma refl_trans_clos_one {A} (R : A -> A -> Prop) x y :
  R x y -> refl_trans_clos R x y.
Proof.
intros H. eapply refl_trans_step ; [reflexivity | assumption].
Qed.

(** The closure is the smallest reflexive-transitive relation containing [R]. *)
Lemma refl_trans_clos_smallest {A} (R R' : A -> A -> Prop) :
  Reflexive R' ->
  Transitive R' ->
  (forall x y, R x y -> R' x y) ->
  forall x y, refl_trans_clos R x y -> R' x y.
Proof.
intros H1 H2 H3 x y H. induction H.
- reflexivity.
- transitivity y.
  + assumption.
  + now apply H3.
Qed.

(** Alternate induction principle on [refl_trans_clos] which makes
    some proofs easier. *)
Lemma refl_trans_clos_ind' {A} (R P : A -> A -> Prop)
  (Hrefl : forall t, P t t)
  (Hstep : forall t1 t2 t3,
      R t1 t2 ->
      refl_trans_clos R t2 t3 ->
      P t2 t3 ->
      P t1 t3) :
  forall t1 t2, refl_trans_clos R t1 t2 -> P t1 t2.
Proof.
enough (forall t1 t2,
  refl_trans_clos R t1 t2 ->
  refl_trans_clos R t1 t2 /\ P t1 t2) by firstorder.
apply refl_trans_clos_smallest
  with (R' := fun t1 t2 => refl_trans_clos R t1 t2 /\ P t1 t2).
- intros x. split ; [reflexivity | apply Hrefl].
- intros x1 x2 x3 [H1 H2] [H3 H4]. split ; [etransitivity ; eauto |].
  clear H2. induction H1 in x3, H3, H4 |- *.
  + assumption.
  + apply IHrefl_trans_clos.
    * transitivity z ; [|assumption]. now apply refl_trans_clos_one.
    * apply Hstep with z ; assumption.
- intros x1 x2 H. split ; [now apply refl_trans_clos_one |].
  now apply Hstep with x2.
Qed.

Lemma refl_trans_clos_incl {A} (R R' : A -> A -> Prop) :
  (forall x y, R x y -> refl_trans_clos R' x y) ->
  forall x y, refl_trans_clos R x y -> refl_trans_clos R' x y.
Proof.
intros H x y H'. induction H'.
- reflexivity.
- transitivity y ; [assumption|]. now apply H.
Qed.

(***********************************************************************)
(** * Diamond property implies confluence *)
(***********************************************************************)

Definition diamond {A} (R1 R2 : A -> A -> Prop) (x : A) : Prop :=
  forall y1 y2,
    R1 x y1 ->
    R2 x y2 ->
    exists z, R2 y1 z /\ R1 y2 z.

Lemma diamond_sym {A} (R1 R2 : A -> A -> Prop) x :
  diamond R1 R2 x <-> diamond R2 R1 x.
Proof.
enough (forall (R1 R2 : A -> A -> Prop),
  diamond R1 R2 x -> diamond R2 R1 x) by firstorder.
clear R1 R2. intros R1 R2 H. unfold diamond in *.
intros y1 y2 H1 H2. specialize (H y2 y1 H2 H1). firstorder.
Qed.

Lemma diamond_clos_left {A} (R R' : A -> A -> Prop) :
  (forall t, diamond R R' t) ->
  (forall t, diamond (refl_trans_clos R) R' t).
Proof.
intros Hdiamond t x y Hx Hy.
induction Hx as [t | t x1 x2 Hx1 IH Hx2].
- exists y. now split.
- destruct (IH Hy) as (u & Hu1 & Hu2).
  specialize (Hdiamond _ _ _ Hx2 Hu1).
  destruct Hdiamond as (v & Hv1 & Hv2). exists v. split.
  + assumption.
  + transitivity u ; [assumption |]. now apply refl_trans_clos_one.
Qed.

(** The diamond property implies confluence. *)
Lemma diamond_confluence {A} (R : A -> A -> Prop) :
  (forall x, diamond R R x) ->
  (forall x, diamond (refl_trans_clos R) (refl_trans_clos R) x).
Proof.
intros H. apply diamond_clos_left. intros t.
rewrite diamond_sym. revert t.
apply diamond_clos_left. assumption.
Qed.
