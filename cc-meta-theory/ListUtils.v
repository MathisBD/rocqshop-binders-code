(** This file defines utilities on lists, notably the predicates [Forall2]
    and [Forall3] which generalize [Forall] to multiple lists,
    and proves many basic lemmas. *)

From Stdlib Require Import List Lia Morphisms.
From Equations Require Import Equations.
Import ListNotations.

(***********************************************************************)
(** * Miscellaneous functions and lemmas. *)
(***********************************************************************)

Lemma map_nil {A B} (f : A -> B) :
  map f [] = [].
Proof. reflexivity. Qed.

Derive Signature for Forall Exists.

Lemma Forall_consequence {A} (P Q : A -> Prop) (xs : list A) :
  (forall x, P x -> Q x) ->
  Forall P xs ->
  Forall Q xs.
Proof. intros Himpl H. depind H ; constructor ; auto. Qed.

(***********************************************************************)
(** * [snoc] function. *)
(***********************************************************************)

(** [snoc xs] decomposes the list [xs = [x_1; x_2 ... x_n]] into its
    first elements [[x_1 ... x_n-1]] and its last element [x_n].
    Returns [None] if [xs] is empty. *)
Fixpoint snoc {A} (xs : list A) : option (list A * A) :=
  match xs with
  | [] => None
  | x :: xs =>
    match snoc xs with
    | None => Some ([], x)
    | Some (ys, y) => Some (x :: ys, y)
    end
  end.

Lemma snoc_None {A} (xs : list A) :
  snoc xs = None ->
  xs = [].
Proof.
intros H. depelim xs.
- reflexivity.
- cbn in H. destruct (snoc xs) as [[] |] ; depelim H.
Qed.

Lemma snoc_Some {A} (xs : list A) ys y :
  snoc xs = Some (ys, y) ->
  xs = ys ++ [y].
Proof.
intros H. depind xs.
- cbn in H. depelim H.
- cbn in H. destruct (snoc xs) as [[zs z] |] eqn:Hsnoc ; depelim H.
  + cbn. f_equal. now apply IHxs.
  + cbn. f_equal. now apply snoc_None in Hsnoc.
Qed.

(***********************************************************************)
(** * Predicate [OnOne2]. *)
(***********************************************************************)

(** [OnOne2 P xs ys] means that the lists [xs] and [ys] are equal except at
    exactly one position, and at these positions the elements are related by [P]. *)
Inductive OnOne2 {A} (P : A -> A -> Prop) : list A -> list A -> Prop :=
| OnOne2_head x x' xs : P x x' -> OnOne2 P (x :: xs) (x' :: xs)
| OnOne2_tail x xs xs' : OnOne2 P xs xs' -> OnOne2 P (x :: xs) (x :: xs').

Derive Signature for OnOne2.

Lemma OnOne2_length {A} (P : A -> A -> Prop) xs ys :
  OnOne2 P xs ys ->
  length xs = length ys.
Proof. intros H. induction H ; cbn ; lia. Qed.

Lemma OnOne2_app_l {A} (P : A -> A -> Prop) xs xs' ys :
  OnOne2 P xs xs' ->
  OnOne2 P (xs ++ ys) (xs' ++ ys).
Proof.
intros H. induction H ; cbn.
- now apply OnOne2_head.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_app_r {A} (P : A -> A -> Prop) xs ys ys' :
  OnOne2 P ys ys' ->
  OnOne2 P (xs ++ ys) (xs ++ ys').
Proof.
intros H. induction xs ; cbn.
- assumption.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_consequence {A} (P Q : A -> A -> Prop) xs ys :
  (forall x y, P x y -> Q x y) ->
  OnOne2 P xs ys ->
  OnOne2 Q xs ys.
Proof.
intros H H'. induction H'.
- apply OnOne2_head. auto.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_map {A A'} (P : A' -> A' -> Prop) (f : A -> A') xs ys :
  OnOne2 (fun x y => P (f x) (f y)) xs ys ->
  OnOne2 P (map f xs) (map f ys).
Proof.
intros H. depind H ; cbn.
- now constructor.
- now constructor.
Qed.

(***********************************************************************)
(** * Predicate [Forall2]. *)
(***********************************************************************)

(** [Forall2 P xs ys] means that [P] holds on every element of [xs] and [ys].
    In particular [xs] and [ys] must have the same length. *)
Inductive Forall2 {A B} (P : A -> B -> Prop) : list A -> list B -> Prop :=
| Forall2_nil : Forall2 P [] []
| Forall2_cons x xs y ys : P x y -> Forall2 P xs ys -> Forall2 P (x :: xs) (y :: ys).

Derive Signature for Forall2.

Lemma Forall2_length {A B} (P : A -> B -> Prop) xs ys :
  Forall2 P xs ys ->
  length xs = length ys.
Proof. intros H ; induction H ; cbn ; lia. Qed.

Lemma Forall2_app {A B} (P : A -> B -> Prop) xs xs' ys ys' :
  Forall2 P xs ys ->
  Forall2 P xs' ys' ->
  Forall2 P (xs ++ xs') (ys ++ ys').
Proof.
intros H1 H2. induction H1 ; cbn.
- assumption.
- now constructor.
Qed.

Lemma Forall2_consequence {A B} (P Q : A -> B -> Prop) xs ys :
  (forall x y, P x y -> Q x y) ->
  Forall2 P xs ys ->
  Forall2 Q xs ys.
Proof. intros H H'. induction H' ; constructor ; auto. Qed.

#[export] Instance Forall2_Reflexive {A} (P : A -> A -> Prop) {H : Reflexive P} :
  Reflexive (Forall2 P).
Proof. intros xs. induction xs ; now constructor. Qed.

Lemma Forall2_of_OnOne2 {A} (P : A -> A -> Prop) xs ys {H : Reflexive P} :
  OnOne2 P xs ys ->
  Forall2 P xs ys.
Proof. intros H'. induction H' ; now constructor. Qed.

Lemma Forall2_map_1 {A0 A B} (P : A -> B -> Prop) (f : A0 -> A) xs ys :
  Forall2 P (map f xs) ys <->
  Forall2 (fun x y => P (f x) y) xs ys.
Proof.
split ; intros H ; depind H.
- destruct xs ; [| depelim H]. constructor.
- destruct xs0 ; [depelim H1 |]. cbn in H1. depelim H1. constructor.
  + assumption.
  + apply IHForall2. reflexivity.
- constructor.
- now constructor.
Qed.

Lemma Forall2_map_2 {A B0 B} (P : A -> B -> Prop) (f : B0 -> B) xs ys :
  Forall2 P xs (map f ys) <->
  Forall2 (fun x y => P x (f y)) xs ys.
Proof.
split ; intros H ; depind H.
- destruct ys ; [| depelim H]. constructor.
- destruct ys0 ; [depelim H1 |]. cbn in H1. depelim H1. constructor.
  + assumption.
  + apply IHForall2. reflexivity.
- constructor.
- now constructor.
Qed.

Lemma Forall2_map {A0 A B0 B} (P : A -> B -> Prop) (f : A0 -> A) (g : B0 -> B) xs ys :
  Forall2 P (map f xs) (map g ys) <->
  Forall2 (fun x y => P (f x) (g y)) xs ys.
Proof.
rewrite Forall2_map_1, Forall2_map_2. reflexivity.
Qed.

(***********************************************************************)
(** * Predicate [Forall3]. *)
(***********************************************************************)

(** [Forall3 P xs ys zs] means that [P] holds on every element of [xs], [ys], and [zs].
    In particular [xs], [ys], and [zs] must have the same length. *)
Inductive Forall3 {A B C : Type} (P : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 P [] [] []
| Forall3_cons x xs y ys z zs : P x y z -> Forall3 P xs ys zs -> Forall3 P (x :: xs) (y :: ys) (z :: zs).

Derive Signature for Forall3.

Lemma Forall3_length {A B C} (P : A -> B -> C -> Prop) xs ys zs :
  Forall3 P xs ys zs ->
  length xs = length ys /\ length ys = length zs.
Proof. intros H ; induction H ; cbn ; lia. Qed.

Lemma Forall3_app {A B C} (P : A -> B -> C -> Prop) xs xs' ys ys' zs zs' :
  Forall3 P xs ys zs ->
  Forall3 P xs' ys' zs' ->
  Forall3 P (xs ++ xs') (ys ++ ys') (zs ++ zs').
Proof.
intros H1 H2. induction H1 ; cbn.
- assumption.
- now constructor.
Qed.

Lemma Forall3_consequence {A B C} (P Q : A -> B -> C -> Prop) xs ys zs :
  (forall x y z, P x y z -> Q x y z) ->
  Forall3 P xs ys zs ->
  Forall3 Q xs ys zs.
Proof. intros H H'. induction H' ; constructor ; auto. Qed.

Lemma Forall3_map_1 {A0 A B C} (P : A -> B -> C -> Prop) (f : A0 -> A) xs ys zs :
  Forall3 P (map f xs) ys zs <->
  Forall3 (fun x y z => P (f x) y z) xs ys zs.
Proof.
split ; intros H ; depind H.
- destruct xs ; [| depelim H]. constructor.
- destruct xs0 ; [depelim H1 |]. cbn in H1. depelim H1. constructor.
  + assumption.
  + apply IHForall3. reflexivity.
- constructor.
- now constructor.
Qed.

Lemma Forall3_map_2 {A B0 B C} (P : A -> B -> C -> Prop) (f : B0 -> B) xs ys zs :
  Forall3 P xs (map f ys) zs <->
  Forall3 (fun x y z => P x (f y) z) xs ys zs.
Proof.
split ; intros H ; depind H.
- destruct ys ; [| depelim H]. constructor.
- destruct ys0 ; [depelim H1 |]. cbn in H1. depelim H1. constructor.
  + assumption.
  + apply IHForall3. reflexivity.
- constructor.
- now constructor.
Qed.

Lemma Forall3_map_3 {A B C0 C} (P : A -> B -> C -> Prop) (f : C0 -> C) xs ys zs :
  Forall3 P xs ys (map f zs) <->
  Forall3 (fun x y z => P x y (f z)) xs ys zs.
Proof.
split ; intros H ; depind H.
- destruct zs ; [| depelim H]. constructor.
- destruct zs0 ; [depelim H1 |]. cbn in H1. depelim H1. constructor.
  + assumption.
  + apply IHForall3. reflexivity.
- constructor.
- now constructor.
Qed.

Lemma Forall3_map {A0 A B0 B C0 C} (P : A -> B -> C -> Prop)
(f : A0 -> A) (g : B0 -> B) (h : C0 -> C) xs ys zs :
  Forall3 P (map f xs) (map g ys) (map h zs) <->
  Forall3 (fun x y z => P (f x) (g y) (h z)) xs ys zs.
Proof.
rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3. reflexivity.
Qed.
