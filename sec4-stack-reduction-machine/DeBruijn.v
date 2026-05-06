From Stdlib Require Import List Morphisms.
Import ListNotations.

(**************************************************************************)
(** * Lambda terms *)
(**************************************************************************)

(** Untyped lambda terms, using de Bruijn indices. *)
Inductive term :=
| var : nat -> term
| app : term -> term -> term
| lam : term -> term.

(** N-ary application constructor. *)
Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

(**************************************************************************)
(** * Parallel substitution *)
(**************************************************************************)

(** [rup ρ] lifts the renaming [ρ] through a binder. *)
Definition rup (ρ : nat -> nat) (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i => S (ρ i)
  end.

(** [rename ρ t] applies the parallel renaming [ρ] to the term [t]. *)
Fixpoint rename (ρ : nat -> nat) (t : term) : term :=
  match t with
  | var i => var (ρ i)
  | app t1 t2 => app (rename ρ t1) (rename ρ t2)
  | lam t => lam (rename (rup ρ) t)
  end.

(** [sup σ] lifts the substitution [σ] through a binder. *)
Definition sup (σ : nat -> term) (i : nat) : term :=
  match i with
  | 0 => var 0
  | S i => rename S (σ i)
  end.

(** [substitute σ t] applies the parallel substitution [σ] to the term [t]. *)
Fixpoint substitute (σ : nat -> term) (t : term) : term :=
  match t with
  | var i => σ i
  | app t1 t2 => app (substitute σ t1) (substitute σ t2)
  | lam t => lam (substitute (sup σ) t)
  end.

(** [subst1 t u] substitutes de Bruijn index [0] with [u] in [t]. *)
Definition subst1 (t u : term) : term :=
  substitute (fun i => match i with 0 => u | S i => var i end) t.

(**************************************************************************)
(** * Reduction relation *)
(**************************************************************************)

Reserved Notation "t '~~>' u" (at level 60, no associativity).

Inductive red : term -> term -> Prop :=
| red_refl t :
    t ~~> t
| red_trans t u v :
    t ~~> u ->
    u ~~> v ->
    t ~~> v
| red_beta t u :
    app (lam t) u ~~> subst1 t u
| red_app t t' u u' :
    t ~~> t' ->
    u ~~> u' ->
    app t u ~~> app t' u'
| red_lam t t' :
    t ~~> t' ->
    lam t ~~> lam t'
where "t '~~>' u" := (red t u).

#[local] Instance red_PreOrder : PreOrder red.
Proof.
constructor.
- intros t. apply red_refl.
- intros t1 t2 t3. apply red_trans.
Qed.

#[local] Instance red_app_Proper : Proper (red ==> red ==> red) app.
Proof.
intros t t' Ht u u' Hu. now apply red_app.
Qed.

#[local] Instance red_lam_Proper : Proper (red ==> red) lam.
Proof.
intros t t' Ht. now apply red_lam.
Qed.

(** This instance could be more general, but is sufficient here. *)
#[local] Instance red_apps : Proper (red ==> eq ==> red) apps.
Proof.
intros f f' Hf xs ? <-. induction xs in f, f', Hf |- * ; cbn.
- assumption.
- apply IHxs. now rewrite Hf.
Qed.

(**************************************************************************)
(** * Stack reduction machine *)
(**************************************************************************)

(** Apply a term to a stack of arguments. *)
Definition zip (t : term * list term) := apps (fst t) (snd t).

(** Strong call-by-name stack reduction machine. *)
Fixpoint reduce_stack (fuel : nat) (t : term) (stack : list term) : term * list term :=
  match fuel with 0 => (t, stack) | S fuel =>
  match t with
  | var i => (var i, stack)
  | app f x => reduce_stack fuel f (x :: stack)
  | lam t =>
    match stack with
    | [] =>
      let t := reduce_stack fuel t [] in
      (lam (zip t), [])
    | arg :: stack =>
      reduce_stack fuel (subst1 t arg) stack
    end
  end
  end.

Lemma reduce_stack_correct fuel t stack :
  apps t stack ~~> zip (reduce_stack fuel t stack).
Proof.
induction fuel in t, stack |- * ; cbn [reduce_stack].
- cbn. reflexivity.
- destruct t.
  (* var case. *)
  + cbn. reflexivity.
  (* app case *)
  + specialize (IHfuel t1 (t2 :: stack)). rewrite <-IHfuel.
    cbn. reflexivity.
  (* lam case *)
  + destruct stack as [| arg stack].
    (* Empty argument stack. *)
    * specialize (IHfuel t []). cbn in *. now f_equiv.
    (* Non-empty argument stack. *)
    * specialize (IHfuel (subst1 t arg) stack).
      cbn in *. rewrite red_beta. exact IHfuel.
Qed.