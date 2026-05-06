From Stdlib Require Import List Morphisms.
From PhantomNames Require Import Index.
From Equations Require Import Equations.
Import ListNotations.

(**************************************************************************)
(** * Lambda terms *)
(**************************************************************************)

(** Untyped lambda terms, using phantom names. *)
Inductive term (s : scope) :=
| var (i : index s)
| app (t u : term s)
| lam (x : tag) (t : term (s ▷ x)).

Arguments var {s}.
Arguments app {s}.
Arguments lam {s}.

(** N-ary application constructor. *)
Fixpoint apps {s} (f : term s) (xs : list (term s)) : term s :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

(** Apply a thinning to a term. *)
Fixpoint thin {s s'} (δ : thinning s s') (t : term s) : term s' :=
  match t with
  | var i => var (tapply δ i)
  | app t u => app (thin δ t) (thin δ u)
  | lam x t => lam x (thin (ThinKeep x δ) t)
  end.

(** Smart weakening operation. *)
Definition wk {s s'} `{scope_incl s s'} (t : term s) : term s' :=
  thin wk_idx t.

(**************************************************************************)
(** * Parallel substitution *)
(**************************************************************************)

(** [subst s s'] is the type of parallel substitutions from scope [s] to [s']. *)
Definition subst (s s' : scope) := index s -> term s'.

(** The identity substitution. *)
Definition sid {s} : subst s s :=
  fun i => var i.

(** [scons x t σ] is a substitution which maps:
    - [0] to [t].
    - [i + 1] to [σ i]. *)
Equations scons {s s'} (x : tag) (t : term s') (σ : subst s s') : subst (s ▷ x) s' :=
scons x t σ I0 := t ;
scons x t σ (IS i) := σ i.

(** [sup x σ] lifts the substitution [σ] through a binder [x]. *)
Definition sup {s s'} (x : tag) (σ : subst s s') : subst (s ▷ x) (s' ▷ x) :=
  scons x (var I0) (fun i => wk (σ i)).

(** [substitute σ t] applies the parallel substitution [σ] to the term [t]. *)
Fixpoint substitute {s s'} (σ : subst s s') (t : term s) : term s' :=
  match t with
  | var i => σ i
  | app t1 t2 => app (substitute σ t1) (substitute σ t2)
  | lam x t => lam x (substitute (sup x σ) t)
  end.

(** [t[x := u]] substitutes de Bruijn index [0] with [u] in [t]. *)
Notation "t [ x := u ]" := (substitute (scons x u sid) t) (at level 0).

(**************************************************************************)
(** * Reduction relation *)
(**************************************************************************)

Reserved Notation "t '~~>' u" (at level 60, no associativity).

Inductive red {s} : term s -> term s -> Prop :=
| red_refl t :
    t ~~> t
| red_trans t u v :
    t ~~> u ->
    u ~~> v ->
    t ~~> v
| red_beta x t u :
    app (lam x t) u ~~> t[x := u]
| red_app t t' u u' :
    t ~~> t' ->
    u ~~> u' ->
    app t u ~~> app t' u'
| red_lam x t t' :
    t ~~> t' ->
    lam x t ~~> lam x t'
where "t '~~>' u" := (red t u).

#[local] Instance red_PreOrder s : PreOrder (@red s).
Proof.
constructor.
- intros t. apply red_refl.
- intros t1 t2 t3. apply red_trans.
Qed.

#[local] Instance red_app_Proper s : Proper (red ==> red ==> red) (@app s).
Proof.
intros t t' Ht u u' Hu. now apply red_app.
Qed.

#[local] Instance red_lam_Proper s x : Proper (red ==> red) (@lam s x).
Proof.
intros t t' Ht. now apply red_lam.
Qed.

(** This instance could be more general, but is sufficient here. *)
#[local] Instance red_apps s : Proper (red ==> eq ==> red) (@apps s).
Proof.
intros f f' Hf xs ? <-. induction xs in f, f', Hf |- * ; cbn.
- assumption.
- apply IHxs. now rewrite Hf.
Qed.

(**************************************************************************)
(** * Stack reduction machine *)
(**************************************************************************)

(** Apply a term to a stack of arguments. *)
Definition zip {s} (t : term s * list (term s)) := apps (fst t) (snd t).

(** Strong call-by-name stack reduction machine. *)
Fixpoint reduce_stack {s} (fuel : nat) (t : term s) (stack : list (term s))
    : term s * list (term s) :=
  match fuel with 0 => (t, stack) | S fuel =>
  match t with
  | var i => (var i, stack)
  | app f arg => reduce_stack fuel f (arg :: stack)
  | lam x t =>
    match stack with
    | [] =>
      let t := reduce_stack fuel t nil in
      (lam x (zip t), [])
    | arg :: stack =>
      reduce_stack fuel (t[x := arg]) stack
    end
  end
  end.

Lemma reduce_stack_correct s fuel (t : term s) stack :
  apps t stack ~~> zip (reduce_stack fuel t stack).
Proof.
induction fuel in s, t, stack |- * ; cbn [reduce_stack].
- cbn. reflexivity.
- destruct t.
  (* var case. *)
  + cbn. reflexivity.
  (* app case *)
  + specialize (IHfuel _ t1 (t2 :: stack)). rewrite <-IHfuel.
    cbn. reflexivity.
  (* lam case *)
  + destruct stack as [| arg stack].
    (* Empty argument stack. *)
    * specialize (IHfuel _ t nil). cbn in *. now f_equiv.
    (* Non-empty argument stack. *)
    * specialize (IHfuel _ (t[x := arg]) stack).
      cbn in *. rewrite red_beta. exact IHfuel.
Qed.