From Stdlib Require Import Morphisms.
From stdpp Require Import gmap.

(** [forward H] performs forward reasoning: given a hypothesis [H : A -> B],
    it firsts asks to prove [A] and then [A |- B]. *)
Ltac forward H :=
  match type of H with
  | ?A -> ?B =>
    let H' := fresh in
    assert (H' : A); [| specialize (H H'); clear H' ]
  end.

(**************************************************************************)
(** * Lambda terms *)
(**************************************************************************)

(** A name is a unique identifier for a variable. *)
Definition name := nat.

(** Untyped lambda terms in the locally nameless style. *)
Inductive term :=
| fvar (x : name) : term
| bvar (i : nat) : term
| app (t1 : term) (t2 : term) : term
| lam (t : term) : term.

(** N-ary application constructor. *)
Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

(**************************************************************************)
(** * Opening and closing terms *)
(**************************************************************************)

Fixpoint open_ (n : nat) (u : term) (t : term) : term :=
  match t with
  | fvar x => fvar x
  | bvar i => if i =? n then u else bvar i
  | app t1 t2 => app (open_ n u t1) (open_ n u t2)
  | lam t => lam (open_ (n+1) u t)
  end.

(** [t ^^ u] replaces de Bruijn index [0] with [u] in [t].
    It assumes [u] is locally closed (so no lifting is needed). *)
Notation "t '^^' u" := (open_ 0 u t) (at level 30, no associativity).
Notation "t '^' x" := (open_ 0 (fvar x) t) (at level 30, no associativity).

Fixpoint close_ (n : nat) (x : name) (t : term) : term :=
  match t with
  | fvar y => if x =? y then bvar n else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (close_ n x t1) (close_ n x t2)
  | lam t => lam (close_ (n+1) x t)
  end.

(** [t \^ x] replaces variable [x] with de Bruijn index [0] in [t]. *)
Notation "t '\^' x" := (close_ 0 x t) (at level 30, no associativity).

(**************************************************************************)
(** * Reduction relation *)
(**************************************************************************)

Reserved Notation "t '~~>' u" (at level 60, no associativity).

(** Strong reduction relation, using cofinite quantification in the
    abstraction case. *)
Inductive red : term -> term -> Prop :=
| red_refl t :
    t ~~> t
| red_trans t u v :
    t ~~> u ->
    u ~~> v ->
    t ~~> v
| red_beta t u :
    app (lam t) u ~~> t ^^ u
| red_app t t' u u' :
    t ~~> t' ->
    u ~~> u' ->
    app t u ~~> app t' u'
| red_lam (L : gset name) t t' :
    (forall x, x ∉ L -> t ^ x ~~> t' ^ x) ->
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

(** This instance could be more general, but we only need this. *)
#[local] Instance red_apps : Proper (red ==> eq ==> red) apps.
Proof.
intros f f' Hf xs ? <-. induction xs in f, f', Hf |- * ; cbn.
- assumption.
- apply IHxs. now rewrite Hf.
Qed.

(**************************************************************************)
(** * Well-scoped judgement *)
(**************************************************************************)

(** A local context stores the names of all free variables
    in scope. The most recent variable is at the head of the list. *)
Definition context := list name.

(** The domain of a context is the set of variables which are bound
    by the context. *)
Fixpoint domain (ctx : context) : gset name :=
  match ctx with
  | [] => ∅
  | x :: ctx => {[ x ]} ∪ domain ctx
  end.

(** A term is well-scoped iff all of its free variables appear in the context.
    In particular [bvar i] is never well-scoped.

    We use cofinite quantification in the abstraction case. *)
Inductive well_scoped : context -> term -> Prop :=
| well_scoped_fvar ctx x :
    x ∈ domain ctx -> well_scoped ctx (fvar x)
| well_scoped_app ctx t1 t2 :
    well_scoped ctx t1 ->
    well_scoped ctx t2 ->
    well_scoped ctx (app t1 t2)
| well_scoped_lam (L : gset name) ctx t :
    (forall x, x ∉ L -> well_scoped (x :: ctx) (t ^ x)) ->
    well_scoped ctx (lam t).

Lemma well_scoped_open ctx t u :
  well_scoped ctx (lam t) ->
  well_scoped ctx u ->
  well_scoped ctx (t ^^ u).
Proof.
Admitted.

(**************************************************************************)
(** * Stack reduction machine *)
(**************************************************************************)

(** [fresh_name Γ] returns a name which is not in the context [Γ]. *)
Definition fresh_name (ctx : context) : name :=
  fresh ctx.

Lemma fresh_name_spec ctx : fresh_name ctx ∉ domain ctx.
Proof.
unfold fresh_name. pose proof (H := infinite_is_fresh ctx).
intros H1. apply H. clear H. unfold context in H1.
remember (@fresh name (list name) (@infinite_fresh name nat_infinite) ctx) as x.
clear Heqx. induction ctx ; set_solver.
Qed.

(** Apply a term to a stack of arguments. *)
Definition zip (t : term * list term) := apps (fst t) (snd t).

(** Strong call-by-name stack reduction machine. *)
Fixpoint reduce_stack (fuel : nat) (Γ : context) (t : term) (stack : list term) : term * list term :=
  match fuel with 0 => (t, stack) | S fuel =>
  match t with
  | fvar x => (fvar x, stack)
  | bvar i => (bvar i, stack) (* This case shouldn't happen. *)
  | app f x => reduce_stack fuel Γ f (x :: stack)
  | lam t =>
    match stack with
    | [] =>
      let x := fresh_name Γ in
      let t := reduce_stack fuel (x :: Γ) (t ^ x) [] in
      (lam (zip t \^ x), [])
    | arg :: stack =>
      reduce_stack fuel Γ (t ^^ arg) stack
    end
  end
  end.

Lemma reduce_stack_correct fuel Γ t stack :
  well_scoped Γ t ->
  Forall (well_scoped Γ) stack ->
  apps t stack ~~> zip (reduce_stack fuel Γ t stack).
Proof.
induction fuel in t, stack, Γ |- * ; cbn [reduce_stack] ; intros Ht HΓ.
- reflexivity.
- destruct Ht.
  (* fvar case. *)
  + cbn. reflexivity.
  (* app case. *)
  + specialize (IHfuel ctx t1 (t2 :: stack)). apply IHfuel.
    * assumption.
    * constructor ; assumption.
  (* lam case. *)
  + destruct stack as [| x stack].
    (* The stack is empty. *)
    * remember (fresh_name ctx) as y. cbn.
      specialize (IHfuel (y :: ctx) (t ^ y) []).
      forward IHfuel.
      {
        (* Here we want to apply [H] which corresponds to the rule for lambda in [well_scoped].
           We get stuck because the premise of the rule is too strong.
           Indeed, we have an _arbitrary_ set [L], and we need to show that the name
           [y] we got from [fresh_name] is not in [L].
           i.e. we would need the rule for [well_scoped_lam] to have a universally quantified
           premise. *)
        apply H. admit.
      }
      forward IHfuel. { constructor. }
      cbn in IHfuel.
      (* Here the premise of the rule for reduction under lambdas is too strong:
         we need to prove that the bodies reduce to each other for co-finitely many
         fresh names, but we only know that is the case for exactly one fresh name
         (the one generated by [fresh_name]).
         i.e. we would need the rule for [red1_lam] to have an existentially quantified
         premise. *)
      apply red_lam with (domain ctx). admit.
    (* The stack is non-empty. *)
    * specialize (IHfuel ctx (t ^^ x) stack).
      forward IHfuel.
      {
        apply well_scoped_open.
        - now apply well_scoped_lam in H.
        - inversion HΓ ; now subst.
      }
      forward IHfuel. { inversion HΓ ; now subst. }
      rewrite <-IHfuel. cbn. rewrite red_beta. reflexivity.
Admitted.

(** The issue is that we don't get to pick the fresh name in the proof,
    it is instead computed by the program we are trying to verify. *)