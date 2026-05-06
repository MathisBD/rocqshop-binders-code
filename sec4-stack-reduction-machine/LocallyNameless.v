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
(** * Names of free variables *)
(**************************************************************************)

(** A name is a unique identifier for a variable. *)
Definition name := nat.

(** [swap_name a b : name -> name] is the permutation which swaps [a] and [b]. *)
Definition swap_name (a b x : name) : name :=
  if x =? a then b
  else if x =? b then a
  else x.

Lemma swap_name_left a b : swap_name a b a = b.
Proof. cbn. unfold swap_name. now rewrite Nat.eqb_refl. Qed.

Lemma swap_name_right a b : swap_name a b b = a.
Proof.
cbn. unfold swap_name. destruct (Nat.eqb_spec b a) ; auto.
now rewrite Nat.eqb_refl.
Qed.

Lemma swap_name_other a b x :
  x ≠ a -> x ≠ b -> swap_name a b x = x.
Proof.
intros Ha Hb. unfold swap_name. rewrite <-Nat.eqb_neq in Ha, Hb.
rewrite Ha, Hb. reflexivity.
Qed.

(** [swap_name] is involutive. *)
Lemma swap_name_inv a b x :
  swap_name a b (swap_name a b x) = x.
Proof.
unfold swap_name. destruct (Nat.eqb_spec x a) ; subst.
- rewrite Nat.eqb_refl. now destruct (Nat.eqb_spec b a).
- destruct (Nat.eqb_spec x b) ; subst.
  + now rewrite Nat.eqb_refl.
  + rewrite <-Nat.eqb_neq in n, n0. now rewrite n, n0.
Qed.

(** [swap_name] is injective. *)
Lemma swap_name_inj a b x x' :
  swap_name a b x = swap_name a b x' ->
  x = x'.
Proof.
intros H. apply (f_equal (swap_name a b)) in H.
now rewrite !swap_name_inv in H.
Qed.

(**************************************************************************)
(** * Lambda terms *)
(**************************************************************************)

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

(** Compute the size of a term. It is sometimes useful to reason by
    induction on the size of terms. *)
Fixpoint term_size (t : term) : nat :=
  match t with
  | fvar _ => 0
  | bvar _ => 0
  | app t1 t2 => 1 + term_size t1 + term_size t2
  | lam t => 1 + term_size t
  end.

(** Compute the set of free variables in a term. *)
Fixpoint fv (t : term) : gset name :=
  match t with
  | fvar x => {[ x ]}
  | bvar i => ∅
  | app t1 t2 => fv t1 ∪ fv t2
  | lam t => fv t
  end.

(** [swap_term a b t] swaps names [a] and [b] in term [t]. *)
Fixpoint swap_term (a b : name) (t : term) : term :=
  match t with
  | fvar x => fvar (swap_name a b x)
  | bvar i => bvar i
  | app t1 t2 => app (swap_term a b t1) (swap_term a b t2)
  | lam t => lam (swap_term a b t)
  end.

(** [swap_term] is involutive. *)
Lemma swap_term_inv a b t :
  swap_term a b (swap_term a b t) = t.
Proof.
induction t ; cbn ; try congruence.
now rewrite swap_name_inv.
Qed.

(** [swap_term] is injective. *)
Lemma swap_term_inj a b t t' :
  swap_term a b t = swap_term a b t' ->
  t = t'.
Proof.
intros H. apply (f_equal (swap_term a b)) in H.
now rewrite !swap_term_inv in H.
Qed.

Lemma swap_term_fv a b x t :
  swap_name a b x ∈ fv (swap_term a b t) <-> x ∈ fv t.
Proof.
induction t ; cbn ; split ; intros H ; try set_solver.
set_unfold. now apply swap_name_inj in H.
Qed.

Lemma swap_term_free a b t :
  a ∉ fv t -> b ∉ fv t -> swap_term a b t = t.
Proof.
intros Ha Hb. induction t ; cbn in *.
- set_unfold in Ha. set_unfold in Hb. now rewrite swap_name_other.
- constructor.
- rewrite IHt1, IHt2 ; set_solver.
- now rewrite IHt.
Qed.

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

Lemma fv_open x t :
  fv t ⊆ fv (t ^ x).
Proof.
generalize 0. induction t ; cbn in * ; set_solver.
Qed.

Lemma not_elem_of_fv_close t x :
  x ∉ fv (t \^ x).
Proof.
generalize 0. intros k. induction t in k, x |- * ; cbn ; try set_solver.
destruct (Nat.eqb_spec x x0) ; set_solver.
Qed.

(** Opening commutes with swapping. *)
Lemma open_equivariant a b t u :
  swap_term a b (t ^^ u) = (swap_term a b t) ^^ (swap_term a b u).
Proof.
generalize 0. induction t ; intros k ; cbn.
- reflexivity.
- now destruct (Nat.eqb_spec i k).
- now rewrite IHt1, IHt2.
- now rewrite IHt.
Qed.

(** Opening commutes with swapping. *)
Lemma open_var_equivariant a b t x :
  swap_term a b (t ^ x) = (swap_term a b t) ^ (swap_name a b x).
Proof. now rewrite open_equivariant. Qed.

(** Closing commutes with swapping. *)
Lemma close_equivariant a b t x :
  swap_term a b (t \^ x) = (swap_term a b t) \^ (swap_name a b x).
Proof.
generalize 0. induction t ; intros k ; cbn.
- destruct (Nat.eqb_spec x x0) ; subst ; cbn.
  + now rewrite Nat.eqb_refl.
  + destruct (Nat.eqb_spec (swap_name a b x) (swap_name a b x0)) as [E | E].
    * apply swap_name_inj in E. firstorder.
    * reflexivity.
- reflexivity.
- now rewrite IHt1, IHt2.
- now rewrite IHt.
Qed.

(**************************************************************************)
(** * Locally closed terms *)
(**************************************************************************)

(** We formalize the notion of locally closed terms in order to state
    and prove the lemma [open_close_same]. *)

(** [lc t n] means that [t] is locally closed under [n] binders,
    i.e. that the de Bruijn indices of [t] are smaller than [n]. *)
Inductive lc : term -> nat -> Prop :=
| lc_fvar x n :
    lc (fvar x) n
| lc_bvar i n :
    i < n ->
    lc (bvar i) n
| lc_app t1 t2 n :
    lc t1 n ->
    lc t2 n ->
    lc (app t1 t2) n
| lc_lam t n :
    lc t (n + 1) ->
    lc (lam t) n.

Lemma lc_open_var t n x :
  lc t (n + 1) <-> lc (open_ n (fvar x) t) n.
Proof.
revert n. induction t ; intros n ; split ; intros H ; cbn in *.
- constructor.
- constructor.
- destruct (Nat.eqb_spec i n) ; subst.
  + constructor.
  + inversion H ; subst. constructor. lia.
- destruct (Nat.eqb_spec i n) ; subst.
  + constructor. lia.
  + constructor. inversion H ; subst. lia.
- inversion H ; subst. constructor.
  + now apply IHt1.
  + now apply IHt2.
- inversion H ; subst. constructor.
  + now apply IHt1.
  + now apply IHt2.
- inversion H ; subst. clear H. constructor. now apply IHt.
- inversion H ; subst. clear H. constructor. now apply IHt.
Qed.

Lemma open_close_same x t :
  lc t 0 ->
  (t \^ x) ^ x = t.
Proof.
generalize 0. induction t ; intros n H ; cbn in *.
- destruct (Nat.eqb_spec x x0) ; subst.
  + cbn. rewrite Nat.eqb_refl. reflexivity.
  + cbn. reflexivity.
- inversion H ; subst. destruct (Nat.eqb_spec i n) ; subst.
  + lia.
  + reflexivity.
- inversion H ; subst. rewrite IHt1, IHt2 by assumption. reflexivity.
- inversion H ; subst. rewrite IHt by assumption. reflexivity.
Qed.

(**************************************************************************)
(** * Reduction relation *)
(**************************************************************************)

Reserved Notation "t '~~>' u" (at level 60, no associativity).

(** Strong reduction relation.
    We use universal quantification in the abstraction case. *)
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
| red_lam t t' :
    (forall x, x ∉ fv t -> x ∉ fv t' -> t ^ x ~~> t' ^ x) ->
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

(** Reduction commutes with swapping. *)
Lemma red_equivariant a b t t' :
  swap_term a b t ~~> swap_term a b t' <-> t ~~> t'.
Proof.
enough (forall t t', t ~~> t' -> swap_term a b t ~~> swap_term a b t').
{
  split ; [|apply H]. rewrite <-(swap_term_inv a b t), <-(swap_term_inv a b t') at 2.
  apply H.
}
clear t t' ; intros t t'. intros H. induction H ; cbn.
- reflexivity.
- rewrite IHred1, IHred2. reflexivity.
- rewrite red_beta. rewrite open_equivariant. reflexivity.
- rewrite IHred1, IHred2. reflexivity.
- apply red_lam. intros x Hx1 Hx2. specialize (H0 (swap_name a b x)).
  rewrite !open_var_equivariant, !swap_name_inv in H0. apply H0.
  + rewrite <-(swap_term_inv a b t). now rewrite swap_term_fv.
  + rewrite <-(swap_term_inv a b t'). now rewrite swap_term_fv.
Qed.

(** Existentially quantified introduction rule for the abstraction
    case of [red]. *)
Lemma red_lam_intro x t t' :
  x ∉ fv t -> x ∉ fv t' -> t ^ x ~~> t' ^ x ->
  lam t ~~> lam t'.
Proof.
intros Hx1 Hx2 H. apply red_lam. intros y Hy1 Hy2. apply (red_equivariant x y) in H.
rewrite !open_var_equivariant, !swap_name_left in H.
now rewrite !swap_term_free in H.
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

Fixpoint swap_context (a b : name) (ctx : context) : context :=
  match ctx with
  | [] => []
  | x :: ctx => swap_name a b x :: swap_context a b ctx
  end.

(** [swap_context] is involutive. *)
Lemma swap_context_inv a b ctx :
  swap_context a b (swap_context a b ctx) = ctx.
Proof.
induction ctx ; cbn.
- reflexivity.
- now rewrite IHctx, swap_name_inv.
Qed.

Lemma swap_context_fv a b x c :
  swap_name a b x ∈ domain (swap_context a b c) <-> x ∈ domain c.
Proof.
induction c ; cbn ; split.
- set_solver.
- set_solver.
- set_unfold. rewrite <-IHc. pose proof (H := swap_name_inj a b x a0).
  firstorder.
- set_solver.
Qed.

Lemma swap_context_free a b c :
  a ∉ domain c -> b ∉ domain c -> swap_context a b c = c.
Proof.
intros Ha Hb. induction c ; cbn.
- reflexivity.
- rewrite IHc ; [| set_solver..]. f_equal.
  rewrite swap_name_other ; set_solver.
Qed.

(** A term is well-scoped iff all of its free variables appear in the context.
    In particular [bvar i] is never well-scoped.

    We use universal quantification in the abstraction case.*)
Inductive well_scoped : context -> term -> Prop :=
| well_scoped_fvar ctx x :
    x ∈ domain ctx -> well_scoped ctx (fvar x)
| well_scoped_app ctx t1 t2 :
    well_scoped ctx t1 ->
    well_scoped ctx t2 ->
    well_scoped ctx (app t1 t2)
| well_scoped_lam ctx t :
    (forall x, x ∉ fv t -> x ∉ domain ctx -> well_scoped (x :: ctx) (t ^ x)) ->
    well_scoped ctx (lam t).

(** [well_scoped] commutes with swapping. *)
Lemma well_scoped_equivariant a b ctx t :
  well_scoped (swap_context a b ctx) (swap_term a b t) <-> well_scoped ctx t.
Proof.
enough (forall ctx t, well_scoped ctx t -> well_scoped (swap_context a b ctx) (swap_term a b t)).
{
  split ; [|apply H].
  rewrite <-(swap_context_inv a b ctx), <-(swap_term_inv a b t) at 2.
  apply H.
}
clear t ctx ; intros ctx t H. induction H ; cbn.
- constructor. rewrite swap_context_fv. assumption.
- constructor ; assumption.
- constructor. intros x Hx1 Hx2. specialize (H0 (swap_name a b x)).
  forward H0. { rewrite <-(swap_term_inv a b t), swap_term_fv. assumption. }
  forward H0. { rewrite <-(swap_context_inv a b ctx), swap_context_fv. assumption. }
  cbn in H0. rewrite open_var_equivariant, !(swap_name_inv) in H0.
  now apply H0.
Qed.

(** Existentially-quantified introduction rule for the abstraction
    case of [well_scoped]. *)
Lemma well_scoped_lam_intro x t ctx :
  x ∉ fv t -> x ∉ domain ctx -> well_scoped (x :: ctx) (t ^ x) ->
  well_scoped ctx (lam t).
Proof.
intros Hx1 Hx2 H. constructor. intros y Hy1 Hy2.
rewrite <-(well_scoped_equivariant x y). cbn. rewrite swap_name_right.
rewrite open_var_equivariant, swap_name_right.
rewrite swap_context_free, swap_term_free by assumption.
exact H.
Qed.

Lemma well_scoped_fv t ctx :
  well_scoped ctx t ->
  fv t ⊆ domain ctx.
Proof.
intros H. induction H ; cbn.
- set_solver.
- set_solver.
- clear H. intros y Hy. destruct (exist_fresh (fv t ∪ domain ctx ∪ {[ y ]})) as [x Hx].
  specialize (H0 x). forward H0 ; [set_solver |]. forward H0 ; [set_solver |].
  rewrite <-fv_open in H0. apply H0 in Hy. cbn in Hy. set_solver.
Qed.

(** A well-scoped term is locally closed. *)
Lemma well_scoped_lc ctx t :
  well_scoped ctx t -> lc t 0.
Proof.
intros H. induction H ; cbn.
- constructor.
- now constructor.
- constructor. cbn.
  destruct (exist_fresh (fv t ∪ domain ctx)) as [x Hx].
  specialize (H0 x). forward H0 ; [set_solver |]. forward H0 ; [set_solver |].
  rewrite <-lc_open_var in H0. assumption.
Qed.

Lemma well_scoped_open ctx t u :
  well_scoped ctx (lam t) ->
  well_scoped ctx u ->
  well_scoped ctx (t ^^ u).
Proof.
Admitted.

(** Reduction preserves well-scopedness. *)
Lemma well_scoped_red ctx t t' :
  t ~~> t' ->
  well_scoped ctx t ->
  well_scoped ctx t'.
Proof.
intros Hred H. induction Hred in ctx, H |- *.
- assumption.
- firstorder.
- inversion H. subst. now apply well_scoped_open.
- inversion H ; subst. apply well_scoped_app ; auto.
- inversion H ; subst. destruct (exist_fresh (fv t ∪ fv t' ∪ domain ctx)) as (y & Hy).
  apply well_scoped_lam_intro with y ; [set_solver.. |].
  apply H1 ; [set_solver.. |]. apply H4 ; set_solver.
Qed.

(**************************************************************************)
(** * Stack reduction machine *)
(**************************************************************************)

(** [fresh_name ctx] returns a name which is not in the context [ctx]. *)
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
      assert (Hy : y ∉ fv t).
      {
        apply well_scoped_lam, well_scoped_fv in H. cbn in H.
        subst. pose proof (fresh_name_spec ctx). firstorder.
      }
      specialize (IHfuel (y :: ctx) (t ^ y) []).
      forward IHfuel.
      {
        apply H.
        - assumption.
        - subst. apply fresh_name_spec.
      }
      forward IHfuel. { constructor. }
      cbn in IHfuel.
      apply red_lam_intro with y.
      --assumption.
      --apply not_elem_of_fv_close.
      --rewrite open_close_same ; [exact IHfuel |].
        apply well_scoped_lc with (ctx := y :: ctx).
        apply well_scoped_red with (t ^ y) ; [assumption |].
        apply H ; auto. subst. apply fresh_name_spec.
    (* The stack is non-empty. *)
    * specialize (IHfuel ctx (t ^^ x) stack).
      forward IHfuel.
      {
        apply well_scoped_open.
        - now apply well_scoped_lam in H.
        - inversion HΓ ; subst. assumption.
      }
      forward IHfuel. { inversion HΓ ; now subst. }
      rewrite <-IHfuel. cbn. rewrite red_beta. reflexivity.
Qed.