(** This module develops the equational theory of thinnings and substitutions,
    i.e. the theory of sigma calculus.
    Note that we assume the functional extensionality axiom which
    simplifies many lemmas and allows the tactic [simp_subst] to be reasonably
    efficient.

    We provide a few tactics to reason about thinnings and substitutions:
    - [thin_ext i] and [subst_ext i] are the analogs of [fun_ext i] for thinnings
      and substitutions.
    - [change_tag x with y] replaces all occurences of tag [x] with tag [y].
    - [simp_subst] repeatedly rewrites with lemmas which simplify thinnings
      and substitutions. A version [simp_subst in H] is also available to
      simplify in hypothesis [H]. Note that [simp_subst] will unfold
      [wk] as this is usually what you want when doing proofs.
    - [nf_subst] is a more aggressive version of [simpl_subst] that will
      replace all thinnings with equivalent substitutions.
      A common pattern is using [nf_subst ; reflexivity] to prove an equality
      which mixes thinning and substitutions.
*)

From Ltac2 Require Import Std Rewrite.
From MetaTheory Require Import Prelude.
From MetaTheory Require Export Data.Term Data.Context.

(***********************************************************************)
(** * Extensionality lemmas *)
(***********************************************************************)

Lemma thin_ext {s s'} (δ δ' : thinning s s') :
  (forall i, tapply δ i = tapply δ' i) -> δ = δ'.
Proof.
intros H. depind δ.
- depelim δ'. reflexivity.
- depelim δ'.
  + f_equal. apply IHδ. intros i. specialize (H i). simp tapply in H. now depelim H.
  + specialize (H I0). simp tapply in H. depelim H.
- depelim δ'.
  + specialize (H I0). simp tapply in H. depelim H.
  + f_equal. apply IHδ. intros i. specialize (H (IS i)). simp tapply in H.
    now depelim H.
Qed.

Lemma subst_ext {s s'} (σ σ' : subst s s') :
  (forall i, sapply σ i = sapply σ' i) -> σ = σ'.
Proof.
intros H. destruct σ ; destruct σ'. f_equal. fun_ext i. apply H.
Qed.

(** Extentionality tactic for thinnings. *)
Tactic Notation "thin_ext" ident(i) := apply thin_ext ; intros i.

(** Extentionality tactic for substitutions. *)
Tactic Notation "subst_ext" ident(i) := apply subst_ext ; intros i.

(***********************************************************************)
(** * [change_tag] tactic *)
(***********************************************************************)

(** [change_tag x with y] replaces all occurences of tag [x] with tag [y],
    and removes [y] from the proof context. *)
Tactic Notation "change_tag" constr(x) "with" constr(y) :=
  assert (x = y) as -> by exact (tag_eq x y).

(***********************************************************************)
(** * [simp_subst] and [nf_subst] tactics *)
(***********************************************************************)

(** [simp_subst] can be applied:
    - to the goal as [simp_subst].
    - to a list of hypotheses as [simp_subst in H1, H2, H3].
    - to all hypotheses and the goal as [simp_subst in *].

    The same goes for [nf_subst].
*)

Lemma thin_closed {s} (δ : thinning ∅ s) :
  δ = wk_idx.
Proof. thin_ext i. depelim i. Qed.

Lemma subst_closed {s} (σ : subst ∅ s) :
  σ = subst_of_thin wk_idx.
Proof. subst_ext i. depelim i. Qed.

(** For some reason [thin_closed] and [subst_closed] don't work with [rewrite_strat].
    We instead rewrite with them using a custom tactic. *)

Local Ltac rewrite_closed :=
  match goal with
  | |- context[ ?x ] => first [ rewrite (thin_closed x) | rewrite (subst_closed x) ]
  | _ => idtac
  end.

Ltac rewrite_closed_in H :=
  match goal with
  | H : context[ ?x ] |- _ => first [ rewrite (thin_closed x) in H | rewrite (subst_closed x) in H ]
  | _ => idtac
  end.

(** [simp_subst] uses the hint database [subst] to allow for easy extension,
    and [nf_subst] uses the hint database [nf_subst].

    We are quite conservative in which lemmas we put in the [subst] database,
    because [simp_subst] can easily loop indefinitely if we aren't careful. *)

Ltac2 tac_subst (hint_db : ident) :=
  unfold wk ;
  repeat (progress (first
    [ rewrite_db hint_db None
    | ltac1:(rewrite_closed) ])).

Ltac2 tac_subst_in (hint_db : ident) (h : ident) :=
  unfold wk in $h ;
  repeat (progress (first
    [ rewrite_db hint_db (Some h)
    | ltac1:(h |- rewrite_closed_in h) (Ltac1.of_ident h) ])).

Tactic Notation "simp_subst" := ltac2:(tac_subst @subst).
Tactic Notation "nf_subst" := ltac2:(tac_subst @nf_subst).

Tactic Notation "simp_subst" "in" ne_ident_list_sep(hs, ",") :=
  let f := ltac2:(hs |-
    let hs := Option.get (Ltac1.to_list hs) in
    List.iter (fun h => tac_subst_in @subst (Option.get (Ltac1.to_ident h))) hs)
  in
  f hs.

Tactic Notation "nf_subst" "in" ne_ident_list_sep(hs, ",") :=
  let f := ltac2:(hs |-
    let hs := Option.get (Ltac1.to_list hs) in
    List.iter (fun h => tac_subst_in @nf_subst (Option.get (Ltac1.to_ident h))) hs)
  in
  f hs.

Tactic Notation "simp_subst" "in" "*" :=
  ltac2:(List.iter (fun (h, _, _) => tac_subst_in @subst h) (Control.hyps ())).

Tactic Notation "nf_subst" "in" "*" :=
  ltac2:(List.iter (fun (h, _, _) => tac_subst_in @nf_subst h) (Control.hyps ())).

#[export] Hint Rewrite
  thin_equation_1
  thin_equation_2
  thin_equation_3
  thin_equation_4
  thin_equation_5
  thin_equation_6 : subst.

#[export] Hint Rewrite
  substitute_equation_1
  substitute_equation_2
  substitute_equation_3
  substitute_equation_4
  substitute_equation_5
  substitute_equation_6 : subst nf_subst.

(** I'm not sure if enabling the second equations of [context_subst]
    is a good idea, as it exposes a [match]. *)
#[export] Hint Rewrite
  context_subst_equation_1
  (*context_subst_equation_2*) : subst nf_subst.

Lemma wk_idx_refl {s} :
  @wk_idx _ _ (@scope_incl_refl s) = tid.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @wk_idx_refl : subst nf_subst.

Lemma wk_idx_incl_skip {x s s'} (H : scope_incl s s') :
  @wk_idx _ _ (scope_incl_skip x H) = ThinSkip x wk_idx.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @wk_idx_incl_skip : subst nf_subst.

Lemma wk_idx_incl_keep {x s s'} (H : scope_incl s s') :
  @wk_idx _ _ (scope_incl_keep x H) = ThinKeep x wk_idx.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @wk_idx_incl_keep : subst nf_subst.

Lemma replace_tag_same {x s} :
  @replace_tag s x x = tid.
Proof. destruct x. reflexivity. Qed.
#[export] Hint Rewrite @replace_tag_same : subst nf_subst.

(***********************************************************************)
(** * Lemmas about [tapply] *)
(***********************************************************************)

#[export] Hint Rewrite
  tapply_equation_1
  tapply_equation_2
  tapply_equation_3
  tapply_equation_4 : subst.

Lemma tapply_tid {s} (i : index s) :
  tapply tid i = i.
Proof.
depind s ; depelim i ; simp tid.
- now simp_subst.
- simp_subst. f_equal. auto.
Qed.
#[export] Hint Rewrite @tapply_tid : subst.

Lemma tapply_tshift {s x} (i : index s) :
  tapply (@tshift s x) i = IS i.
Proof. unfold tshift. now simp_subst. Qed.
#[export] Hint Rewrite @tapply_tshift : subst.

Lemma tapply_tcomp {s s' s''} (δ1 : thinning s s') (δ2 : thinning s' s'') i :
  tapply (tcomp δ1 δ2) i = tapply δ2 (tapply δ1 i).
Proof.
funelim (tcomp δ1 δ2) ; simp_subst.
- depelim i.
- f_equal. apply H.
- f_equal. apply H.
- f_equal. apply H.
- depelim i ; simp_subst.
  + reflexivity.
  + f_equal. apply H.
Qed.
#[export] Hint Rewrite @tapply_tcomp : subst.

(***********************************************************************)
(** * Lemmas about [tapply_inv] *)
(***********************************************************************)

Lemma tapply_inv_tapply {s s'} (δ : thinning s s') (i : index s) :
  tapply_inv δ (tapply δ i) = Some i.
Proof.
funelim (tapply δ i).
- simp tapply_inv.
- simp tapply_inv. reflexivity.
- simp tapply_inv. rewrite H. reflexivity.
Qed.
#[export] Hint Rewrite @tapply_inv_tapply : subst nf_subst.

Lemma tapply_inv_Some {s s'} (δ : thinning s s') i i' :
  tapply_inv δ i = Some i' <->
  tapply δ i' = i.
Proof.
split.
- intros H. funelim (tapply_inv δ i).
  + rewrite H in Heqcall. depelim Heqcall.
  + simp tapply_inv in H0. simp tapply. apply H in H0. now rewrite H0.
  + simp tapply_inv in H. depelim H. simp tapply. reflexivity.
  + simp tapply_inv in H0. destruct (tapply_inv δ i) as [i0 |].
    * cbn in H0. depelim H0. simp tapply. f_equal. now apply H.
    * cbn in H0. depelim H0.
- intros <-. simp_subst. reflexivity.
Qed.

(***********************************************************************)
(** * Lemmas about thinnings *)
(***********************************************************************)

Lemma tcomp_tid_l {s s'} (δ : thinning s s') :
  tcomp tid δ = δ.
Proof. thin_ext i. now simp_subst. Qed.
#[export] Hint Rewrite @tcomp_tid_l : subst.

Lemma tcomp_tid_r {s s'} (δ : thinning s s') :
  tcomp δ tid = δ.
Proof. thin_ext i. now simp_subst. Qed.
#[export] Hint Rewrite @tcomp_tid_r : subst.

Lemma ThinKeep_tid {s x} :
  ThinKeep x tid = @tid (s ▷ x).
Proof. thin_ext i. depelim i ; reflexivity. Qed.
#[export] Hint Rewrite @ThinKeep_tid : subst.

Lemma ThinKeep_tcomp {x s s' s''} (δ1 : thinning s s') (δ2 : thinning s' s'') :
  ThinKeep x (tcomp δ1 δ2) = tcomp (ThinKeep x δ1) (ThinKeep x δ2).
Proof. thin_ext i. depelim i ; reflexivity. Qed.
#[export] Hint Rewrite @ThinKeep_tcomp : subst.

Lemma ThinSkip_tid {x s} :
  ThinSkip x (@tid s) = tshift.
Proof. thin_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @ThinSkip_tid : subst.

Lemma tcomp_tshift_ThinKeep {x s s'} (δ : thinning s s') :
  tcomp tshift (ThinKeep x δ) = tcomp δ tshift.
Proof. thin_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tcomp_tshift_ThinKeep : subst.

Lemma tcomp_tshift_r {x s s'} (δ : thinning s s') :
  tcomp δ tshift = ThinSkip x δ.
Proof. thin_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tcomp_tshift_r : subst.

Lemma thin_tid {s} t :
  thin (@tid s) t = t.
Proof. induction t ; simp_subst ; f_equal ; assumption. Qed.
#[export] Hint Rewrite @thin_tid : subst.

Lemma thin_thin {s s' s''} (δ1 : thinning s s') (δ2 : thinning s' s'') t :
  thin δ2 (thin δ1 t) = thin (tcomp δ1 δ2) t.
Proof.
induction t in s', s'', δ1, δ2 |- * ; simp_subst ; f_equal ; auto.
Qed.
#[export] Hint Rewrite @thin_thin : subst.

Lemma tcomp_assoc {s s' s'' s'''} (δ1 : thinning s s') (δ2 : thinning s' s'') (δ3 : thinning s'' s''') :
  tcomp (tcomp δ1 δ2) δ3 = tcomp δ1 (tcomp δ2 δ3).
Proof. thin_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tcomp_assoc : subst.

Lemma thin_arrow {s s'} (a b : term s) (δ : thinning s s') :
  thin δ (arrow a b) = arrow (thin δ a) (thin δ b).
Proof. unfold arrow. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @thin_arrow : subst.

(***********************************************************************)
(** * Lemmas about [thicken] *)
(***********************************************************************)

Lemma thicken_thin {s s'} (δ : thinning s s') (t : term s) :
  thicken δ (thin δ t) = Some t.
Proof.
funelim (thin δ t) ; simp thicken ; simp_subst.
- reflexivity.
- reflexivity.
- rewrite H, H0. reflexivity.
- rewrite H, H0. reflexivity.
- rewrite H, H0. reflexivity.
- reflexivity.
Qed.
#[export] Hint Rewrite @thicken_thin : subst nf_subst.

Lemma thicken_Some {s s'} (δ : thinning s s') t t' :
  thicken δ t = Some t' <->
  thin δ t' = t.
Proof.
split.
- intros H. funelim (thicken δ t) ; simp thicken in H.
  + depelim H. simp thin. reflexivity.
  + destruct (tapply_inv δ i) as [i' |] eqn:H' ; cbn in H ; depelim H.
    rewrite tapply_inv_Some in H'. simp thin. now rewrite H'.
  + simp thicken in H1.
    destruct (thicken δ ty) as [ty' |] ; cbn in H1 ; simp option_apply in H1 ; [| depelim H1].
    destruct (thicken (ThinKeep x δ) body) as [body' |] ; simp option_apply in H1 ; depelim H1.
    simp thin. rewrite H, H0 ; reflexivity.
  + simp thicken in H1.
    destruct (thicken δ a) as [a' |] ; cbn in H1 ; simp option_apply in H1 ; [| depelim H1].
    destruct (thicken (ThinKeep x δ) b) as [b' |] ; simp option_apply in H1 ; depelim H1.
    simp thin. rewrite H, H0 ; reflexivity.
  + simp thicken in H1.
    destruct (thicken δ f) as [f' |] ; cbn in H1 ; simp option_apply in H1 ; [| depelim H1].
    destruct (thicken δ arg) as [arg' |] ; simp option_apply in H1 ; depelim H1.
    simp thin. rewrite H, H0 ; reflexivity.
  + depelim H. simp thin. reflexivity.
- intros <-. now simp_subst.
Qed.

(***********************************************************************)
(** * Inversion lemmas for [thin] *)
(***********************************************************************)

(** Injectivity of [tapply]. *)
Lemma tapply_inj {s s'} (δ : thinning s s') (i j : index s) :
  tapply δ i = tapply δ j ->
  i = j.
Proof.
intros H. apply (f_equal (tapply_inv δ)) in H.
rewrite !tapply_inv_tapply in H. now depelim H.
Qed.

(** Injectivity of [thin]. *)
Lemma thin_inj {s s'} (δ : thinning s s') (t u : term s) :
  thin δ t = thin δ u ->
  t = u.
Proof.
intros H. apply (f_equal (thicken δ)) in H.
rewrite !thicken_thin in H. now depelim H.
Qed.

Lemma thin_lam_inv {s s' x} (δ : thinning s s') ty' body' t :
  thin δ t = Lam x ty' body' ->
  exists ty body,
    t = Lam x ty body /\
    thin δ ty = ty' /\
    thin (ThinKeep x δ) body = body'.
Proof.
intros H. depelim t ; simp thin in H ; depelim H.
exists t1, t2 ; easy.
Qed.

Lemma thin_prod_inv {s s' x} (δ : thinning s s') a' b' t :
  thin δ t = Prod x a' b' ->
  exists a b,
    t = Prod x a b /\
    thin δ a = a' /\
    thin (ThinKeep x δ) b = b'.
Proof.
intros H. depelim t ; simp thin in H ; depelim H.
exists t1, t2 ; easy.
Qed.

Lemma thin_app_inv {s s'} (δ : thinning s s') f' arg' t :
  thin δ t = App f' arg' ->
  exists f arg,
    t = App f arg /\
    thin δ f = f' /\
    thin δ arg = arg'.
Proof.
intros H. depelim t ; simp thin in H ; depelim H.
exists t1, t2 ; easy.
Qed.

Lemma thin_evar_inv {s s'} (δ : thinning s s') ev t :
  thin δ t = Evar ev ->
  t = Evar ev.
Proof.
intros H. depelim t ; simp thin in H ; depelim H. reflexivity.
Qed.

Lemma thin_type_inv {s s'} (δ : thinning s s') t :
  thin δ t = Type_ ->
  t = Type_.
Proof.
intros H. depelim t ; simp thin in H ; depelim H. reflexivity.
Qed.

Lemma thin_var_inv {s s'} (δ : thinning s s') i' t :
  thin δ t = Var i' ->
  exists i,
    t = Var i /\
    tapply δ i = i'.
Proof.
intros H. depelim t ; simp thin in H ; depelim H.
exists i. now split.
Qed.

(***********************************************************************)
(** * Lemmas about [sapply] *)
(***********************************************************************)

Lemma sapply_sid {s} i :
  sapply (@sid s) i = Var i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sid : subst nf_subst.

Lemma sapply_sshift {s x} i :
  sapply (@sshift s x) i = Var (IS i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sshift : subst nf_subst.

Lemma sapply_stcomp {s s' s''} (σ : subst s s') (δ : thinning s' s'') i :
  sapply (stcomp σ δ) i = thin δ (sapply σ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_stcomp : subst.

Lemma sapply_tscomp {s s' s''} (δ : thinning s s') (σ : subst s' s'') i :
  sapply (tscomp δ σ) i = sapply σ (tapply δ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_tscomp : subst.

Lemma sapply_scomp {s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') i :
  sapply (scomp σ1 σ2) i = substitute σ2 (sapply σ1 i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scomp : subst nf_subst.

Lemma sapply_scons_zero {s s' x} t (σ : subst s s') :
  sapply (scons x t σ) I0 = t.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scons_zero : subst nf_subst.

Lemma sapply_scons_succ {s s' x} t (σ : subst s s') i :
  sapply (scons x t σ) (IS i) = sapply σ i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scons_succ : subst nf_subst.

Lemma sapply_sup_zero {s s' x} (σ : subst s s') :
  sapply (sup x σ) I0 = Var I0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sup_zero : subst nf_subst.

Lemma sapply_sup_succ {s s' x} i (σ : subst s s') :
  sapply (sup x σ) (IS i) = thin tshift (sapply σ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sup_succ : subst nf_subst.

(***********************************************************************)
(** * Lemmas about [subst_of_thin] *)
(***********************************************************************)

Lemma sapply_subst_of_thin {s s'} (δ : thinning s s') i :
  sapply (subst_of_thin δ) i = Var (tapply δ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_subst_of_thin : subst.
#[export] Hint Rewrite <-@sapply_subst_of_thin : nf_subst.

Lemma subst_of_thin_tid {s} :
  subst_of_thin (@tid s) = sid.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @subst_of_thin_tid : subst nf_subst.

Lemma subst_of_thin_tshift {s x} :
  subst_of_thin (@tshift s x) = sshift.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @subst_of_thin_tshift : subst nf_subst.

Lemma subst_of_thin_tskip {x s s'} (δ : thinning s s') :
  subst_of_thin (ThinSkip x δ) = stcomp (subst_of_thin δ) tshift.
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @subst_of_thin_tskip : subst nf_subst.

Lemma subst_of_thin_tkeep {x s s'} (δ : thinning s s') :
  subst_of_thin (ThinKeep x δ) = sup x (subst_of_thin δ).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @subst_of_thin_tkeep : subst nf_subst.

Lemma subst_of_thin_tcomp {s s' s''} (δ1 : thinning s s') (δ2 : thinning s' s'') :
  subst_of_thin (tcomp δ1 δ2) = scomp (subst_of_thin δ1) (subst_of_thin δ2).
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @subst_of_thin_tcomp : subst nf_subst.

Lemma substitute_subst_of_thin {s s'} (δ : thinning s s') t :
  substitute (subst_of_thin δ) t = thin δ t.
Proof.
induction t in s', δ |- * ; simp_subst ; f_equal ; auto.
- rewrite <-IHt2. now simp_subst.
- rewrite <-IHt2. now simp_subst.
Qed.
#[export] Hint Rewrite @substitute_subst_of_thin : subst.
#[export] Hint Rewrite <-@substitute_subst_of_thin : nf_subst.

(*Lemma substitute_sshift {s x} t :
  substitute (@sshift s x) t = thin tshift t.
Proof. rewrite <-substitute_subst_of_thin. reflexivity. Qed.
#[export] Hint Rewrite @substitute_sshift : subst.*)

(***********************************************************************)
(** * Lemmas about [stcomp] *)
(***********************************************************************)

Lemma sup_stcomp {s s' s'' x} (σ : subst s s') (δ : thinning s' s'') :
  sup x (stcomp σ δ) = stcomp (sup x σ) (ThinKeep x δ).
Proof.
subst_ext i. depelim i ; simp_subst.
- reflexivity.
- reflexivity.
Qed.

Lemma thin_substitute {s s' s''} (σ : subst s s') (δ : thinning s' s'') t :
  thin δ (substitute σ t) = substitute (stcomp σ δ) t.
Proof.
induction t in s', s'', σ, δ |- * ; simp_subst ; f_equal ; auto.
- rewrite sup_stcomp. auto.
- rewrite sup_stcomp. auto.
Qed.
#[export] Hint Rewrite @thin_substitute : subst.

Lemma stcomp_tid_r {s s'} (σ : subst s s') :
  stcomp σ tid = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @stcomp_tid_r : subst.

Lemma stcomp_sid_l {s s'} (δ : thinning s s') :
  stcomp sid δ = subst_of_thin δ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @stcomp_sid_l : subst.

Lemma stcomp_assoc {s s' s'' s'''} (σ1 : subst s s') (σ2 : subst s' s'') (δ3 : thinning s'' s''') :
  stcomp (scomp σ1 σ2) δ3 = scomp σ1 (stcomp σ2 δ3).
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @stcomp_assoc : subst.

Lemma stcomp_scons_l {x s s' s''} t (σ1 : subst s s') (δ2 : thinning s' s'') :
  stcomp (scons x t σ1) δ2 = scons x (thin δ2 t) (stcomp σ1 δ2).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @stcomp_scons_l : subst.

Lemma stcomp_sup_l {x s s' s''} (σ1 : subst s s') (δ2 : thinning (s' ▷ x) s'') :
  stcomp (sup x σ1) δ2 = scons x (Var (tapply δ2 I0)) (stcomp σ1 (tcomp tshift δ2)).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @stcomp_sup_l : subst.

Lemma stcomp_subst_of_thin_r {s s' s''} (σ : subst s s') (δ : thinning s' s'') :
  stcomp σ δ = scomp σ (subst_of_thin δ).
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @stcomp_subst_of_thin_r : nf_subst.

(***********************************************************************)
(** * Lemmas about [tscomp] *)
(***********************************************************************)

Lemma tscomp_tid_l {s s'} (σ : subst s s') :
  tscomp tid σ = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_tid_l : subst.

Lemma tscomp_sid_r {s s'} (δ : thinning s s') :
  tscomp δ sid = subst_of_thin δ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_sid_r : subst.

Lemma tscomp_tshift_scons {x s s'} t (σ : subst s s') :
  tscomp tshift (scons x t σ) = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_tshift_scons : subst.

Lemma tscomp_tshift_sup {x s s'} (σ : subst s s') :
  tscomp tshift (sup x σ) = stcomp σ tshift.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_tshift_sup : subst.

Lemma sup_tscomp {s s' s'' x} (δ : thinning s s') (σ : subst s' s'') :
  sup x (tscomp δ σ) = tscomp (ThinKeep x δ) (sup x σ).
Proof.
subst_ext i. depelim i ; simp_subst.
- reflexivity.
- reflexivity.
Qed.
#[export] Hint Rewrite @sup_stcomp : subst.

Lemma substitute_thin {s s' s''} (δ : thinning s s') (σ : subst s' s'') t :
  substitute σ (thin δ t) = substitute (tscomp δ σ) t.
Proof.
induction t in s', s'', σ, δ |- * ; simp_subst ; f_equal ; auto.
- rewrite sup_tscomp. f_equal ; auto.
- rewrite sup_tscomp. f_equal ; auto.
Qed.
#[export] Hint Rewrite @substitute_thin : subst.

Lemma tscomp_assoc {s s' s'' s'''} (δ1 : thinning s s') (σ2 : subst s' s'') (σ3 : subst s'' s''') :
  scomp (tscomp δ1 σ2) σ3 = tscomp δ1 (scomp σ2 σ3).
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_assoc : subst.

(*Lemma tscomp_rcons_l {x s s' s''} i (δ1 : thinning s s') (σ2 : subst s' s'') :
  tscomp (Vrcons x i δ1) σ2 = scons x (sapply σ2 i) (tscomp δ1 σ2).
Proof. subst_ext j. depelim j ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @tscomp_rcons_l : subst.*)

Lemma tscomp_tkeep_l {x s s' s''} (δ1 : thinning s s') (σ2 : subst (s' ▷ x) s'') :
  tscomp (ThinKeep x δ1) σ2 = scons x (sapply σ2 I0) (tscomp δ1 (tscomp tshift σ2)).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @tscomp_tkeep_l : subst.

Lemma tscomp_subst_of_thin_l {s s' s''} (δ : thinning s s') (σ : subst s' s'') :
  tscomp δ σ = scomp (subst_of_thin δ) σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @tscomp_subst_of_thin_l : nf_subst.

(***********************************************************************)
(** * Lemmas about [scomp] *)
(***********************************************************************)

Lemma sup_sid {s x} :
  sup x (@sid s) = sid.
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @sup_sid : subst nf_subst.

Lemma sup_scomp {x s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') :
  sup x (scomp σ1 σ2) = scomp (sup x σ1) (sup x σ2).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @sup_scomp : subst nf_subst.

Lemma substitute_sid {s} t :
  substitute (@sid s) t = t.
Proof.
induction t ; simp_subst ; f_equal ; assumption.
Qed.
#[export] Hint Rewrite @substitute_sid : subst nf_subst.

Lemma scomp_sid_l {s s'} (σ : subst s s') :
  scomp sid σ = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sid_l : subst nf_subst.

Lemma scomp_sid_r {s s'} (σ : subst s s') :
  scomp σ sid = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sid_r : subst nf_subst.

Lemma substitute_substitute {s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') t :
  substitute σ2 (substitute σ1 t) = substitute (scomp σ1 σ2) t.
Proof.
induction t in s', s'', σ1, σ2 |- * ; simp_subst ; f_equal ; auto.
Qed.
#[export] Hint Rewrite @substitute_substitute : subst nf_subst.

Lemma scomp_assoc {s s' s'' s'''} (σ1 : subst s s') (σ2 : subst s' s'') (σ3 : subst s'' s''') :
  scomp (scomp σ1 σ2) σ3 = scomp σ1 (scomp σ2 σ3).
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_assoc : subst nf_subst.

Lemma scomp_scons_l {x s s' s''} t (σ1 : subst s s') (σ2 : subst s' s'') :
  scomp (scons x t σ1) σ2 = scons x (substitute σ2 t) (scomp σ1 σ2).
Proof. subst_ext i. depelim i ; simp_subst ; reflexivity. Qed.
#[export] Hint Rewrite @scomp_scons_l : subst nf_subst.

Lemma scomp_sup_l {x s s' s''} (σ1 : subst s s') (σ2 : subst (s' ▷ x) s'') :
  scomp (sup x σ1) σ2 = scons x (sapply σ2 I0) (scomp σ1 (scomp sshift σ2)).
Proof. subst_ext i. depelim i ; simp_subst ; try reflexivity. now nf_subst. Qed.
#[export] Hint Rewrite @scomp_sup_l : subst nf_subst.

Lemma scomp_sshift_scons {x s s'} t (σ : subst s s') :
  scomp sshift (scons x t σ) = σ.
Proof. subst_ext i. simp_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sshift_scons : subst nf_subst.

Lemma scomp_sshift_sup {x s s'} (σ : subst s s') :
  scomp sshift (sup x σ) = scomp σ sshift.
Proof. subst_ext i. nf_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sshift_sup : subst nf_subst.