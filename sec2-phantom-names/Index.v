(** This file defines:
    - (well-scoped) de Bruijn indices.
    - thinnings, i.e. order-preserving renamings. *)

From PhantomNames Require Export Typeclasses.

(***********************************************************************)
(** * De Bruijn indices *)
(***********************************************************************)

(** [index s] is the type of de Bruijn indices in scope [s].
    You can think of an index as a natural number which
    tells you how many binders to count up (i.e. going towards the root)
    until you find the corresponding variable. *)
Inductive index : scope -> Type :=
| I0 {s x} : index (s ▷ x)
| IS {s x} : index s -> index (s ▷ x).

Derive Signature NoConfusion NoConfusionHom for index.

(** Boolean equality test on de Bruijn indices. *)
Equations index_eq {s} : index s -> index s -> bool :=
index_eq I0 I0 := true ;
index_eq (IS i) (IS i') := index_eq i i' ;
index_eq _ _ := false.

Lemma index_eq_spec {s} (i i' : index s) :
  reflect (i = i') (index_eq i i').
Proof.
funelim (index_eq i i').
- constructor. reflexivity.
- constructor. intros H ; depelim H.
- constructor. intros H ; depelim H.
- destruct H ; constructor.
  + f_equal. assumption.
  + intros H ; depelim H. auto.
Qed.

(** [idx_of x] returns the index corresponding to the tag [x]
    in the ambient scope [s]. *)
Fixpoint idx_of (x : tag) {s} {wit : scope_mem x s} : index s :=
  match wit with
  | scope_mem_here _ => I0
  | scope_mem_skip _ wit => IS (@idx_of x _ wit)
  end.

(** [tag_of i] creates a tag corresponding to a de Bruijn index [x],
    along with a witness that [x] is included in scope [s]. *)
Fixpoint tag_of {s} (i : index s) : { x & scope_mem x s } :=
  match i with
  | @I0 s x => existT _ x (scope_mem_here x)
  | @IS s x i =>
    let '(existT _ y H) := tag_of i in
    existT _ y (scope_mem_skip x H)
  end.

(***********************************************************************)
(** * Thinnings *)
(***********************************************************************)

(** [thinning s s'] is the type of thinnings from scope [s] to scope [s'].
    Thinnings are order-preserving renamings and are thus injective.

    We could think of simply encoding a thinning as a pair of a renaming (i.e. a
    function [index s -> index s']) and a proof of monotonicity.
    We do *not* choose this encoding because it makes it
    impossible to define the function [thicken] (we would only be able to
    write [thicken] as a relation).
*)
Inductive thinning : scope -> scope -> Type :=
| ThinNil : thinning ∅ ∅
| ThinSkip {s s'} x : thinning s s' -> thinning s (s' ▷ x)
| ThinKeep {s s'} x : thinning s s' -> thinning (s ▷ x) (s' ▷ x).

Arguments ThinSkip {s s'}.
Arguments ThinKeep {s s'}.

Derive Signature NoConfusion NoConfusionHom for thinning.

(** Identity thinning. *)
Equations tid {s} : thinning s s :=
@tid ∅ := ThinNil ;
@tid (s ▷ x) := ThinKeep x tid.

(** Shift thinning. *)
Definition tshift {s x} : thinning s (s ▷ x) :=
  ThinSkip x tid.

(** [tcomp δ1 δ2] is the composition of the thinning [δ1] followed by the thinning [δ2]. *)
Equations tcomp {s s' s''} : thinning s s' -> thinning s' s'' -> thinning s s'' :=
tcomp ThinNil δ2 := δ2 ;
tcomp δ1 (ThinSkip x δ2) := ThinSkip _ (tcomp δ1 δ2) ;
tcomp (ThinKeep x δ1) (ThinKeep _ δ2) := ThinKeep x (tcomp δ1 δ2) ;
tcomp (ThinSkip x δ1) (ThinKeep _ δ2) := ThinSkip x (tcomp δ1 δ2).

(** [replace_tag x] is a thinning which replaces the tag of variable [I0] with [x].
    Computationally it behaves as the identity. *)
Definition replace_tag {s x0} (x : tag) : thinning (s ▷ x0) (s ▷ x).
destruct x0. destruct x. exact tid.
Defined.

(** Apply a thinning to an index. *)
Equations tapply {s s'} : thinning s s' -> index s -> index s' :=
tapply (ThinSkip x δ) i := IS (tapply δ i) ;
tapply (ThinKeep x δ) I0 := I0 ;
tapply (ThinKeep x δ) (IS i) := IS (tapply δ i).

(** [wk_idx] is a thinning which weakens any index [i] into the ambient scope. *)
Fixpoint wk_idx {s s'} {wit : scope_incl s s'} : thinning s s' :=
  match wit with
  | scope_incl_refl => tid
  | scope_incl_keep x wit => ThinKeep x (@wk_idx _ _ wit)
  | scope_incl_skip x wit => ThinSkip x (@wk_idx _ _ wit)
  end.
