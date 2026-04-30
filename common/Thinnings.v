(** This file defines thinnings, i.e. order-preserving renamings. *)

From Common Require Import Index.

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
