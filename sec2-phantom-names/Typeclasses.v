(** This file defines typeclasses [scope_mem] and [scope_incl] for
    scope membership and inclusion. *)

From PhantomNames Require Export Scope.

(***********************************************************************)
(** * Typeclass for scope membership *)
(***********************************************************************)

(** [scope_mem x s] is a witness of the fact that variable [x]
    occurs in scope [s]. *)
Inductive scope_mem (x : tag) : scope -> Type :=
| scope_mem_here s : scope_mem x (s ▷ x)
| scope_mem_skip y s : scope_mem x s -> scope_mem x (s ▷ y).

Arguments scope_mem_here x {s}.
Arguments scope_mem_skip {x} y {s}.

(** We declare [scope_mem] as a typeclass to allow synthesizing
    a witness automatically. *)
Existing Class scope_mem.
#[export] Existing Instance scope_mem_here.
#[export] Existing Instance scope_mem_skip.

(***********************************************************************)
(** * Typeclass for scope inclusion *)
(***********************************************************************)

(** [scope_incl s s'] is a witness of the fact that the scope [s]
    is included in the scope [s'], i.e. that there exists a thinning
    from [s] to [s']. *)
Inductive scope_incl : scope -> scope -> Type :=
| scope_incl_refl s : scope_incl s s
| scope_incl_keep x s s' : scope_incl s s' -> scope_incl (s ▷ x) (s' ▷ x)
| scope_incl_skip x s s' : scope_incl s s' -> scope_incl s (s' ▷ x).

Arguments scope_incl_refl {s}.
Arguments scope_incl_keep x {s s'}.
Arguments scope_incl_skip x {s s'}.

(** We declare [scope_incl] as a typeclass to allow synthesizing
    a witness automatically. *)
Existing Class scope_incl.
#[export] Existing Instance scope_incl_refl.
#[export] Existing Instance scope_incl_keep.
#[export] Existing Instance scope_incl_skip.

#[export] Instance scope_incl_empty s : scope_incl ∅ s.
  induction s ; typeclasses eauto.
Defined.
