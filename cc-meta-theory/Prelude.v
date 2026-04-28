From MetaTheory Require Export ListUtils.

From Stdlib Require Export Bool Nat List Lia PrimString Relations Morphisms Program.
From Stdlib Require Uint63.
From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
Export ListNotations.

(***********************************************************************)
(** * Global settings *)
(***********************************************************************)

(** Importing Ltac2 sets the default proof mode to Ltac2, but we want
    to keep it to Ltac (the default). *)
#[export] Set Default Proof Mode "Classic".

(** We allow [Equations] to use UIP instances, e.g. when deriving
    instances of [NoConfusion] or [NoConfusionHom]. *)
#[export] Set Equations With UIP.

(** Replace [Program]'s default obligation tactic. *)
#[export] Obligation Tactic := cbn beta zeta iota.

(***********************************************************************)
(** * Miscellaneous notations, functions, and lemmas *)
(***********************************************************************)

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).

Equations option_apply {A B} : option (A -> B) -> option A -> option B :=
option_apply (Some f) (Some x) := Some (f x) ;
option_apply _ _ := None.

Equations option_sequence {A} : list (option A) -> option (list A) :=
option_sequence [] := Some nil ;
option_sequence (None :: _) := None ;
option_sequence (Some x :: xs) := option_map (cons x) (option_sequence xs).

Lemma option_map_None {A B} (f : A -> B) :
  option_map f None = None.
Proof. reflexivity. Qed.

Lemma option_map_Some {A B} (f : A -> B) a :
  option_map f (Some a) = Some (f a).
Proof. reflexivity. Qed.

(** Ternary version of [sigT]. *)
Inductive sigT3 (A : Type) (P Q R : A -> Type) : Type :=
  existT3 : forall x : A, P x -> Q x -> R x -> sigT3 A P Q R.
Arguments sigT3 [A].
Arguments existT3 [A].

Notation "{ x & P & Q & R }" := (sigT3 (fun x => P) (fun x => Q) (fun x => R))
  (at level 0, x at level 99) : type_scope.

(** Notations to construct sigma-types. *)
Notation "⟨ x , y ⟩" := (existT _ x y) (format "⟨ x ,  y ⟩").
Notation "⟨ x , y1 , y2 ⟩" := (existT2 _ _ x y1 y2) (format "⟨ x ,  y1 ,  y2 ⟩").
Notation "⟨ x , y1 , y2 , y3 ⟩" := (existT3 _ _ _ x y1 y2 y3) (format "⟨ x ,  y1 ,  y2 ,  y3 ⟩").

(** Generalization of [split] to multiple goals. *)
Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** Ltac2 function to throw a [Tactic_failure] exception with a
    formatted error message. It must be used via the notation [tactic_failure!]. *)
Ltac2 tactic_failure (fmt : ('a, unit, message, 'r) format) : 'a :=
  Message.Format.kfprintf (fun msg =>
    Control.throw (Tactic_failure (Some msg))) fmt.

Ltac2 Notation "tactic_failure!" fmt(format) := tactic_failure fmt.

(***********************************************************************)
(** * Fixing setoid rewriting *)
(***********************************************************************)

(** Custom notation for [forall_relation], which allows writing [Proper]
    instances like [Proper (R ==> ∀ x y, S ==> T)].
    This should be included in a future release of Rocq. *)

Notation "∀ x .. y , R" :=
  (@forall_relation _ _ (fun x => .. (@forall_relation _ _ (fun y => R%signature)) ..))
  (right associativity, at level 55, x binder, y binder) : signature_scope.

Lemma flip_forall {A : Type} {B : A -> Type} (R R' : forall a, relation (B a))
  `(N : forall a, Normalizes (B a) (R a) (flip (R' a))) :
  Normalizes (forall a, B a) (forall_relation R) (flip (forall_relation R')).
Proof.
intros F G. split.
- intros H a. specialize (H a). now apply (N a) in H.
- intros H a. specialize (H a). now apply (N a) in H.
Qed.

Hint Extern 1 (Normalizes _ (forall_relation _) _) =>
  class_apply @flip_forall : typeclass_instances.

(***********************************************************************)
(** * Functional extensionality *)
(***********************************************************************)

(** Functional extensionality: two dependent functions
    are equal if they are pointwise equal. *)
Axiom functional_extensionality :
  forall (A : Type) (B : A -> Type) (f g : forall a : A, B a),
  (forall a, f a = g a) ->
  f = g.

(** The tactic [fun_ext x1 x2 ... xn] applies the functional extentionality
    axiom [n] times and introduces variables [x1] to [xn]. *)

Ltac2 fun_ext_ltac2 (x : ident) : unit :=
  lazy_match! (Control.goal ()) with
  | @eq ?ty _ _ =>
    lazy_match! Std.eval Std.Red.hnf ty with
    | forall _, _ =>
        apply functional_extensionality ;
        Std.intro (Some x) None
    | _ => tactic_failure!
            "Tactic fun_ext: the equality is at type %t which should be of the form (A -> B) or (forall x : A, B)."
            ty
    end
  | _ => tactic_failure! "Tactic fun_ext: the goal is not an equality"
  end.

Ltac fun_ext_ltac1 x :=
  let f := ltac2:(x |- fun_ext_ltac2 (Option.get (Ltac1.to_ident x))) in
  f x.

Tactic Notation "fun_ext" ident(x1) :=
  fun_ext_ltac1 x1.

Tactic Notation "fun_ext" ident(x1) ident(x2) :=
  fun_ext_ltac1 x1 ;
  fun_ext_ltac1 x2.

Tactic Notation "fun_ext" ident(x1) ident(x2) ident(x3) :=
  fun_ext_ltac1 x1 ;
  fun_ext_ltac1 x2 ;
  fun_ext_ltac1 x3.