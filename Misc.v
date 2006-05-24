(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Miscellaneous *)

Set Implicit Arguments.

(** ** Axioms *)

Axiom functional_choice : forall (A B : Type) (R : A -> B -> Prop),
  (forall x : A,  exists y : B, R x y) ->
  exists f : A -> B, (forall x : A, R x (f x)).

Axiom proof_irrelevance : forall (A : Prop) (H1 H2 : A), H1 = H2.
Hint Resolve proof_irrelevance.

Axiom extens_dep : forall (X : Type) (T : X -> Type)
  (f g : forall x : X, T x),
  (forall x : X, f x = g x) -> f = g.

Lemma extens : forall (X Y : Type) (f g : X -> Y),
  (forall x, f x = g x) -> f = g.
Proof.
intros.
apply extens_dep with (T := fun _ : X => Y).
assumption.
Qed.

Tactic Notation "extens" := apply extens; intro.
Tactic Notation "extens" ident(id) := apply extens; intro id.


(** ** Notations *)

Reserved Notation "x >>= f" (at level 42, left associativity).
Reserved Notation "x >>- f" (at level 42, left associativity).
Reserved Notation "x >>>= f" (at level 42, left associativity).
Reserved Notation "x >>>- f" (at level 42, left associativity).

Reserved Notation "x //= f" (at level 42, left associativity).
Reserved Notation "x ///= f" (at level 42, left associativity).
Reserved Notation "x //- f" (at level 42, left associativity).
Reserved Notation "x ///- f" (at level 42, left associativity).

Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y :> X"
  (at level 70, y at next level, no associativity).

Reserved Notation "x [=] y" (at level 70, no associativity).
Reserved Notation "x [=] y :> X"
  (at level 70, y at next level, no associativity).


(** ** Poor man congruence tactic *)
Ltac congr :=
  match goal with
  | |- ?f ?a = ?f ?b =>
      change ((fun u => f a = f u) b);
      replace b with a; trivial with *
  | |- ?f ?a ?a2= ?f ?b ?a2  =>
      change ((fun u => f a a2 = f u a2) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a= ?f ?b1 ?b =>
      change ((fun u => f a1 a = f b1 u) b);
      replace b with a; trivial with *
  | |- ?f ?a ?a2 ?a3 = ?f ?b ?a2 ?a3 =>
      change ((fun u => f a a2 a3 = f u a2 a3) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a ?a3 = ?f ?b1 ?b ?a3 =>
      change ((fun u => f a1 a a3 = f b1 u a3) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a = ?f ?b1 ?b2 ?b =>
      change ((fun u => f a1 a2 a = f b1 b2 u) b);
      replace b with a; trivial with *
  | |- ?f ?a ?a2 ?a3 ?a4 = ?f ?b ?a2 ?a3 ?a4 =>
      change ((fun u => f a a2 a3 a4 = f u a2 a3 a4) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a ?a3 ?a4 = ?f ?b1 ?b ?a3 ?a4 =>
      change ((fun u => f a1 a a3 a4 = f b1 u a3 a4) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a ?a4 = ?f ?b1 ?b2 ?b ?a4 =>
      change ((fun u => f a1 a2 a a4 = f b1 b2 u a4) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a = ?f ?b1 ?b2 ?b3 ?b =>
      change ((fun u => f a1 a2 a3 a = f b1 b2 b3 u) b);
      replace b with a; trivial with *
  | |- ?f ?a ?a2 ?a3 ?a4 ?a5 = ?f ?b ?a2 ?a3 ?a4 ?a5 =>
      change ((fun u => f a a2 a3 a4 a5 = f u a2 a3 a4 a5) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a ?a3 ?a4 ?a5 = ?f ?a1 ?b ?a3 ?a4 ?a5 =>
      change ((fun u => f a1 a a3 a4 a5 = f a1 u a3 a4 a5) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a ?a4 ?a5 = ?f ?a1 ?a2 ?b ?a4 ?a5 =>
      change ((fun u => f a1 a2 a a4 a5 = f a1 a2 u a4 a5) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a ?a5 = ?f ?a1 ?a2 ?a3 ?b ?a5 =>
      change ((fun u => f a1 a2 a3 a a5 = f a1 a2 a3 u a5) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a4 ?a = ?f ?a1 ?a2 ?a3 ?a4 ?b =>
      change ((fun u => f a1 a2 a3 a4 a = f a1 a2 a3 a4 u) b);
      replace b with a; trivial with *
  | |- ?f ?a ?a2 ?a3 ?a4 ?a5 ?a6 = ?f ?b ?a2 ?a3 ?a4 ?a5 ?a6 =>
      change ((fun u => f a a2 a3 a4 a5 a6 = f u a2 a3 a4 a5 a6) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a ?a3 ?a4 ?a5 ?a6 = ?f ?a1 ?b ?a3 ?a4 ?a5 ?a6 =>
      change ((fun u => f a1 a a3 a4 a5 a6 = f a1 u a3 a4 a5 a6) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a ?a4 ?a5 ?a6 = ?f ?a1 ?a2 ?b ?a4 ?a5 ?a6 =>
      change ((fun u => f a1 a2 a a4 a5 a6 = f a1 a2 u a4 a5 a6) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a ?a5 ?a6 = ?f ?a1 ?a2 ?a3 ?b ?a5 ?a6 =>
      change ((fun u => f a1 a2 a3 a a5 a6 = f a1 a2 a3 u a5 a6) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a4 ?a ?a6 = ?f ?a1 ?a2 ?a3 ?a4 ?b ?a6 =>
      change ((fun u => f a1 a2 a3 a4 a a6 = f a1 a2 a3 a4 u a6) b);
      replace b with a; trivial with *
  | |- ?f ?a1 ?a2 ?a3 ?a4 ?a5 ?a = ?f ?a1 ?a2 ?a3 ?a4 ?a5 ?b =>
      change ((fun u => f a1 a2 a3 a4 a5 a = f a1 a2 a3 a4 a5 u) b);
      replace b with a; trivial with *
  end.

Hint Extern 1 (?x = ?y) => congr.


(** ** Handy terms for [option] *)

Definition optmap (X Y : Set)
  (f : X -> Y) (x : option X) : option Y := 
  match x with Some a => Some (f a) | new => None end.

Definition default (X Y : Set)
  (f : X -> Y) (def : Y) (x : option X) : Y :=
  match x with Some a => f a | new => def end.
