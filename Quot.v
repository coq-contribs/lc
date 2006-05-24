(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Equivalence relations and quotients *)

Set Implicit Arguments.

Require Export Misc.


(** ** Equivalence relations *)

Record Eqv (A : Set) : Type := {
  eqv_data :> forall x y : A, Prop;
  eqv_rfl : forall x, eqv_data x x;
  eqv_sym : forall x y, eqv_data y x -> eqv_data x y;
  eqv_trs : forall x y z,
    eqv_data x y -> eqv_data y z -> eqv_data x z
}.

Hint Immediate eqv_sym.
Hint Resolve eqv_rfl eqv_trs.

Lemma eq_eqv : forall (A : Set) (r : Eqv A) x y, x = y -> r x y.
Proof.
destruct 1. apply eqv_rfl.
Qed.

Hint Resolve eq_eqv.


(** ** Quotients *)

Parameter quotient : forall (X : Set) (r : Eqv X), Set.
Implicit Arguments quotient [].
Infix "//" := quotient
  (at level 45, right associativity) : quotient.
Open Scope quotient.

Parameter class : forall (X : Set) (r : Eqv X), X -> X//r.
Implicit Arguments class [X].
Notation "x / r" := (class r x) : quotient.

Axiom class_eq : forall (X : Set) (r : Eqv X) (x y : X),
  r x y -> x/r = y/r.
Hint Resolve class_eq.

Axiom class_rel : forall (X : Set) (r : Eqv X) (x y : X),
  x/r = y/r -> r x y.
Hint Resolve class_rel.

Axiom class_surj : forall (X : Set) (r : Eqv X) (u : X//r),
  exists a, a/r = u.
Hint Resolve class_surj.

Parameter factor : forall (X : Set) (r : Eqv X) Y (f : X -> Y)
  (Hf : forall x y, r x y -> f x = f y),
  X//r -> Y.
Implicit Arguments factor [X Y].

Axiom factorize : forall X (r : Eqv X) Y (f : X -> Y)
  (H : forall x y, r x y -> f x = f y),
    forall x ,  factor r f H (x/r) = f x.
Hint Resolve factorize.
Hint Rewrite factorize : quotient.

Lemma factor_extens : forall (X : Set) (r : Eqv X) Y
  (f : X -> Y) (Hf : forall x y, r x y -> f x = f y)
  (g : X -> Y) (Hg : forall x y, r x y -> g x = g y)
  (H : f = g),
  factor r f Hf = factor r g Hg.
Proof.
destruct 1. replace Hg with Hf.
reflexivity.
apply proof_irrelevance.
Qed.

Section Factor1.

Variable (X : Set) (rX : Eqv X).
Variable (Y : Set) (rY : Eqv Y).
Variable f : X -> Y.
Hypothesis Hf : forall x y, rX x y -> rY (f x) (f y).

Definition factor1 : X // rX -> Y // rY.
Proof.
apply (factor rX (fun x => f x / rY)).
abstract auto.
Defined.

Lemma factorize1 : forall x, factor1 (x / rX) = f x / rY.
Proof.
unfold factor1.
intros. rewrite factorize. reflexivity.
Qed.

End Factor1.

Implicit Arguments factor1 [X Y].
Implicit Arguments factorize1 [X Y].
Hint Rewrite factorize1 : quotient.

Ltac class x u :=
  destruct (class_surj x) as [u []]; try clear x.

Lemma factor1_extens : forall X (rX : Eqv X) Y (rY : Eqv Y)
  (f : X -> Y) (Hf : forall x y, rX x y -> rY (f x) (f y))
  (g : X -> Y) (Hg : forall x y, rX x y -> rY (g x) (g y))
  (H : forall x, rY (f x) (g x)) x,
  factor1 rX rY f Hf x = factor1 rX rY g Hg x.
Proof.
intros. class x u.
do 2 rewrite factorize1. auto.
Qed.

Section Factor2.

Variable (X : Set) (rX : Eqv X).
Variable (Y : Set) (rY : Eqv Y).
Variable (Z : Set) (rZ : Eqv Z).
Variable f : X -> Y -> Z.

Hypothesis Hf : forall x y z w,
  rX x y -> rY z w -> rZ (f x z) (f y w).

Let h  (x : X) : Y // rY -> Z // rZ.
Proof.
intro. apply (factor1 rY rZ (f x)). abstract auto.
Defined.

Remark rmk : forall x y, rX x y -> h x = h y.
Proof.
unfold h. intros. extens u. class u v.
do 2 rewrite factorize1. auto.
Qed.

Definition factor2 : X // rX -> Y // rY -> Z // rZ.
Proof.
apply (factor rX h). exact rmk.
Defined.

Lemma factorize2 : forall x y,
  factor2 (x / rX) (y / rY) = f x y / rZ.
Proof.
unfold factor2, h. intros.
rewrite factorize. rewrite factorize1. auto.
Qed.

End Factor2.

Implicit Arguments factor2 [X Y Z].
Implicit Arguments factorize2 [X Y Z].

Hint Rewrite factorize2 : quotient.

Lemma factor2_extens :
  forall X (rX : Eqv X) Y (rY : Eqv Y) Z (rZ : Eqv Z)
  (f : X -> Y -> Z)
  (Hf : forall x y z w, rX x y -> rY z w -> rZ (f x z) (f y w))
  (g : X -> Y -> Z)
  (Hg : forall x y z w, rX x y -> rY z w -> rZ (g x z) (g y w))
  (H : forall x y, rZ (f x y) (g x y)) x y,
  factor2 rX rY rZ f Hf x y = factor2 rX rY rZ g Hg x y.
Proof.
intros. class x u. class y v.
do 2 rewrite factorize2. auto.
Qed.

Lemma lift_fun : forall (X Y : Set) (r : Eqv Y) (f : X -> Y // r),
  exists h : X -> Y, f = fun x => h x / r.
Proof.
intros.
pose (R := fun x y => f x = y / r).
destruct (functional_choice R) as [g Hg].
unfold R. intros.
class (f x) u. exists u. reflexivity.
exists g. extens. rewrite Hg. reflexivity.
Qed.

Ltac lift_fun f g :=
  destruct (lift_fun f) as [g Hlift_f]; subst f.
