(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Simple (untyped) Lambda Calculus *)

Set Implicit Arguments.

Require Import Quot.
Require Export Slc.
Opaque app1.

Section Lc.

Let r X : Eqv (term X) :=
  Build_Eqv (@lcr X) (@lcr_rfl X) (@lcr_sym X) (@lcr_trs X).
Implicit Arguments r [X].

Definition lc (X : Set) : Set := term X // r.

Definition lc_class (X : Set) : term X -> lc X := class r.
Notation "/ x" := (lc_class x).

Lemma lc_class_eq : forall (X : Set) (x y : term X),
  x == y -> /x = /y.
Proof.
unfold lc_class. intros.
apply class_eq with (r := @r X). assumption.
Qed.
Hint Resolve lc_class_eq.

Lemma lc_class_rel : forall (X : Set) (x y : term X),
  /x = /y -> x == y.
Proof.
unfold lc_class; simpl. intros.
apply class_rel with (r := @r X). assumption.
Qed.
Hint Resolve lc_class_rel.

Lemma lc_class_surj : forall (X : Set) (u : lc X),
  exists a, /a = u.
Proof.
unfold r; simpl. intros. class u v. split with v. reflexivity.
Qed.
Hint Resolve lc_class_surj.

Definition lc_factor (X Y : Set) (f : term X -> Y)
  (Hf : forall x y, x == y -> f x = f y) : lc X -> Y :=
  factor r f Hf.

Lemma lc_factorize : forall (X Y : Set) (f : term X -> Y)
  (H : forall x y, x == y -> f x = f y),
    forall x,  lc_factor f H (/x) = f x.
Proof.
unfold lc_factor, lc_class; simpl; intros. apply factorize.
Qed.
Hint Resolve lc_factorize.

Definition lc_factor1 (X Y : Set) (f : term X -> term Y)
  (Hf : forall x y, x == y -> f x == f y) : lc X -> lc Y :=
  factor1 r r f Hf.

Lemma lc_factorize1 : forall (X Y : Set) (f : term X -> term Y)
  (H : forall x y, x == y -> f x == f y),
    forall x,  lc_factor1 f H (/x) = /f x.
Proof.
unfold lc, lc_factor1, lc_class; simpl; intros. apply factorize1.
Qed.
Hint Resolve lc_factorize1.

Definition lc_factor2 (X Y Z : Set)
  (f : term X -> term Y -> term Z)
  (Hf : forall x y z w, x == y -> z == w -> f x z == f y w) :
    lc X -> lc Y -> lc Z :=
  factor2 r r r f Hf.

Lemma lc_factorize2 : forall (X Y Z : Set)
  (f : term X -> term Y -> term Z)
  (H : forall x y z w, x == y -> z == w -> f x z == f y w),
    forall x y,  lc_factor2 f H (/x) (/y) = /f x y.
Proof.
unfold lc, lc_factor2, lc_class; simpl; intros. apply factorize2.
Qed.
Hint Resolve lc_factorize2.

Lemma lc_fun_lift : forall (X Y : Set) (f : X -> lc Y),
  exists g : X -> term Y, f = fun x => /g x.
Proof.
intros. lift_fun f f'. exists f'. reflexivity.
Qed.

Opaque lc lc_class lc_factor lc_factor1 lc_factor2.

Definition lc_abs (X : Set) : lc (option X) -> lc X :=
  lc_factor1 (@abs X) (@lcr_abs X).

Lemma lc_abs_factorize : forall (X : Set) (x : term (option X)),
  lc_abs (/x) = / abs x.
Proof.
unfold lc_abs. intros. apply lc_factorize1.
Qed.

Opaque lc_abs.

Definition lc_app1 (X : Set) : lc X -> lc (option X) :=
  lc_factor1 (@app1 X) (@lcr_app1 X).

Lemma lc_app1_factorize : forall (X : Set) (x : term X),
  lc_app1 (/x) = / app1 x.
Proof.
unfold lc_app1. intros. apply lc_factorize1.
Qed.

Opaque lc_app1.

Definition lc_app (X : Set) : lc X -> lc X -> lc X :=
  lc_factor2 (@app X) (@lcr_app X).

Lemma lc_app_factorize : forall (X : Set) (x y : term X),
  lc_app (/x) (/y) = / app x y.
Proof.
unfold lc_app. intros. apply lc_factorize2.
Qed.

Opaque lc_app.

Definition lc_var (X : Set) (x : X) : lc X := / var x.


Definition lc_fct (X Y : Set) (f : X -> Y) : lc X -> lc Y :=
  lc_factor1 (fct f) (lcr_fct f).

Lemma lc_fct_factorize : forall (X Y : Set)
  (f : X -> Y) (x : term X),
  lc_fct f (/x) = /fct f x.
Proof.
unfold lc_fct; intros. apply lc_factorize1.
Qed.

Opaque lc_fct.

Definition lc_comm (X Y : Set)
  (f : X -> lc Y) (x : option X) : lc (option Y) :=
  match x with
  | Some a => lc_fct (@Some Y) (f a)
  | None => lc_var None
  end.

Fixpoint lc_subst_fix (X Y : Set) (f : X -> lc Y)
  (x : term X) { struct x } : lc Y :=
  match x with
  | var x => f x
  | app x y => lc_app (lc_subst_fix f x) (lc_subst_fix f y)
  | abs x => lc_abs (lc_subst_fix (lc_comm f) x)
  end.

Remark lc_subst_fix_factorize : forall (X Y : Set)
  (f : X -> term Y) (x : term X),
  lc_subst_fix (fun a => /f a) x = /(x //= f).
Proof.
intros.
generalize Y f; clear Y f.
induction x; simpl; intros.
reflexivity.
rewrite IHx1.
rewrite IHx2.
apply lc_app_factorize.
rewrite <- lc_abs_factorize.
congr.
rewrite <- IHx.
congr.
extens u.
destruct u; simpl.
rewrite lc_fct_factorize.
reflexivity.
reflexivity.
Qed.

Remark lc_subst_fix_wd : forall (X Y : Set)
  (f : X -> lc Y) (x y : term X),
  x == y -> lc_subst_fix f x = lc_subst_fix f y.
Proof.
intros. destruct (lc_fun_lift f) as (f', Hf). subst f.
do 2 rewrite lc_subst_fix_factorize. apply lc_class_eq.
apply lcr_subst. intros. apply lcr_rfl. assumption.
Qed.

Definition lc_subst (X Y : Set) (f : X -> lc Y) : lc X -> lc Y :=
  lc_factor (lc_subst_fix f) (lc_subst_fix_wd f).

Lemma lc_subst_factorize : forall (X Y : Set)
  (f : X -> term Y) (x : term X),
  lc_subst (fun a => /f a) (/x) = /(x //= f).
Proof.
unfold lc_subst. intros.
rewrite lc_factorize. apply lc_subst_fix_factorize.
Qed.

Opaque lc_subst.

Lemma lc_fct_as_subst : forall (X Y : Set) (f : X -> Y),
  lc_fct f = lc_subst (fun a => lc_var (f a)).
Proof.
unfold lc_var. intros. extens.
destruct (lc_class_surj x) as [y Hy]. subst x.
rewrite lc_fct_factorize. rewrite fct_as_subst.
rewrite <- lc_subst_factorize. reflexivity.
Qed.

Lemma lc_subst_assoc : forall (X Y Z : Set)
  (f : X -> lc Y) (g : Y -> lc Z) (x : lc X),
  lc_subst g (lc_subst f x) =
    lc_subst (fun a => lc_subst g (f a)) x.
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_subst_factorize.
destruct (lc_fun_lift g) as (g', Hg). subst g.
rewrite lc_subst_factorize.
rewrite subst_subst.
rewrite <- lc_subst_factorize.
congr. extens. rewrite lc_subst_factorize. reflexivity.
Qed.

Lemma lc_subst_var : forall (X Y : Set) (f : X -> lc Y) (x : X),
  lc_subst f (lc_var x) = f x.
Proof.
unfold lc_var. intros.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_subst_factorize. rewrite subst_var. reflexivity.
Qed.

Lemma lc_var_subst : forall (X : Set) (x : lc X),
  lc_subst (@lc_var X) x = x.
Proof.
unfold lc_var. intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_subst_factorize.
rewrite var_subst. reflexivity.
Qed.

Lemma lc_subst_abs : forall (X Y : Set)
  (f : X -> lc Y) (x : lc (option X)),
  lc_subst f (lc_abs x) = lc_abs (lc_subst (lc_comm f) x).
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_abs_factorize.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_subst_factorize. simpl.
rewrite <- lc_abs_factorize. congr.
rewrite <- lc_subst_factorize. congr.
extens. destruct x; simpl. 2:reflexivity.
rewrite lc_fct_factorize. reflexivity.
Qed.

Lemma lc_subst_app1 : forall (X Y : Set)
  (f : X -> lc Y) (x : lc X),
  lc_subst (lc_comm f) (lc_app1 x) = lc_app1 (lc_subst f x).
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_app1_factorize.
rewrite lc_subst_factorize.
rewrite lc_app1_factorize.
replace (lc_comm (fun x : X => / f' x))
  with (fun a => /comm f' a).
rewrite lc_subst_factorize.
rewrite subst_app1. rewrite app1_app.
unfold shift. rewrite fct_subst. reflexivity.
extens a; destruct a; simpl. 2:reflexivity.
rewrite lc_fct_factorize. reflexivity.
Qed.

Lemma lc_eta : forall (X : Set) (x : lc X),
  lc_abs (lc_app1 x) = x.
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_app1_factorize. rewrite lc_abs_factorize.
apply lc_class_eq. apply lcr_eta.
Qed.

Lemma lc_beta : forall (X : Set) (x : lc (option X)),
  lc_app1 (lc_abs x) = x.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_abs_factorize. rewrite lc_app1_factorize.
apply lc_class_eq. apply lcr_beta. 
rewrite app1_app. unfold shift. simpl.
apply beta_intro2. rewrite subst_fct.
apply var_subst_match.
destruct u; reflexivity.
Qed.

End Lc.
