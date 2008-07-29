(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Modules *)

Set Implicit Arguments.

Require Export Monad.

Record Mod (U : Monad) : Type := {
  mod_carrier :> Set -> Set;
  mbind : forall (X Y: Set) (f : X -> U Y) (x : mod_carrier X),
    mod_carrier Y;
  mbind_mbind : forall (X Y Z : Set)
    (f : X -> U Y) (g : Y -> U Z) (x : mod_carrier X),
    mbind Z g (mbind Y f x) = mbind Z (fun u => f u >>= g) x;
  unit_mbind : forall (X : Set) (x : mod_carrier X),
    mbind X (@unit U X) x = x
}.

Notation "x >>>= f" := (@mbind _ _ _ _ f x).

Hint Rewrite -> mbind_mbind unit_mbind : mod.

Hint Extern 1 (_ = _ :> @mod_carrier _ _ _) =>
  autorewrite with mod : mod.

Ltac mod :=
  intros;
  autorewrite with monad mod;
  auto with mod monad.

Definition mmap (U : Monad) (T : Mod U)
  (X Y : Set) (f : X -> Y) (x : T X) : T Y :=
  x >>>= fun x => unit U (f x).

Notation "x >>>- f" := (@mmap _ _ _ _ f x).

Definition mlift (U : Monad) (T : Mod U)
  (X Y : Set) (f : X -> Y) : T X -> T Y :=
  @mbind U T _ _ (fun x => unit U (f x)).

Definition mlift2 (U : Monad) (T : Mod U) (X Y Z : Set)
  (f : X -> Y -> Z) (a : U X) (b : T Y) : T Z :=
  b >>>= (fun y => a >>= fun x => unit U (f x y)).

Section Mod_Facts.

Variable P : Monad.
Variable M : Mod P.

Lemma mbind_congr : forall (X Y : Set) (f g : X -> P Y) (x y : M X),
  x = y -> (forall a, f a = g a) -> x >>>= f = y >>>= g.
Proof.
intros. subst y. replace g with f. reflexivity. extens. trivial.
Qed.

Hint Resolve mbind_congr : mod.

Lemma unit_mbind_match : forall (X : Set) (f : X -> P X) (x : M X),
  (forall a, f a = unit P a) -> x >>>= f = x.
Proof.
intros. replace f with (@unit P X). mod. extens. auto.
Qed.

Lemma mmap_mbind : forall (X Y Z : Set)
  (f : X -> P Y) (g : Y -> Z) (x : M X),
  x >>>= f >>>- g = x >>>= (fun u => f u >>- g).
Proof.
unfold mmap; mod.
Qed.

Lemma mbind_mmap : forall (X Y Z : Set)
  (f : X -> Y) (g : Y -> P Z) (x : M X),
  x >>>- f >>>= g = x >>>= fun u : X => g (f u).
Proof.
unfold mmap. mod.
Qed.

Lemma mmap_mmap : forall (X Y Z : Set)
  (f : X -> Y) (g : Y -> Z) (x : M X),
  x >>>- f >>>- g = x >>>- fun u : X => g (f u).
Proof.
unfold mmap. mod.
Qed.

End Mod_Facts.

Hint Resolve unit_mbind_match mbind_congr : mod.
Hint Rewrite -> mmap_mbind mbind_mmap mmap_mmap : mod.

Record Mod_Hom (U : Monad) (S T : Mod U) : Type := {
  mod_hom_carrier :> forall X : Set, S X -> T X;
  mod_hom_mbind : forall (X Y : Set) (f : X -> U Y) (x : S X),
    mod_hom_carrier Y (x >>>= f) = mod_hom_carrier X x >>>= f
}.

Hint Rewrite -> mod_hom_mbind : mod.

Lemma mod_hom_extens : forall (U : Monad)
  (S T : Mod U) (f g : Mod_Hom S T),
  (forall X (x : S X), f X x = g X x) -> f = g.
Proof.
destruct f as [f Hf1 Hf2]. destruct g as [g Hg1 Hg2].
simpl. intros.
cut (f = g).
destruct 1. replace Hg1 with Hf1. reflexivity.
apply proof_irrelevance.
apply extens_dep with (T := fun X : Set => S X -> T X).
intros X.
apply extens.
trivial.
Qed.



(** ** Tautological module *)

Definition Taut_Mod (U : Monad) : Mod U :=
  Build_Mod U U (@bind U) (@bind_bind U) (@unit_bind U).

Coercion Taut_Mod : Monad >-> Mod.


(** ** Pull-back module *)

Section Pull_back.

Variable (P Q: Monad) (h : Monad_Hom P Q) (M : Mod Q).

Let bb (X Y : Set) (f : X -> P Y) (x : M X) : M Y :=
  x >>>= fun u => h Y (f u).

Remark bb_bb : forall (X Y Z : Set)
  (f : X -> P Y) (g : Y -> P Z) (x : M X),
  bb Z g (bb Y f x) = bb Z (fun u : X => f u >>= g) x.
Proof.
unfold bb; mod.
Qed.

Remark unit_bb : forall (X : Set) (x : M X),
  bb X (unit P (X:=X)) x = x.
Proof.
unfold bb; mod.
Qed.

Definition PB : Mod P := Build_Mod P M bb bb_bb unit_bb.

End Pull_back.
