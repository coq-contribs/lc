(** * Monads *)

Set Implicit Arguments.

Require Export Misc.

Record Monad : Type := {
  monad_carrier :> Set -> Set;
  bind : forall X Y : Set,
    (X -> monad_carrier Y) -> monad_carrier X -> monad_carrier Y;
  unit : forall X : Set, X -> monad_carrier X;
  bind_bind :
    forall (X Y Z : Set)
    (f : X -> monad_carrier Y) (g : Y -> monad_carrier Z)
    (x : monad_carrier X),
    bind Y Z g (bind X Y f x) =
      bind X Z (fun u => bind Y Z g (f u)) x;
  bind_unit : forall (X Y : Set) (f : X -> monad_carrier Y) (x : X),
    bind X Y f (unit X x) = f x;
  unit_bind : forall (X : Set) (x : monad_carrier X),
    bind X X (unit X) x = x
}.

Notation "x >>= f" := (@bind _ _ _ f x).

Hint Rewrite -> bind_bind bind_unit unit_bind : monad.

Hint Extern 1 (_ = _ : monad_carrier _ _) =>
  autorewrite with monad : monad.

Ltac monad := intros; autorewrite with monad; auto with monad.


Definition map (P : Monad) (X Y : Set)
  (f : X -> Y) (x : P X) : P Y :=
  x >>= (fun x => unit P (f x)).

Notation "x >>- f" := (@map _ _ _ f x).

Definition join (P : Monad) (X : Set) : P (P X) -> P X :=
  bind P X (fun x => x).

Definition ap (P : Monad) (X Y : Set)
  (f : P (X -> Y)) : P X -> P Y :=
  @bind P X Y (fun x => f >>= (fun ff => unit P (ff x))).

Definition lift (P : Monad) (X Y : Set)
  (f : X -> Y) : P X -> P Y :=
  @bind P X Y (fun u => unit P (f u)).

Definition lift2 (P : Monad) (X Y Z : Set)
  (f : X -> Y -> Z) (a : P X) (b : P Y) : P Z :=
  a >>= (fun x => b >>= fun y => unit P (f x y)).

Definition lift3 (P : Monad) (X Y Z W : Set)
  (f : X -> Y -> Z -> W) (a : P X) (b : P Y) (c : P Z) : P W :=
  a >>= (fun x => b >>= fun y => c >>= fun z => unit P (f x y z)).

Section Monad_Facts.

Variable P : Monad.

Lemma bind_congr : forall (X Y : Set) (f g : X -> P Y) (x y : P X),
  x = y -> (forall a, f a = g a) -> x >>= f = y >>= g.
Proof.
intros. replace g with f. subst y. reflexivity. extens; trivial.
Qed.

Lemma unit_bind_match : forall (X : Set)
  (f : X -> P X) (x : P X),
  (forall a, f a = unit P a) -> x >>= f = x.
Proof.
intros.
replace f with (@unit P X).
rewrite unit_bind.
reflexivity.
extens; auto.
Qed.

Hint Resolve bind_congr unit_bind_match : monad.

Lemma map_congr : forall (X Y : Set) (f g : X -> Y) (x y : P X),
  x = y -> (forall a, f a = g a) -> x >>- f = y >>- g.
Proof.
intros. subst y. replace g with f. reflexivity. extens. trivial.
Qed.

Hint Resolve map_congr : monad.

Lemma map_id : forall (X : Set) (f : X -> X) (x : P X),
  (forall a, f a = a) -> x >>- f = x.
Proof.
unfold map; monad.
Qed.

Hint Resolve map_id : monad.

Lemma map_unit : forall (X Y : Set) (f : X -> Y) (x : X),
  unit P x >>- f = unit P (f x).
Proof.
unfold map; monad.
Qed.

Lemma map_map : forall (X Y Z : Set)
  (f : X -> Y) (g : Y -> Z) (x : P X),
  (x >>- f) >>- g = x >>- (fun u => g (f u)).
Proof.
unfold map; monad.
Qed.

Lemma map_bind : forall (X Y Z : Set)
  (f : X -> Y) (g : Y -> P Z) (x : P X),
  x >>- f >>= g = x >>= (fun u => g (f u)).
Proof.
unfold map; monad.
Qed.

Lemma bind_map : forall (X Y Z : Set)
  (f : X -> P Y) (g : Y -> Z) (x : P X),
  x >>= f >>- g = x >>= (fun u => f u >>- g).
Proof.
unfold map; monad.
Qed.

Hint Rewrite -> map_unit map_map map_bind bind_map : monad.

Lemma join_join : forall (X : Set) (x : P (P (P X))),
  join P X (join P (P X) x) = join P X (x >>- (join P X)).
Proof.
unfold join; monad.
Qed.

Lemma join_unit : forall (X : Set) (x : P X),
  join P X (unit P x) = x.
Proof.
unfold join; monad.
Qed.

Lemma unit_join : forall (X : Set) (x : P X),
  join P X (x >>- @unit P X) = x.
Proof.
unfold join; monad.
Qed.

Lemma join_map : forall (X Y : Set) (f : X -> P Y) (x : P X),
  join P Y (x >>- f) = x >>= f.
Proof.
unfold join; monad.
Qed.

End Monad_Facts.

Hint Resolve unit_bind_match bind_congr map_congr map_id : monad.

Hint Rewrite -> map_unit map_map map_bind bind_map
                join_join join_unit unit_join join_map : monad.


(** ** Monad morphisms *)

Record Monad_Hom (P Q : Monad) : Type := {
  monad_hom :> forall X : Set, P X -> Q X;
  monad_hom_bind : forall (X Y : Set) (f : X -> P Y) (x : P X),
    monad_hom Y (x >>= f) =
      monad_hom X x >>= (fun a : X => monad_hom Y (f a));
  monad_hom_unit : forall (X : Set) (a : X),
    monad_hom X (unit P a) = unit Q a
}.

Hint Rewrite -> monad_hom_bind monad_hom_unit : monad.


Section Monad_Hom.

Variables P Q : Monad.

Section Facts.

Variable h : Monad_Hom P Q.

Lemma monad_hom_map : forall (X Y : Set) (f : X -> Y) (a : P X),
  h Y (a >>- f) = (h X a) >>- f.
Proof.
unfold map; monad.
Qed.

Hint Rewrite -> monad_hom_map : monad.

Lemma monad_hom_join : forall (X : Set) (x : P (P X)),
  h X (join P X x) = join Q X (h (P X) x >>- h X).
Proof.
unfold join; monad.
Qed.

Hint Rewrite -> monad_hom_join : monad.

Lemma monad_hom_extens : forall (f g : Monad_Hom P Q),
  (forall X x, f X x = g X x) -> f = g.
Proof.
intros [f f_bind f_unit] [g g_bind g_unit].
simpl. intros.
assert (f = g).
apply extens_dep with (T := fun X : Set => P X -> Q X).
intro X. extens. trivial.
subst g.
replace g_bind with f_bind. 2: apply proof_irrelevance.
replace g_unit with f_unit. 2: apply proof_irrelevance.
reflexivity.
Qed.

End Facts.

End Monad_Hom.

Hint Rewrite -> monad_hom_map monad_hom_join : monad.
