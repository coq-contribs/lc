(** *  Syntactic Lambda calculus *)

(** Lambda terms modulo alpha-equivalence (and its monadic
    structure given by the substitution). *)

Set Implicit Arguments.

Require Export Misc.

Implicit Type X Y Z : Set.

Inductive term (X : Set) : Set :=
  | var : X -> term X
  | app : term X -> term X -> term X
  | abs : term (option X) -> term X.

Hint Extern 1 (_ = _ :> term _) =>
  autorewrite with slc; simpl : slc.

Fixpoint fct (X Y : Set) (f : X -> Y)
  (x : term X) { struct x } : term Y :=
  match x with
  | var a => var (f a)
  | app x y => app (x //- f) (y //- f)
  | abs x => abs (x //- (optmap f))
  end
where "x //- f" := (@fct _ _ f x) : lc_scope.

Open Scope lc_scope.

Lemma fct_fct :
  forall (X Y Z : Set) (f : X -> Y) (g : Y -> Z) (x : term X) ,
  x //- f //- g = x //- (fun u => g (f u)).
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; auto.
congr. rewrite IHx.
congr; clear x IHx.
extens x; destruct x; reflexivity.
Qed.
Hint Rewrite -> fct_fct : slc.

Lemma fct_id : forall (X : Set) (f : X -> X) (x : term X),
  (forall u, f u = u) -> x //- f = x.
Proof.
induction x; intros; simpl; congr; auto.
apply IHx.
destruct u; simpl; auto.
Qed.

Definition shift X (x : term X) : term (option X) :=
  x //- @Some X.

Lemma shift_fct : forall X Y (f : X -> Y) (x : term X),
  shift (x //- f) = x //- fun a => Some (f a).
Proof.
unfold shift. intros. rewrite fct_fct. reflexivity.
Qed.

Lemma fct_shift : forall X Y (f : option X -> Y) (x : term X),
  shift x //- f = x //- fun a => f (Some a).
Proof.
unfold shift. intros. rewrite fct_fct. reflexivity.
Qed.

Hint Rewrite -> shift_fct fct_shift : slc.

Definition comm
  (X Y : Set) (f : X -> term Y) (x : option X) : term (option Y) :=
  match x with
  | Some a => shift (f a)
  | None => var None
  end.

Remark comm_var : forall X, comm (@var X) = @var (option X).
Proof.
intros; extens.
destruct x; reflexivity.
Qed.

Fixpoint subst (X Y : Set) (f : X -> term Y)
  (x : term X) { struct x } : term Y :=
  match x with
  | var x => f x
  | app x y => app (x //= f) (y //= f)
  | abs x => abs (x //= comm f)
  end
where "x //= f" := (@subst _ _ f x) : lc_scope.

Ltac slc :=
  intros;
  repeat first [ progress simpl fct
               | progress simpl subst
               | progress autorewrite with slc ];
  auto with slc.

Lemma subst_var : forall (X Y : Set) (f : X -> term Y) (x : X),
  var x //=  f = f x.
Proof.
reflexivity.
Qed.

Lemma var_subst : forall X (x : term X),
  x //= @var X = x.
Proof.
induction x; simpl; auto.
rewrite comm_var.
auto.
Qed.

Lemma var_subst_match : forall X (x : term X) (f : X -> term X),
  (forall u, f u = var u) -> x //= f = x.
Proof.
intros; transitivity (x //= @var _).
congr; extens.
trivial.
apply var_subst.
Qed.

Hint Resolve var_subst_match : slc.

Lemma fct_subst : forall (X Y Z : Set)
  (f : X -> term Y) (g : Y -> Z) (x : term X),
  x //= f //- g = x //= fun u => f u //- g.
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; congr; auto.
rewrite IHx.
congr; clear x IHx.
extens x; destruct x; slc.
Qed.
Hint Rewrite -> fct_subst : slc.

Lemma subst_fct : forall (X Y Z : Set)
  (f : X -> Y) (g : Y -> term Z) (x : term X),
  x //- f //= g = x //= fun u => g (f u).
Proof.
intros; generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; congr; auto.
rewrite IHx.
congr; clear x IHx.
extens x; destruct x; reflexivity.
Qed.
Hint Rewrite -> subst_fct : slc.

Lemma shift_subst : forall (X Y : Set) (f : X -> term Y) (x : term X),
  shift (x //= f) = x //= fun a => shift (f a).
Proof.
unfold shift.
intros.
rewrite fct_subst.
reflexivity.
Qed.

Lemma subst_shift : forall (X Y : Set)
  (f : option X -> term Y) (x : term X),
  shift x //= f = x //= fun a => f (Some a).
Proof.
unfold shift.
intros.
rewrite subst_fct.
reflexivity.
Qed.

Hint Rewrite -> shift_subst subst_shift : slc.

Lemma subst_subst : forall (X Y Z : Set)
  (f : X -> term Y) (g : Y -> term Z) (x : term X),
  x //= f //= g = x //= fun u => f u //= g.
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; congr; auto.
rewrite IHx.
congr; clear x IHx.
extens x; destruct x; slc.
Qed.
Hint Rewrite -> subst_subst : slc.

Lemma fct_as_subst : forall (X Y : Set) (f : X -> Y) (x : term X),
  x //- f = x //= (fun a => var (f a)).
Proof.
intros. generalize Y f; clear Y f.
induction x; simpl; intros; auto.
rewrite IHx; clear IHx.
congr. congr; clear x.
extens x; destruct x; reflexivity.
Qed.

Definition app1 X (x : term X) : term (option X) :=
  app (shift x) (var None).

Lemma app1_app : forall X (x : term X),
  app1 x = app (shift x) (var None).
Proof.
reflexivity.
Qed.

Opaque app1.

Lemma fct_app1 : forall (X Y : Set) (f : X -> Y) (x : term X),
  app1 x //- (optmap f) = app1 (x //- f).
Proof.
intros.
do 2 rewrite app1_app.
simpl. slc.
Qed.
Hint Rewrite -> fct_app1 : slc.

Lemma app_as_app1 : forall X (x y : term X),
  app x y = app1 x //= default (@var _) y.
Proof.
intros. rewrite app1_app. slc.
symmetry. slc.
Qed.

Lemma subst_app1 : forall X Y (f : option X -> term Y) (x : term X),
  app1 x //= f = app (x //= fun u : X => f (Some u)) (f None).
Proof.
intros. rewrite app1_app. simpl. slc.
Qed.

Hint Rewrite -> subst_app1 : slc.

Inductive Beta (X : Set) : term X -> term X -> Prop :=
  | beta_intro : forall (x1 : term (option X)) (x2 : term X),
      Beta (app (abs x1) x2) (x1 //= (default (fun a => var a) x2)).

Lemma beta_intro2 : forall (X : Set)
  (x1 : term (option X)) (x2 y : term X),
  x1 //= (default (fun a => var a) x2) = y ->
    Beta (app (abs x1) x2) y.
Proof.
intros. subst y. apply beta_intro.
Qed.

Lemma app_abs1 : forall X (x : term (option X)),
  Beta (app1 (abs x)) x.
Proof.
intros. rewrite app1_app. unfold shift. slc.
apply beta_intro2.
slc.
apply var_subst_match.
destruct u; simpl; reflexivity.
Qed.

Inductive lcr (X : Set) : term X -> term X -> Prop :=
  | lcr_var : forall a : X, var a == var a
  | lcr_app : forall x1 x2 y1 y2 : term X,
      x1 == x2 -> y1 == y2 -> app x1 y1 == app x2 y2
  | lcr_abs : forall x y : term (option X),
      x == y -> abs x == abs y
  | lcr_beta : forall x y : term X, Beta x y -> x == y
  | lcr_eta : forall x : term X, abs (app1 x) == x
  | lcr_sym : forall x y : term X, y == x -> x == y
  | lcr_trs : forall x y z : term X,
      lcr x y -> lcr y z -> lcr x z
where "x == y" := (@lcr _ x y).

Hint Resolve lcr_var lcr_app lcr_abs lcr_eta lcr_beta lcr_trs : slc.
Hint Immediate lcr_sym : slc.

Lemma lcr_rfl : forall X (x : term X), x == x.
Proof.
intros.
apply lcr_trs with (abs (app1 x)).
apply lcr_sym.
apply lcr_eta; reflexivity.
apply lcr_eta; reflexivity.
Qed.
Hint Resolve lcr_rfl : slc.

Lemma lcr_eq : forall X (x y : term X), x = y -> x == y.
Proof.
intros; subst y; slc.
Qed.
Hint Resolve lcr_eq : slc.

Lemma eta_fct : forall (X Y : Set) (f : X -> Y) (x : term X),
  abs (app1 x) //- f = abs (app1 (x //- f)).
Proof.
induction x; simpl; slc.
Qed.

Lemma fct_abs : forall (X Y : Set)
  (f : X -> Y) (x : term (option X)),
  abs x //- f = abs (x //- optmap f).
Proof.
reflexivity.
Qed.

Lemma lcr_fct : forall (X Y : Set) (f : X -> Y) (x y : term X),
  x == y -> x //- f == y //- f.
Proof.
intros.
generalize Y f.
clear Y f.
induction H; intros; try solve [simpl; slc].
2: eauto with slc.
destruct H.
simpl. slc.
apply lcr_beta. apply beta_intro2.
slc. congr.
extens. destruct x; reflexivity.
Qed.

Hint Resolve lcr_fct : slc.

Lemma eta_subst : forall (X Y : Set)
  (f : X -> term Y) (x : term X),
  abs (app1 x) //= f = abs (app1 (x //= f)).
Proof.
intros. simpl. slc.
rewrite app1_app. slc.
Qed.

Lemma lcr_subst_arg : forall (X Y : Set)
  (f : X -> term Y) (x y : term X),
  x == y -> x //= f == y //= f.
Proof.
intros. generalize Y f; clear Y f.
induction H; intros; try solve [simpl; slc].
3: eauto with slc.
2: rewrite eta_subst; slc.
destruct H.
simpl.
rewrite subst_subst.
apply lcr_beta.
apply beta_intro2.
rewrite subst_subst.
congr.
clear x1.
extens x; destruct x; simpl; slc.
Qed.

Lemma lcr_subst_fun : forall (X Y : Set)
  (f g : X -> term Y) (x : term X),
  (forall u, f u == g u) ->
  x //= f == x //= g.
Proof.
intros. generalize Y f g H; clear Y f g H.
induction x; intros; simpl; slc.
apply lcr_abs.
apply IHx.
destruct u; simpl; unfold shift; slc.
Qed.

Lemma lcr_subst : forall (X Y : Set)
  (f g : X -> term Y) (x y : term X),
  (forall u, f u == g u) -> x == y ->
  x //= f == y //= g.
Proof.
intros.
apply lcr_trs with (x //= g).
apply lcr_subst_fun; assumption.
apply lcr_subst_arg; assumption.
Qed.

Lemma lcr_app1 : forall X (x y : term X),
  x == y -> app1 x == app1 y.
Proof.
intros. do 2 rewrite app1_app. unfold shift. slc.
Qed.
