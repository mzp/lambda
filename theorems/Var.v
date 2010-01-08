Require Import String.
Require Import Term.

Inductive Free : string -> term -> Prop :=
  | FVar    : forall s, Free s (Var s)
  | FLambda : forall x y t T, x <> y -> Free x t -> Free x (Lambda y T t)
  | FApply  : forall x t1 t2, Free x t1 \/ Free x t2 -> Free x (Apply t1 t2)
  | FIf     : forall x t1 t2 t3, Free x t1 \/ Free x t2 \/ Free x t3 -> Free x (If t1 t2 t3).

Inductive Bound : string -> term -> Prop :=
  | BLambda1 : forall x T t, Bound x (Lambda x T t)
  | BLambda2 : forall x y T t, Bound x t -> Bound x (Lambda y T t)
  | BApply   : forall x t1 t2, Bound x t1 \/ Bound x t2 -> Bound x (Apply t1 t2)
  | BIf      : forall x t1 t2 t3, Bound x t1 \/ Bound x t2 \/ Bound x t3 -> Bound x (If t1 t2 t3).

Lemma not_free_lambda: forall x y T t,
  x <> y -> ~ Free x (Lambda y T t) -> ~Free x t.
Proof.
intros; intro.
apply H0.
apply FLambda; tauto.
Qed.

Lemma not_bound_lambda: forall x y T t,
  ~ Bound x (Lambda y T t) -> ~Bound x t.
Proof.
intros; intro.
apply H.
apply BLambda2.
tauto.
Qed.

Lemma not_free_apply: forall x t1 t2,
  ~ Free x (Apply t1 t2) -> ~ Free x t1 /\ ~ Free x t2.
Proof.
intros.
split;
 intro;
 apply H;
 apply FApply;
 tauto.
Qed.

Lemma not_bound_apply: forall x t1 t2,
  ~ Bound x (Apply t1 t2) -> ~ Bound x t1 /\ ~ Bound x t2.
Proof.
intros.
split;
 intro;
 apply H;
 apply BApply;
 tauto.
Qed.

Lemma not_free_if: forall x t1 t2 t3,
  ~ Free x (If t1 t2 t3) -> ~ Free x t1 /\ ~ Free x t2 /\ ~ Free x t3.
Proof.
intros.
split; [ | split ];
 intro;
 apply H;
 apply FIf;
 tauto.
Qed.

Lemma not_bound_if: forall x t1 t2 t3,
  ~ Bound x (If t1 t2 t3) -> ~ Bound x t1 /\ ~ Bound x t2 /\ ~ Bound x t3.
Proof.
intros.
split; [ | split ];
 intro;
 apply H;
 apply BIf;
 tauto.
Qed.

