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

Lemma Free_Lambda_inv: forall x y T t,
  x <> y -> ~ Free x (Lambda y T t) -> ~Free x t.
Proof.
intros; intro.
apply H0.
apply FLambda; tauto.
Qed.

Lemma Bound_Lambda_inv: forall x y T t,
  ~ Bound x (Lambda y T t) -> ~Bound x t.
Proof.
intros; intro.
apply H.
apply BLambda2.
tauto.
Qed.

Lemma Free_Apply_inv_1: forall x t1 t2,
  ~ Free x (Apply t1 t2) -> ~Free x t1.
Proof.
intros; intro.
apply H.
apply FApply.
tauto.
Qed.

Lemma Free_Apply_inv_2: forall x t1 t2,
  ~ Free x (Apply t1 t2) -> ~Free x t2.
Proof.
intros; intro.
apply H.
apply FApply.
tauto.
Qed.

Lemma Bound_Apply_inv_1: forall x t1 t2,
  ~ Bound x (Apply t1 t2) -> ~Bound x t1.
Proof.
intros; intro.
apply H.
apply BApply.
tauto.
Qed.

Lemma Bound_Apply_inv_2: forall x t1 t2,
  ~ Bound x (Apply t1 t2) -> ~Bound x t2.
Proof.
intros; intro.
apply H.
apply BApply.
tauto.
Qed.

Lemma Free_If_inv_1: forall x t1 t2 t3,
  ~ Free x (If t1 t2 t3) -> ~Free x t1.
Proof.
intros; intro.
apply H.
apply FIf.
tauto.
Qed.

Lemma Free_If_inv_2: forall x t1 t2 t3,
  ~ Free x (If t1 t2 t3) -> ~Free x t2.
Proof.
intros; intro.
apply H.
apply FIf.
tauto.
Qed.

Lemma Free_If_inv_3: forall x t1 t2 t3,
  ~ Free x (If t1 t2 t3) -> ~Free x t3.
Proof.
intros; intro.
apply H.
apply FIf.
tauto.
Qed.

Lemma Bound_If_inv_1: forall x t1 t2 t3,
  ~ Bound x (If t1 t2 t3) -> ~Bound x t1.
Proof.
intros; intro.
apply H.
apply BIf.
tauto.
Qed.

Lemma Bound_If_inv_2: forall x t1 t2 t3,
  ~ Bound x (If t1 t2 t3) -> ~Bound x t2.
Proof.
intros; intro.
apply H.
apply BIf.
tauto.
Qed.

Lemma Bound_If_inv_3: forall x t1 t2 t3,
  ~ Bound x (If t1 t2 t3) -> ~Bound x t3.
Proof.
intros; intro.
apply H.
apply BIf.
tauto.
Qed.
