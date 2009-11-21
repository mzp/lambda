Require Import List.
Require Import String.

Require Import Term.

Lemma FV_Lambda: forall x y T t,
  x <> y -> ~ FV x (Lambda y T t) -> ~FV x t.
Proof.
intros; intro.
apply H0.
apply FVLambda.
exact H.
exact H1.
Qed.

Lemma BV_Lambda: forall x y T t,
  ~ BV x (Lambda y T t) -> ~BV x t.
Proof.
intros; intro.
apply H.
apply BVLambda2.
exact H0.
Qed.


Lemma FV_Apply_1: forall x t1 t2,
  ~ FV x (Apply t1 t2) -> ~FV x t1.
Proof.
intros; intro.
apply H.
apply FVApply.
left; exact H0.
Qed.

Lemma FV_Apply_2: forall x t1 t2,
  ~ FV x (Apply t1 t2) -> ~FV x t2.
Proof.
intros; intro.
apply H.
apply FVApply.
right; exact H0.
Qed.

Lemma BV_Apply_1: forall x t1 t2,
  ~ BV x (Apply t1 t2) -> ~BV x t1.
Proof.
intros; intro.
apply H.
apply BVApply.
left; exact H0.
Qed.

Lemma BV_Apply_2: forall x t1 t2,
  ~ BV x (Apply t1 t2) -> ~BV x t2.
Proof.
intros; intro.
apply H.
apply BVApply.
right; exact H0.
Qed.


Lemma FV_If_1: forall x t1 t2 t3,
  ~ FV x (If t1 t2 t3) -> ~FV x t1.
Proof.
intros; intro.
apply H.
apply FVIf.
left; exact H0.
Qed.

Lemma FV_If_2: forall x t1 t2 t3,
  ~ FV x (If t1 t2 t3) -> ~FV x t2.
Proof.
intros; intro.
apply H.
apply FVIf.
right; left; exact H0.
Qed.

Lemma FV_If_3: forall x t1 t2 t3,
  ~ FV x (If t1 t2 t3) -> ~FV x t3.
Proof.
intros; intro.
apply H.
apply FVIf.
right; right; exact H0.
Qed.

Lemma BV_If_1: forall x t1 t2 t3,
  ~ BV x (If t1 t2 t3) -> ~BV x t1.
Proof.
intros; intro.
apply H.
apply BVIf.
left; exact H0.
Qed.

Lemma BV_If_2: forall x t1 t2 t3,
  ~ BV x (If t1 t2 t3) -> ~BV x t2.
Proof.
intros; intro.
apply H.
apply BVIf.
right; left; exact H0.
Qed.

Lemma BV_If_3: forall x t1 t2 t3,
  ~ BV x (If t1 t2 t3) -> ~BV x t3.
Proof.
intros; intro.
apply H.
apply BVIf.
right; right; exact H0.
Qed.

