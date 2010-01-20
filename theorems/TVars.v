Require Import String.

Require Import Util.
Require Import Dec.
Require Import Sets.


Module TVars  := Sets.Make StrDec.
Definition tvars  := TVars.t.

Definition DisjointBy {A : Type} (Free : string -> A -> Prop) xs (T : A) :=
  (forall x, TVars.In x xs -> ~ Free x T) /\ (forall x, Free x T -> ~ TVars.In x xs).

Lemma in_not_eq: forall x y X,
 ~ TVars.In x X -> TVars.In y X -> x <> y.
Proof.
intros.
Contrapositive H.
rewrite H1.
assumption.
Qed.

Lemma eq_not_in: forall x y X,
  ~ TVars.In x X -> x = y -> ~ TVars.In y X.
Proof.
intros.
rewrite <- H0.
assumption.
Qed.

Lemma not_in_not_eq: forall x y X,
 TVars.In x X -> ~ TVars.In y X -> x <> y.
Proof.
intros.
Contrapositive H0.
rewrite <- H1.
assumption.
Qed.

Lemma eq_in: forall x y X,
 TVars.In x X -> x = y -> TVars.FSet.In y X.
Proof.
intros.
rewrite <- H0.
assumption.
Qed.

Hint Resolve in_not_eq eq_not_in not_in_not_eq eq_in: TVars.
