Require Import Ensembles.
Require Import String.

Definition set A := Ensemble A.
Definition In    {A : Type} x xs     := Ensembles.In    A xs x.
Definition Union {A : Type} xs ys    := Ensembles.Union A xs ys.
Definition Add   {A : Type} x xs     := Ensembles.Add   A xs x.
Definition Disjoint {A : Type} xs ys := Ensembles.Disjoint A xs ys.

Lemma disjoint_union : forall A (X Y Z: set A),
  Disjoint (Union X Z) Y -> Disjoint X Y.
Proof.
intros.
inversion H.
apply Disjoint_intro.
intro.
specialize (H0 x).
intro.
apply H0.
inversion H1.
apply Intersection_intro.
 apply Union_introl.
 trivial.

 trivial.
Qed.

Lemma disjoint_add : forall A (X Y : set A) x,
  Disjoint (Add x X) Y -> Disjoint X Y.
Proof.
intros.
apply disjoint_union with (Z := Singleton A x).
trivial.
Qed.

Lemma disjoint_sym : forall A (X Y : set A),
  Disjoint X Y -> Disjoint Y X.
Proof.
intros.
inversion H.
apply Disjoint_intro.
intros.
specialize (H0 x).
intro.
apply H0.
inversion H1.
apply Intersection_intro; trivial.
Qed.


Lemma union_sym : forall A (X Y : set A),
  Union X Y = Union Y X.
Proof.
intros.
apply Extensionality_Ensembles.
unfold Same_set in |- *.
unfold Included in |- *.
split; intros.
 inversion H.
  apply Union_intror.
  trivial.

  apply Union_introl.
  trivial.

 inversion H.
  apply Union_intror.
  trivial.

  apply Union_introl.
  trivial.
Qed.

