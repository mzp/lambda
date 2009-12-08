Require Import Ensembles.
Require Import String.
Require Import DecidableType.
Require Import FSetWeakList.
Require Import FSetFacts.

Module Make(Dec : DecidableType).
  Module FSet  := FSetWeakList.Make Dec.
  Module WFact := FSetFacts.WFacts_fun Dec FSet.

  Axiom Extensionality_Set : forall A B,
    FSet.Equal A B -> A = B.

  Definition t := FSet.t.
  Definition empty := FSet.empty.
  Definition In x xs := FSet.In x xs.
  Definition union xs ys := FSet.union xs ys.
  Definition add   x xs     := FSet.add x xs.
  Definition Disjoint xs ys := forall x, ~ FSet.In x (FSet.inter xs ys).

  Lemma disjoint_union : forall X Y Z,
    Disjoint (union X Z) Y -> Disjoint X Y.
  Proof.
  unfold Disjoint in |- *.
  intros.
  specialize (H x).
  intro.
  apply H.
  apply (WFact.inter_iff (union X Z) Y x).
  apply (WFact.inter_iff X Y x) in H0.
  inversion H0.
  split.
   apply (WFact.union_iff X Z x).
   left; trivial.

   trivial.
  Qed.

  Lemma disjoint_add : forall X Y x,
    Disjoint (add x X) Y -> Disjoint X Y.
  Proof.
  unfold Disjoint in |- *.
  intros.
  specialize (H x0).
  intro.
  apply H.
  apply (WFact.inter_iff (add x X) Y _).
  apply (WFact.inter_iff X Y) in H0.
  inversion H0.
  split.
   apply (WFact.add_iff X x x0).
   right; trivial.

   trivial.
  Qed.

  Lemma disjoint_sym : forall X Y,
    Disjoint X Y -> Disjoint Y X.
  Proof.
  unfold Disjoint in |- *.
  intros.
  intro.
  specialize (H x).
  apply H.
  apply (WFact.inter_iff X Y x).
  apply (WFact.inter_iff Y X x) in H0.
  inversion H0.
  split; trivial.
  Qed.

  Lemma union_sym : forall X Y,
    union X Y = union Y X.
  Proof.
  intros.
  apply Extensionality_Set.
  unfold FSet.Equal in |- *.
  split.
   intro.
   apply (WFact.union_iff Y X a).
   apply (WFact.union_iff X Y a) in H.
   inversion H.
    right; trivial.

    left; trivial.

   intros.
   apply (WFact.union_iff X Y a).
   apply (WFact.union_iff Y X a) in H.
   inversion H.
    right; trivial.

    left; trivial.
  Qed.
End Make.
