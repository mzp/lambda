Require Import String.
Require Import Util.
Require Import DecidableType.
Require Import FSetWeakList.
Require Import FSetFacts.
Require Import FSetProperties.

Module Make(Dec : DecidableType).
  Module FSet  := FSetWeakList.Make Dec.
  Module WFact := FSetFacts.WFacts_fun Dec FSet.
  Module WProp := FSetProperties.WProperties_fun Dec FSet.

  Axiom Extensionality_Set : forall A B,
    FSet.Equal A B -> A = B.

  Definition t := FSet.t.
  Definition empty := FSet.empty.
  Definition In x xs := FSet.In x xs.
  Definition union xs ys := FSet.union xs ys.
  Definition add   x xs     := FSet.add x xs.
  Definition Disjoint xs ys := forall x, ~ FSet.In x (FSet.inter xs ys).

  Lemma equal_ind : forall X Y,
    (forall x, FSet.In x X -> FSet.In x Y) ->
    (forall x, FSet.In x Y -> FSet.In x X) ->
    X = Y.
  Proof.
  intros.
  apply Extensionality_Set.
  unfold FSet.Equal in |- *.
  split; intros; auto.
  Qed.

  Lemma add_union : forall x X,
    add x X = union (FSet.singleton x) X.
  Proof.
  intros.
  apply equal_ind; intros.
   apply <-  WFact.union_iff.
   apply WFact.add_iff in H.
   decompose [or] H.
    left.
    apply <-  WFact.singleton_iff.
    assumption.

    tauto.

   apply WFact.union_iff in H.
   apply <-  WFact.add_iff.
   decompose [or] H.
    left.
    apply WFact.singleton_iff in H0.
    assumption.

    tauto.
  Qed.

  Lemma union_assoc : forall X Y Z,
    union X (union Y Z) = (union (union X Y) Z).
  Proof.
  intros.
  apply equal_ind; intros.
   apply WFact.union_iff in H.
   apply <- WFact.union_iff.
   decompose [or] H.
    left.
    apply <- WFact.union_iff.
    tauto.

    apply WFact.union_iff in H0.
    decompose [or] H0.
     left.
     apply <- WFact.union_iff.
     tauto.

     tauto.

   apply <- WFact.union_iff.
   apply WFact.union_iff in H.
   decompose [or] H.
    apply WFact.union_iff in H0.
    decompose [or] H0.
     tauto.

     right.
     apply <- WFact.union_iff.
     tauto.

    right.
    apply <- WFact.union_iff.
    tauto.
  Qed.

  Lemma union_sym : forall X Y,
    union X Y = union Y X.
  Proof.
  intros.
  apply equal_ind; intros.
   apply <- WFact.union_iff.
   apply WFact.union_iff in H.
   decompose [or] H; tauto.

   apply <- WFact.union_iff.
   apply WFact.union_iff in H.
   decompose [or] H; tauto.
  Qed.

  Lemma disjoint_sym : forall X Y,
    Disjoint X Y -> Disjoint Y X.
  Proof.
  unfold Disjoint in |- *.
  intros.
  specialize (H x).
  Contrapositive H.
  apply <- WFact.inter_iff.
  apply WFact.inter_iff in H0.
  decompose [and] H0.
  tauto.
  Qed.

  Lemma disjoint_union_iff: forall X Y Z,
    Disjoint (union X Y) Z <-> Disjoint X Z /\ Disjoint Y Z.
  Proof.
  unfold Disjoint in |- *.
  split; intros.
   split; intros; specialize (H x).
    Contrapositive H.
    apply <-  WFact.inter_iff.
    apply WFact.inter_iff in H0.
    decompose [and] H0.
    split; auto.
    apply <-  WFact.union_iff.
    tauto.

    Contrapositive H.
    apply WFact.inter_iff in H0.
    decompose [and] H0.
    apply <-  WFact.inter_iff.
    split; auto.
    apply <-  WFact.union_iff.
    tauto.

   decompose [and] H.
   specialize (H0 x).
   specialize (H1 x).
   intro.
   apply WFact.inter_iff in H2.
   decompose [and] H2.
   apply WFact.union_iff in H3.
   decompose [or] H3.
    apply H0.
    apply <-  WFact.inter_iff.
    tauto.

    apply H1.
    apply <-  WFact.inter_iff.
    tauto.
  Qed.

  Lemma disjoint_add_iff : forall X Y x,
    Disjoint (add x X) Y <-> ~In x Y /\ Disjoint X Y.
  Proof.
  intros.
  rewrite add_union in |- *.
  split; intros.
   apply disjoint_union_iff in H.
   decompose [and] H.
   split; auto.
   unfold Disjoint in H0.
   specialize (H0 x).
   Contrapositive H0.
   apply <- WFact.inter_iff.
   split; auto.
   apply <- WFact.singleton_iff.
   reflexivity.

   apply <- disjoint_union_iff.
   decompose [and] H.
   split; auto.
   unfold Disjoint.
   intros.
   Contrapositive H0.
   apply WFact.inter_iff in H2.
   decompose [and] H2.
   apply WFact.singleton_iff in H3.
   rewrite H3.
   tauto.
  Qed.

  Lemma disjoint_iff : forall X Y,
    Disjoint X Y <-> (forall x, In x X -> ~ In x Y) /\ (forall x, In x Y -> ~ In x X).
  Proof.
  unfold Disjoint in |- *.
  split; intros.
  split; intros; specialize (H x);
   Contrapositive H;
   apply <- WFact.inter_iff;
   tauto.

  decompose [and] H.
  specialize (H0 x).
  specialize (H1 x).
  intro.
  apply WFact.inter_iff in H2.
  decompose [and] H2.
  apply H0 in H3.
  contradiction.
  Qed.
End Make.
