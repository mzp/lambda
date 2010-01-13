Require Import List.
Require Import Ensembles.
Require Import String.

Require Import Tables.
Require Import Sets.
Require Import Dec.
Require Import Term.
Require Import TVar.
Require Import TypeSubst.

Module TypePairDec := PairDec TypeDec TypeDec.
Module TConst := Sets.Make TypePairDec.
Definition tconst := TConst.t.

Delimit Scope const_scope with tconst.
Bind Scope const_scope with tconst.
Open Scope const_scope.
Infix "|_|" := TConst.union (at level 50) : const_scope.
Close Scope  const_scope.

Definition FreeC x c := forall S T,
  TConst.In (S,T) c -> FreeT x S \/ FreeT x T.

Definition Unified (c : tconst) (t : tsubst) := forall S T,
  TConst.In (S,T) c -> type_subst S t = type_subst T t.

Lemma unified_union_iff : forall C1 C2 tsubst,
  (Unified C1 tsubst /\ Unified C2 tsubst) <->
  Unified (C1 |_| C2) tsubst.
Proof.
unfold Unified in |- *.
split; intros.
 decompose [and] H.
 apply TConst.WFact.union_iff in H0.
 decompose [or] H0;
  [ apply H1 in H3 | apply H2 in H3 ];
    tauto.

 split; intros;
  apply H;
  apply <- TConst.WFact.union_iff;
  tauto.
Qed.

Lemma unified_empty : forall tsubst,
  Unified TConst.empty tsubst.
Proof.
unfold Unified in |- *.
intros.
inversion H.
Qed.

Hint Immediate unified_empty.

Lemma Unified_Union_intro : forall C1 C2 tsubst,
  Unified C1 tsubst ->
  Unified C2 tsubst ->
  Unified (TConst.union C1 C2) tsubst.
Proof.
unfold Unified in |- *.
intros.
apply (TConst.WFact.union_iff C1 C2 _) in H1.
decompose [or] H1; [ apply H in H2 | apply H0 in H2 ]; trivial.
Qed.

Lemma Unified_Union : forall C1 C2 tsubst,
  Unified (TConst.union C1 C2) tsubst -> Unified C1 tsubst.
Proof.
unfold Unified in |- *.
intros.
apply H.
apply (TConst.WFact.union_iff C1 C2 _).
left; trivial.
Qed.

Lemma Unified_empty : forall tsubst,
  Unified TConst.empty tsubst.
Proof.
unfold Unified in |- *.
intros.
inversion H.
Qed.

Lemma Unified_Add_intro : forall c C tsubst,
  Unified C tsubst ->
  Unified (TConst.FSet.singleton c) tsubst ->
  Unified (TConst.add c C) tsubst.
Proof.
unfold Unified in |- *.
intros.
apply (TConst.WFact.add_iff C c _) in H1.
decompose [or] H1.
 destruct c.
 apply TConst.WFact.singleton_iff in H2.
 apply H0 in H2.
 trivial.

 apply H in H2.
 trivial.
Qed.

Lemma Unified_Add : forall c C tsubst,
  Unified (TConst.add c C) tsubst -> Unified C tsubst.
Proof.
unfold Unified in |- *.
intros.
apply H.
apply (TConst.WFact.add_iff C c _).
right; trivial.
Qed.

