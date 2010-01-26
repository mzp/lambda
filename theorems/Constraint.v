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
Infix "∪" := TConst.union (at level 50) : const_scope.
Close Scope  const_scope.

Definition FreeC x c := exists S, exists T,
  TConst.In (S,T) c /\ (FreeT x S \/ FreeT x T).

Definition Unified (c : tconst) (t : tsubst) := forall S T,
  TConst.In (S,T) c -> type_subst S t = type_subst T t.

Lemma unified_union_iff : forall C1 C2 tsubst,
  (Unified C1 tsubst /\ Unified C2 tsubst) <->
  Unified (C1 ∪ C2) tsubst.
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

Lemma unified_add_iff : forall S T C tsubst,
  Unified (TConst.add (S,T) C) tsubst <-> (type_subst S tsubst = type_subst T tsubst /\ Unified C tsubst).
Proof.
intros.
rewrite TConst.add_union.
split; intros.
 apply unified_union_iff in H.
 decompose [and] H.
 split; auto.
 apply H0.
 apply <- TConst.WFact.singleton_iff.
 tauto.

 decompose [and] H.
 apply (unified_union_iff (TConst.FSet.singleton (S,T)) C _).
 split; auto.
 unfold Unified.
 intros.
 apply TConst.WFact.singleton_iff in H2.
 simpl in H2.
 decompose [and] H2.
 rewrite <- H3, <- H4.
 assumption.
Qed.

Lemma unified_empty : forall tsubst,
  Unified TConst.empty tsubst.
Proof.
unfold Unified in |- *.
intros.
inversion H.
Qed.

Hint Immediate unified_empty.
