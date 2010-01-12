Require Import String.
Require Import FMapWeakList.
Require Import FMapInterface.
Require Import FMapFacts.
Require Import Dec.

Module Table := FMapWeakList.Make StrDec.
Module TableWF := FMapFacts.WFacts_fun StrDec Table.
Module TableProp := WProperties_fun StrDec Table.

Definition table t := Table.t t.
Definition empty t := Table.empty t.

Axiom Extensionality_Table : forall (t : Type) (A B : table t),
   Table.Equal A B -> A = B.

Lemma equal_ind : forall (t : Type) A B,
 (forall k (e : t), Table.MapsTo k e A -> Table.MapsTo k e B) ->
 (forall k (e : t), Table.MapsTo k e B -> Table.MapsTo k e A) ->
 A = B.
Proof.
intros.
apply Extensionality_Table.
apply (TableWF.Equal_mapsto_iff A B).
split; [ apply H | apply H0 ].
Qed.

Lemma add_1 : forall (t : Type) (A : table t) x r1 r2,
  Table.add x r1 (Table.add x r2 A) = Table.add x r1 A.
Proof.
intros.
apply equal_ind; intros; apply TableWF.add_mapsto_iff in H;
 decompose [or and] H.
 rewrite H1,  H2 in |- *.
 apply Table.add_1.
 reflexivity.

 apply Table.add_2; auto.
 apply Table.add_3 in H2; tauto.

 rewrite H1,  H2 in |- *.
 apply Table.add_1.
 reflexivity.

 apply Table.add_2; auto.
 apply Table.add_2; tauto.
Qed.

Lemma add_2 : forall (t : Type) (A : table t) x y r1 r2,
  x <> y -> Table.add x r1 (Table.add y r2 A) = Table.add y r2 (Table.add x r1 A).
Proof.
intros.
apply equal_ind; intros; apply TableWF.add_mapsto_iff in H0.
 decompose [and or] H0.
  rewrite H2,  H3 in |- *.
  apply Table.add_2.
   apply sym_not_eq.
   rewrite <- H2 in |- *.
   tauto.

   apply Table.add_1.
   reflexivity.

  apply TableWF.add_mapsto_iff in H3.
  decompose [and or] H3.
   rewrite H4,  H5 in |- *.
   apply Table.add_1.
   reflexivity.

   apply Table.add_2; auto.
   apply Table.add_2; tauto.

 decompose [and or] H0.
  rewrite <- H2,  <- H3 in |- *.
  apply Table.add_2; auto.
  apply Table.add_1.
  reflexivity.

  apply TableWF.add_mapsto_iff in H3.
  decompose [and or] H3.
   rewrite H4,  H5 in |- *.
   apply Table.add_1.
   reflexivity.

   apply Table.add_2; auto.
   apply Table.add_2; tauto.
Qed.

Lemma map_add : forall (A : Type) (f : A -> A) x T table,
  Table.map f (Table.add x T table) = Table.add x (f T) (Table.map f table).
Proof.
intros.
apply equal_ind; intros.
 apply TableWF.map_mapsto_iff in H.
 decompose [ex and] H.
 apply TableWF.add_mapsto_iff in H2.
 decompose [and or] H2.
  rewrite H1, H3, H4 in |- *.
  apply Table.add_1.
  reflexivity.

  apply Table.add_2; auto.
  apply <- TableWF.map_mapsto_iff.
  exists x0.
  split; tauto.

 apply TableWF.add_mapsto_iff in H.
 apply <- TableWF.map_mapsto_iff.
 decompose [and or] H.
  exists T.
  split.
   rewrite H2 in |- *.
   reflexivity.

   apply Table.add_1.
   tauto.

  apply TableWF.map_mapsto_iff in H2.
  decompose [ex and] H2.
  exists x0.
  split.
   tauto.

   apply Table.add_2; tauto.
Qed.

Lemma MapsTo_In : forall (t : Type)  A x (T : table t),
  Table.MapsTo x T A -> Table.In x A.
Proof.
intros.
unfold Table.In in |- *.
unfold Table.Raw.PX.In in |- *.
unfold Table.MapsTo in H.
exists T.
tauto.
Qed.
