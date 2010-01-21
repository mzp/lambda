Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TVar.
Require Import TVars.
Require Import TypeSubst.

Definition sub {A : Type} (tsubst : table A) X :=
  filter (fun x => not_sumbool (TVars.WProp.In_dec x X)) tsubst.

Infix "//" := sub (at level 50).

Definition Disjoint {A : Type} (tsubst : table A) tvars := forall x,
  (Table.In x tsubst -> ~ TVars.In x tvars) /\
  (TVars.In x tvars  -> ~ Table.In x tsubst).

Lemma union_disjoint_iff: forall A (m : table A) X Y,
  Disjoint m (TVars.union X Y) <-> Disjoint m X /\ Disjoint m Y.
Proof.
unfold Disjoint.
split; intros.
 split; intros; decompose [and] (H x); split; intros.

  apply H0 in H2.
  Contrapositive H2.
  apply <- TVars.WFact.union_iff.
  tauto.

  apply H1.
  apply <- TVars.WFact.union_iff.
  tauto.

  apply H0 in H2.
  Contrapositive H2.
  apply <- TVars.WFact.union_iff.
  tauto.

  apply H1.
  apply <- TVars.WFact.union_iff.
  tauto.

 decompose [and] H.
 decompose [and] (H0 x).
 decompose [and] (H1 x).
 split; intros.
  intro.
  apply TVars.WFact.union_iff in H7.
  decompose [or] H7;
   [ apply H2 in H6 | apply H4 in H6];
   contradiction.

  intro.
  apply TVars.WFact.union_iff in H6.
  decompose [or] H6;
   [apply H3 in H8 | apply H5 in H8 ];
   contradiction.
Qed.

Lemma add_disjoint_iff: forall A (m : table A) x X,
  Disjoint m (TVars.add x X) <-> ~ Table.In x m /\ Disjoint m X.
Proof.
intros.
rewrite TVars.add_union.
split; intros.
 apply union_disjoint_iff in H.
 decompose [and] H.
 split; auto.
 unfold Disjoint in H0.
 specialize (H0 x).
 decompose [and] H0.
 apply H3.
 apply <- TVars.WFact.singleton_iff.
 reflexivity.

 apply <- union_disjoint_iff.
 decompose [and] H.
 split; auto.
 unfold Disjoint in H1.
 unfold Disjoint.
 intros.
 split; intros.
 decompose [and] (H1 x0).
  intro.
  apply TVars.WFact.singleton_iff in H5.
  rewrite <- H5 in H2.
  contradiction.

  apply TVars.WFact.singleton_iff in H2.
  rewrite <- H2.
  assumption.
Qed.

Lemma sub_empty : forall A (tsubst : table A),
  tsubst = tsubst // TVars.empty.
Proof.
intros.
apply equal_ind; intros.
 apply <- filter_iff.
 split; auto.
 intro.
 inversion H0.

 unfold sub in H.
 apply filter_iff in H.
 tauto.
Qed.

Lemma sub_in : forall A x (tsubst : table A) X,
 Table.In x (tsubst // X) -> Table.In x tsubst.
Proof.
intros.
UnfoldIn H.
unfold sub in H0.
apply filter_iff in H0.
decompose [and] H0.
unfold Table.In, Table.Raw.PX.In.
exists x0.
assumption.
Qed.

Lemma sub_mapsto : forall A (tsubst : table A) x X U,
  ~ TVars.In x X ->
  (Table.MapsTo x U (tsubst // X) <-> Table.MapsTo x U tsubst).
Proof.
split; intros.
 unfold sub in H0.
 apply filter_iff in H0.
 decompose [and] H0.
 tauto.

 apply <- filter_iff.
 tauto.
Qed.

Lemma sub_find : forall A (tsubst : table A) x X ,
  ~ TVars.In x X ->
  (Table.find x (tsubst // X) = Table.find x tsubst).
Proof.
intros.
destruct (TableWF.In_dec tsubst x).
 UnfoldIn i.
 Dup H0.
 apply sub_mapsto in H1.
  apply H.

  apply TableWF.find_mapsto_iff in H0.
  apply TableWF.find_mapsto_iff in H1.
  rewrite H0,H1.
  reflexivity.

 assert ( ~ Table.In x (tsubst // X)).
  Contrapositive n.
  apply sub_in with (X:=X).
  assumption.

  apply TableWF.not_find_in_iff in n.
  apply TableWF.not_find_in_iff in H0.
  rewrite n,H0.
  reflexivity.
Qed.

Lemma sub_type_subst_var : forall (tsubst : tsubst) x X,
  ~ TVars.In x X ->
  type_subst (VarT x) (tsubst // X) =  type_subst (VarT x) tsubst.
Proof.
intros.
apply sub_find with (tsubst:=tsubst) in H.
simpl.
rewrite H.
reflexivity.
Qed.

Lemma fun_not_free : forall (X : TVars.t) T1 T2,
  (forall x, TVars.In x X -> ~ FreeT x (FunT T1 T2)) ->
  (forall x, TVars.In x X -> ~ FreeT x T1) /\
  (forall x, TVars.In x X -> ~ FreeT x T2).
Proof.
split; intros;
 apply H in H0;
 Contrapositive H0;
 apply FFunT;
 tauto.
Qed.

Lemma sub_type_subst : forall T X tsubst1,
  (forall x, TVars.In x X -> ~ FreeT x T) ->
  type_subst T tsubst1 = type_subst T (tsubst1 // X).
Proof.
induction T; intros; simpl in |- *; auto.
 destruct (TVars.WProp.In_dec s X).
  apply H in i.
  assert False; try contradiction.
  apply i.
  apply FVarT.

  apply sub_find with (tsubst:=tsubst1) in n.
  rewrite n in |- *.
  reflexivity.

 apply fun_not_free in H.
 decompose [and] H.
  apply (IHT1 _ tsubst1) in H0.
  apply (IHT2 _ tsubst1) in H1.
  rewrite H0,H1.
  reflexivity.
Qed.
