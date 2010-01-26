Require Import List.
Require Import String.
Require Import Sumbool.
Require Import Classical.

Require Import Util.
Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import TVar.
Require Import TVars.
Require Import TVarsFree.
Require Import Constraint.
Require Import ConstraintRule.
Require Import Solution.
Require Import CSolutionInv.
Require Import TSolutionInv.
Require Import TVarsSub.
Require Import TypeSubst.
Require Import TypeSubstMerge.

Lemma mapsto_var_type_subst: forall x tsubst1 tsubst2,
 (forall U, (Table.MapsTo x U tsubst1 <-> Table.MapsTo x U tsubst2)) ->
 type_subst (VarT x) tsubst1 = type_subst (VarT x) tsubst2.
Proof.
intros; simpl.
destruct (TableWF.In_dec tsubst1 x).
 UnfoldIn i.
 Dup H0.
 apply H in H0.
 apply TableWF.find_mapsto_iff in H0.
 apply TableWF.find_mapsto_iff in H1.
 rewrite H0,H1 in |- *.
 reflexivity.

 assert (~ Table.In (elt:=type) x tsubst2).
  Contrapositive n.
  UnfoldIn H0.
  unfold Table.In, Table.Raw.PX.In in |- *.
  exists x0.
  apply <- H.
  tauto.

  apply TableWF.not_find_mapsto_iff in n.
  apply TableWF.not_find_mapsto_iff in H0.
  rewrite n,H0 in |- *.
  reflexivity.
Qed.

Lemma free_mapsto_type_subst: forall T m1 m2,
  (forall k e, FreeT k T -> (Table.MapsTo k e m1 <-> Table.MapsTo k e m2)) ->
  type_subst T m1 = type_subst T m2.
Proof.
induction T; intros; auto.
 intros.
 apply mapsto_var_type_subst.
 intros.
 apply H.
 apply FVarT.

 simpl.
 rewrite IHT1 with (m2:=m2), IHT2 with (m2:=m2); intros.
  reflexivity.

  apply H.
  apply FFunT.
  tauto.

  apply H.
  apply FFunT.
  tauto.
Qed.

Lemma free_mapsto: forall A T (m' m1 m2 : table A) X1 X2 k e,
  (forall x, FreeT x T -> ~ TVars.In x X2 -> ~ TVars.In x X1) ->
  (forall k e, ~ TVars.In k X1  ->
    (Table.MapsTo k e m1 <-> Table.MapsTo k e m')) ->
  (forall k e, TVars.In k X2 ->
    (Table.MapsTo k e m2 <-> Table.MapsTo k e m')) ->
  m1 = m2 // X2 ->
  FreeT k T ->
  (Table.MapsTo k e m' <-> Table.MapsTo k e m2).
Proof.
intros.
destruct (TVars.WProp.In_dec k X2); intros.
 apply (H1 _ e) in i.
 apply iff_sym.
 assumption.

 split; intros.
  rewrite <- (sub_mapsto _ _ _ X2), <- H2; auto.
  apply H in H3; auto.
  apply (H0 _ e) in H3.
  apply H3.
  assumption.

  rewrite <- (sub_mapsto _ _ _ X2), <- H2 in H4; auto.
  apply H in H3; auto.
  apply (H0 _ e) in H3.
  apply H3.
  assumption.
Qed.

Lemma free_unified: forall m' m1 m2 X1 X2 C,
  (forall x, FreeC x C -> ~ TVars.In x X2 -> ~ TVars.In x X1) ->
  (forall k e, ~ TVars.In k X1  ->
    (Table.MapsTo k e m1 <-> Table.MapsTo k e m')) ->
  (forall k e,   TVars.In k X2 ->
    (Table.MapsTo k e m2 <-> Table.MapsTo k e m')) ->
  m1 = m2 // X2 ->
  Unified C m2 -> Unified C m'.
Proof.
unfold Unified.
intros.
assert (type_subst S m' = type_subst S m2).
 apply free_mapsto_type_subst.
 intros.
 apply (free_mapsto _ S _ m1 _ X1 X2); auto.
 intros.
 apply H; auto.
 unfold FreeC.
 exists S.
 exists T.
 tauto.

 assert (type_subst T m' = type_subst T m2).
  apply free_mapsto_type_subst.
  intros.
  apply (free_mapsto _ T _ m1 _ X1 X2); auto.
  intros.
  apply H; auto.
  unfold FreeC.
  exists S.
  exists T.
  tauto.

  rewrite H5, H6.
  apply H3.
  assumption.
Qed.

Definition ApplyMaps {A : Type} m' X X1 X2 (m m1 m2 : table A) x T :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U m <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U m1 <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U m2 <-> Table.MapsTo Y U m')) /\
  Table.MapsTo x T m'.

Lemma ex_ApplyMaps : forall A X X1 X2 (m m1 m2 : table A) x T ,
 TVars.Disjoint X1 X2 ->
 (forall y, TVars.FSet.In y X1 -> TVars.FSet.In y X) ->
 (forall y, TVars.FSet.In y X2 -> TVars.FSet.In y X) ->
 TVars.FSet.In x X -> ~ TVars.FSet.In x X1  -> ~ TVars.FSet.In x X2 ->
  exists s : table A, ApplyMaps s X X1 X2 m m1 m2 x T.
Proof.
intros.
rewrite TVars.disjoint_iff in H.
decompose [and] H.
exists
 (merge (fun y => not_sumbool $ TVars.WProp.In_dec y X) m $
  merge (fun y => TVars.WProp.In_dec y X1) m1 $
  merge (fun y => TVars.WProp.In_dec y X2) m2 $
  merge (fun y => string_dec x y) (Table.add x T (Table.empty A)) $
  Table.empty A).
unfold ApplyMaps, app in |- *.
split; [ idtac | split; [ idtac | split ] ]; intros; try (split; intro MH).
 apply <- merge_iff.
 tauto.

 apply merge_iff in MH.
 decompose [or and] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge in |- *; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge with (m1 := m1) (m2 := m2) in |- *; auto.
 rewrite disjoint_merge in |- *; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge with (m1 := m1) (m2 := m2) in MH; auto.
 rewrite disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge with (m1 := m2) (m2 := Table.add x T (Table.empty A))
  in |- *; eauto    with TVars.
 rewrite disjoint_merge with (m1 := m1) (m2 := Table.add x T (Table.empty A))
  in |- *; eauto    with TVars.
 rewrite disjoint_merge in |- *; eauto    with TVars.
 apply <- merge_iff.
 left.
 split; auto.
 apply <- TableWF.add_mapsto_iff.
 tauto.
Qed.

Definition IfMaps {A : Type} m' X X1 X2 X3 (m m1 m2 m3: table A) :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U m <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U m1 <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U m2 <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X3 ->
    (Table.MapsTo Y U m3 <-> Table.MapsTo Y U m')).

Lemma ex_IfMaps : forall A X X1 X2 X3 (m m1 m2 m3 : table A),
 (forall y, TVars.FSet.In y X1 -> TVars.FSet.In y X) ->
 (forall y, TVars.FSet.In y X2 -> TVars.FSet.In y X) ->
 (forall y, TVars.FSet.In y X3 -> TVars.FSet.In y X) ->
  Disjoint m X ->
  TVars.Disjoint X1 X2 ->
  TVars.Disjoint X2 X3 ->
  TVars.Disjoint X3 X1 ->
  exists m', IfMaps m' X X1 X2 X3 m m1 m2 m3.
Proof.
intros.
rewrite TVars.disjoint_iff in H3.
rewrite TVars.disjoint_iff in H4.
rewrite TVars.disjoint_iff in H5.
decompose [and] H3.
decompose [and] H4.
decompose [and] H5.
exists
 (merge (fun y => not_sumbool $ TVars.WProp.In_dec y X) m $
  merge (fun y => TVars.WProp.In_dec y X1) m1 $
  merge (fun y => TVars.WProp.In_dec y X2) m2 $
  merge (fun y => TVars.WProp.In_dec y X3) m3 $
  Table.empty A).
unfold IfMaps, app in |- *.
split; [ idtac | split; [ idtac | split ] ]; intros; try (split; intro MH).
 apply <- merge_iff.
 tauto.

 apply merge_iff in MH.
 decompose [or and] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge in |- *; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge with (m1 := m1) (m2 := m2),
         disjoint_merge in |- *; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge with (m1 := m1) (m2 := m2),
         disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH; [ assumption | contradiction  ].

 rewrite disjoint_merge with (m1 := m2) (m2 := m3),
         disjoint_merge with (m1 := m1) (m2 := m3),
         disjoint_merge; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge with (m1 := m2) (m2 := m3),
         disjoint_merge with (m1 := m1) (m2 := m3),
         disjoint_merge in MH; auto.
 apply merge_iff in MH.
 tauto.
Qed.

Lemma not_in_sub : forall A (m' m : table A) X,
  Disjoint m X ->
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U m <-> Table.MapsTo Y U m')) ->
  m = m' // X.
Proof.
intros.
apply Extensionality_Table.
apply <- TableWF.Equal_mapsto_iff.
intros.
unfold sub.
specialize (H0 k e).
split; intros.
 unfold Disjoint in H.
 decompose [and] (H k).
 destruct (TVars.WProp.In_dec k X).
  assert (Table.In k m).
   unfold Table.In, Table.Raw.PX.In in |- *.
   exists e.
   tauto.

   apply H2 in H4.
   contradiction.

  apply <- filter_iff.
  split; auto.
  apply H0 in n.
  apply n in H1.
  assumption.

 apply filter_iff in H1.
 decompose [and] H1.
 apply H0 in H3.
 apply H3 in H2.
 assumption.
Qed.

Lemma disjoint_fun_inv: forall X T1 T2,
  DisjointT X (FunT T1 T2) ->
  DisjointT X T1 /\ DisjointT X T2.
Proof.
unfold DisjointT, DisjointBy.
intros.
decompose [and] H.
repeat split; intros.
 apply H0 in H2.
 Contrapositive H2.
 apply FFunT.
 tauto.

 apply H1.
 apply FFunT.
 tauto.

 apply H0 in H2.
 Contrapositive H2.
 apply FFunT.
 tauto.

 apply H1.
 apply FFunT.
 tauto.
Qed.

Lemma disjoint_subst: forall T m' m X,
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U m <-> Table.MapsTo Y U m')) ->
  DisjointT X T ->
  m' = m // X ->
  type_subst T m' = type_subst T m.
Proof.
intros.
induction T; intros; auto.
 unfold DisjointT, DisjointBy in H0.
 decompose [and] H0.
 destruct (TVars.WProp.In_dec s X).
  apply H2 in i.
  assert False; try contradiction.
  apply i.
  apply FVarT.

  apply mapsto_var_type_subst.
  intros.
  apply H with (U:=U) in n.
  tauto.

 apply disjoint_fun_inv in H0.
 decompose [and] H0.
 apply IHT1 in H2.
 apply IHT2 in H3.
 simpl.
 rewrite H2, H3.
 reflexivity.
Qed.

Lemma in_apply_union: forall A (Free : string -> A -> Prop) (T : A) x y X1 X2,
  Free x T -> DisjointBy Free X2 T ->
  ~ Free y T ->
  ~ TVars.In x X1 -> ~ TVars.In x (TVars.add y (TVars.union X1 X2)).
Proof.
intros.
Contrapositive H2.
rewrite TVars.WFact.add_iff, TVars.WFact.union_iff in H3.
decompose [or] H3.
 rewrite <- H4 in H.
 contradiction.

 assumption.

 unfold DisjointBy in H0.
 decompose [and] H0.
 apply H4 in H5.
 contradiction.
Qed.


Lemma in_if_union: forall A (Free : string -> A -> Prop) (T : A) x X1 X2 X3,
  Free x T ->
  DisjointBy Free X2 T ->
  DisjointBy Free X3 T ->
  ~ TVars.In x X1 -> ~ TVars.In x (TVars.union X1 (TVars.union X2 X3)).
Proof.
intros.
Contrapositive H2.
repeat (rewrite TVars.WFact.union_iff in H3).
decompose [or] H3; auto.
 unfold DisjointBy in H0.
 decompose [and] H0.
 apply H4 in H5.
 contradiction.

 unfold DisjointBy in H1.
 decompose [and] H1.
 apply H4 in H5.
 contradiction.
Qed.

Theorem completeness: forall t tenv Ts S T X C tsubst1,
  TypeConstraint t tenv Ts S X C ->
  TSolution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  exists tsubst2,
    tsubst1 = tsubst2 // X /\
    CSolution tsubst2 T tenv Ts t S C.
Proof.
intros until tsubst1.
intro.
generalize T.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; unfold CSolution in |- *; simpl in |- *; intros; auto.
 exists tsubst1.
 split; try (apply sub_empty).
 exists TVars.empty.
  split; [ | split].
   apply CTVar.
   trivial.

   apply unified_empty.

   apply var_inv with (S := T0) in H1; tauto.

 apply lambda_inv in H2.
 decompose [ex and] H2.
 apply H1 in H5; auto.
  decompose [ex and] H5.
  exists x1.
  split; auto.
  exists X0.
  repeat split; auto.
   apply CTLambda.
   tauto.

   rewrite <- H10, H6, H7.
   cut (type_subst T1 x1 = type_subst T1 (x1 // X0)).
    intros.
    rewrite H9.
    reflexivity.

    apply sub_type_subst.
    intros.
    apply tvars_not_free with (x := x3) in H0; auto.
    decompose [and] H0.
    unfold FreeTs in H11.
    Contrapositive H11.
    exists T1.
    split; auto.
    apply in_eq.

 exists tsubst1.
 split; (try apply sub_empty).
 exists TVars.empty.
 split; (try apply CTBool).
 split; (try (apply unified_empty)).
 inversion H0.
 reflexivity.

 apply apply_inv in H8.
 decompose [ex and] H8.
 rewrite H7 in H9.
 Dup H9.
 apply add_disjoint_iff in H9.
 rewrite union_disjoint_iff in H9.
 decompose [and] H9.
 apply H1 in H11; auto.
 apply H3 in H12; auto.
 decompose [ex and] H11.
 decompose [ex and] H12.
 assert (exists s,
       ApplyMaps s (TVars.add x (TVars.union X1 X2)) X1 X2 tsubst1 x1 x3 x T0).
  unfold CTApplyDisjoint in H4.
  decompose [and] H4.
  unfold Fresh in H5.
  decompose [and] H5.
  apply ex_ApplyMaps; auto; intros;
   rewrite TVars.WFact.add_iff, TVars.WFact.union_iff;
   tauto.

   decompose [ex] H23.
   exists x5.
   assert (type_subst (VarT x) x5 = T0).
    simpl.
    unfold ApplyMaps in H25.
    decompose [and] H25.
    apply TableWF.find_mapsto_iff in H30.
    rewrite H30.
    reflexivity.

    split.
     unfold ApplyMaps in H25.
     decompose [and] H25.
     rewrite H7.
     apply not_in_sub; auto.

     exists (TVars.add x (TVars.union X1 X2)).
     repeat split; auto.
     apply (CTApply _ _ _ T1 T2 _ _ _ X1 X2 C1 C2); auto.

     rewrite H6.
     rewrite unified_add_iff, <- unified_union_iff.
     repeat split; auto.
     assert (type_subst T1 x5 = type_subst T1 x1).
      apply free_mapsto_type_subst.
      intros.
      apply (free_mapsto _ T1 _ tsubst1 _ (TVars.add x (TVars.union X1 X2)) X1);
       (try (unfold ApplyMaps in H25;
             decompose [and] H25;
             tauto)).
      intros.
      apply (in_apply_union _ FreeT T1); auto.
       apply apply_disjoint_t in H4.
       tauto.

       unfold Fresh in H5.
       decompose [and] H5.
       tauto.

      assert (type_subst T2 x5 = type_subst T2 x3).
       apply free_mapsto_type_subst.
       intros.
       apply (free_mapsto _ T2 _ tsubst1 _ (TVars.add x (TVars.union X1 X2)) X2);
        (try (unfold ApplyMaps in H25;
              decompose [and] H25;
              tauto)).
       intros.
       rewrite TVars.union_sym.
       apply  apply_disjoint_sym in H4.
       apply (in_apply_union _ FreeT T2); auto.
        apply apply_disjoint_t in H4.
        tauto.

        unfold Fresh in H5.
        decompose [and] H5.
        tauto.

       simpl.
       simpl in H26.
       rewrite H26, H27, H28, <- H20, <- H24.
       reflexivity.

     apply (free_unified _ tsubst1 x1 (TVars.add x (TVars.union X1 X2)) X1);
        (try (unfold ApplyMaps in H25;
              decompose [and] H25;
              tauto)).
     intros.
     apply (in_apply_union _ FreeC C1); auto.
      apply apply_disjoint_c in H4.
      tauto.

      unfold Fresh in H5.
      decompose [and] H5.
      tauto.

     apply (free_unified _ tsubst1 x3 (TVars.add x (TVars.union X1 X2)) X2);
        (try (unfold ApplyMaps in H25;
              decompose [and] H25;
              tauto)).
     intros.
     rewrite TVars.union_sym.
     apply  apply_disjoint_sym in H4.
     apply (in_apply_union _ FreeC C2); auto.
      apply apply_disjoint_c in H4.
      assumption.

      unfold Fresh in H5.
      decompose [and] H5.
      assumption.

 rewrite H8 in H10.
 Dup H10.
 repeat (rewrite union_disjoint_iff in H10).
 decompose [and] H10.
 apply if_inv in H9.
 decompose [and] H9.
 apply H1 in H13; auto.
 apply H3 in H17; auto.
 apply H5 in H18; auto.
 decompose [ex and] H13.
 decompose [ex and] H17.
 decompose [ex and] H18.
 assert
   (exists s : _,
      IfMaps s (TVars.union X1 (TVars.union X2 X3)) X1 X2 X3 tsubst1 x x1 x3).
  apply ex_IfMaps;
  auto;
  try (unfold CTIfDisjoint in H6;
       decompose [and] H6;
       tauto).
   intros.
   repeat (rewrite TVars.WFact.union_iff).
   tauto.

   intros.
   repeat (rewrite TVars.WFact.union_iff).
   tauto.

   intros.
   repeat (rewrite TVars.WFact.union_iff).
   tauto.

  decompose [ex] H29.
  exists x5.
  split.
   unfold IfMaps in H31.
   decompose [and] H31.
   rewrite H8.
   apply not_in_sub; auto.

   exists (TVars.union X1 (TVars.union X2 X3)).
   assert (type_subst T2 x5 = type_subst T2 x1).
    apply free_mapsto_type_subst.
    intros.
    apply (free_mapsto _ T2 _ tsubst1 _ (TVars.union X1 (TVars.union X2 X3)) X2);
     try (unfold IfMaps in H31;
          decompose [and] H31;
          auto).
    intros.
    rewrite TVars.union_sym, <- TVars.union_assoc.
    unfold CTIfDisjoint in H6.
    decompose [and] H6.
    apply (in_if_union _ FreeT T2); auto.

    assert (type_subst T3 x5 = type_subst T3 x3).
     apply free_mapsto_type_subst.
     intros.
     apply (free_mapsto _ T3 _ tsubst1 _ (TVars.union X1 (TVars.union X2 X3)) X3);
      try (unfold IfMaps in H31;
           decompose [and] H31;
           auto).
     intros.
     rewrite TVars.union_sym, (TVars.union_sym X2 X3), <- TVars.union_assoc.
     unfold CTIfDisjoint in H6.
     decompose [and] H6.
     apply (in_if_union _ FreeT T3); auto.

     rewrite H32, <- H26.
     repeat split.
      apply (CTIf _ _ _ T1 _ T3 _ _ X1 X2 X3 _ C1 C2 C3); auto.

      rewrite H7.
      rewrite unified_add_iff, unified_add_iff, <- unified_union_iff,  <- unified_union_iff.
      rewrite H32, H33, <- H26, <- H30.
      repeat split; auto.
       simpl.
       rewrite H22.
       apply free_mapsto_type_subst.
       intros.
       unfold IfMaps in H31.
       decompose [and] H31.
       apply (free_mapsto _ T1 _ tsubst1 _ (TVars.union X1 (TVars.union X2 X3)) X1);
       auto.
       intros.
       unfold CTIfDisjoint in H6.
       decompose [and] H6.
       apply (in_if_union _ FreeT T1); auto.

       apply (free_unified _ tsubst1 x (TVars.union X1 (TVars.union X2 X3)) X1);
        try (unfold IfMaps in H31;
              decompose [and] H31;
              tauto).
        intros.
        unfold CTIfDisjoint in H6.
        decompose [and] H6.
        apply (in_if_union _ FreeC C1); auto.

       apply (free_unified _ tsubst1 x1 (TVars.union X1 (TVars.union X2 X3)) X2);
        try (unfold IfMaps in H31;
              decompose [and] H31;
              tauto).
        intros.
        rewrite TVars.union_sym, <- TVars.union_assoc.
        unfold CTIfDisjoint in H6.
        decompose [and] H6.
        apply (in_if_union _ FreeC C2); auto.

       apply (free_unified _ tsubst1 x3 (TVars.union X1 (TVars.union X2 X3)) X3);
        try (unfold IfMaps in H31;
              decompose [and] H31;
              tauto).
        intros.
        rewrite TVars.union_sym, (TVars.union_sym X2 X3), <- TVars.union_assoc.
        unfold CTIfDisjoint in H6.
        decompose [and] H6.
        apply (in_if_union _ FreeC C3); auto.
Qed.
