Require Import List.
Require Import String.

Require Import TypeSubst.
Require Import Constraint.
Require Import TypingRule.
Require Import ConstraintRule.

Definition TSolution tsubst T tenv t :=
  Typed (term_subst t tsubst) (tenv_subst tenv tsubst) T.

Definition CSolution tsubst T tenv Ts t S C := exists X,
  TypeConstraint t tenv Ts S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

(*
Lemma var_solution_inv : forall T S tenv Ts tsubst x C,
  Solution tsubst T tenv Ts (Var x) S C ->
  Table.MapsTo x T (tenv_subst tenv tsubst).
Proof.
intros.
unfold Solution in H.
inversion H.
inversion H0.
unfold tenv_subst in |- *.
apply
 (TableWF.map_mapsto_iff tenv x T (fun T0 : type => type_subst T0 tsubst)).
inversion H1.
exists S.
inversion H2.
split; trivial.
Qed.

Lemma lambda_solution_inv : forall tsubst T T1 T2 tenv Ts x t C,
  Solution tsubst T tenv Ts (Lambda x T1 t) (FunT T1 T2) C ->
  T = FunT (type_subst T1 tsubst) (type_subst T2 tsubst) /\
  Solution tsubst (type_subst T2 tsubst) (Table.add x T1 tenv) (T1::Ts) t T2 C.
Proof.
unfold Solution in |- *.
intros.
inversion H.
inversion H0.
inversion H1; inversion H2.
split.
 simpl in H13.
 trivial.

 exists x0.
 split; [ trivial | split; [ trivial | reflexivity ] ].
Qed.

Lemma bool_solution_inv : forall tsubst T tenv Ts t C,
  Solution tsubst T tenv Ts t BoolT C ->
  T = BoolT.
Proof.
unfold Solution in |- *.
intros.
inversion H.
inversion H0.
inversion H2.
simpl in H4.
trivial.
Qed.

Lemma apply_solution_inv: forall tsubst tenv Ts t1 t2 T T1 T2 S C1 C2 X1 X2,
 TypeConstraint t1 tenv Ts T1 X1 C1 ->
 TypeConstraint t2 tenv Ts T2 X2 C2 ->
 Solution tsubst S tenv Ts (Apply t1 t2) T (TConst.add (T1,FunT T2 T) (TConst.union C1 C2)) ->
   type_subst T1 tsubst = type_subst (FunT T2 T) tsubst /\
   Solution tsubst (type_subst T1 tsubst) tenv Ts t1 T1 C1 /\
   Solution tsubst (type_subst T2 tsubst) tenv Ts t2 T2 C2.
Proof.
unfold Solution in |- *.
intros.
inversion H1.
inversion H2.
inversion H4.
split.
 unfold Unified in H5.
 apply H5.
 apply (TConst.WFact.add_iff (TConst.union C1 C2) _ _).
 left.
 simpl in |- *.
 split; reflexivity.

 split.
  exists X1.
  split.
   trivial.

   split.
    apply (Unified_Union C1 C2 tsubst).
    apply Unified_Add with (c := (T1, FunT T2 T)).
    trivial.

    reflexivity.

  exists X2.
  split.
   trivial.

   split.
    apply (Unified_Union C2 C1 tsubst).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T1, FunT T2 T)).
    trivial.

    reflexivity.
Qed.

Lemma if_solution_inv : forall t1 t2 t3 S T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv Ts tsubst,
  TypeConstraint t1 tenv Ts T1 X1 C1 ->
  TypeConstraint t2 tenv Ts T2 X2 C2 ->
  TypeConstraint t3 tenv Ts T3 X3 C3 ->
  Solution tsubst S tenv Ts (If t1 t2 t3) T2
                  (TConst.add (T1, BoolT)
                            (TConst.add (T2, T3)
                                      (TConst.union C1 (TConst.union C2 C3)))) ->
  Solution tsubst BoolT tenv Ts t1 T1 C1 /\
  Solution tsubst S tenv Ts t2 T2 C2 /\
  Solution tsubst S tenv Ts t3 T3 C3.
Proof.
unfold Solution in |- *.
intros.
inversion H2.
inversion H3.
inversion H5.
split.
 exists X1.
 split.
  trivial.

  split.
   apply (Unified_Union C1 (TConst.union C2 C3) tsubst).
   apply Unified_Add with (c := (T2, T3)).
   apply Unified_Add with (c := (T1, BoolT)).
   trivial.

   unfold Unified in H6.
   change BoolT with (type_subst BoolT tsubst) in |- *.
   apply sym_eq.
   apply H6.
   apply
    (TConst.WFact.add_iff
       (TConst.add (T2, T3) (TConst.union C1 (TConst.union C2 C3))) _ _).
   left.
   split; reflexivity.

 split.
  exists X2.
  split.
   trivial.

   split.
    apply (Unified_Union C2 C3 tsubst).
    apply (Unified_Union (TConst.union C2 C3) C1 tsubst).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    trivial.

  exists X3.
  split.
   trivial.

   split.
    apply (Unified_Union C3 C2).
    rewrite TConst.union_sym in |- *.
    apply (Unified_Union _ C1).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    rewrite H7 in |- *.
    unfold Unified in H6.
    apply H6.
    apply
     (TConst.WFact.add_iff
        (TConst.add (T2, T3) (TConst.union C1 (TConst.union C2 C3))) _ _).
    right.
    apply (TConst.WFact.add_iff (TConst.union C1 (TConst.union C2 C3)) _ _).
    left; split; reflexivity.
Qed.

Lemma empty_add : forall x s,
  TVars.FSet.Raw.empty <> TVars.FSet.Raw.add x s.
Proof.
intros.
unfold TVars.FSet.Raw.empty in |- *.
destruct s; intros; simpl.
 intro.
 inversion H.

 destruct (TVars.WProp.Dec.F.eq_dec x e); intro; inversion H.
Qed.

Lemma tvars_free : forall t X x tenv Ts S C,
  TypeConstraint t tenv Ts S X C ->
  TVars.In x X ->
  FreshTs x Ts /\ FreshTerm x t.
Proof.
intros until C.
intro.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; intros.
 (* Var *)
 inversion H1.

 (* Lambda *)
 apply H1 in H2.
 decompose [and] H2.
 split.
  unfold FreshTs in H3; unfold FreshTs in |- *.
  intros.
  apply H3.
  apply in_cons.
  trivial.

  apply FLambda.
  split.
   unfold FreshTs in H3.
   apply H3.
   apply in_eq.

   trivial.

 (* Bool *)
 inversion H0.

 (* Apply *)
 apply TVars.WFact.add_iff in H13.
 decompose [or] H13.
  rewrite <- H14 in |- *.
  unfold Fresh in H11.
  decompose [and] H11.
  split; [ trivial | apply FApply; split; trivial ].

  apply TVars.WFact.union_iff in H14.
  decompose [or] H14.
   split.
    apply H1 in H15.
    tauto.

    apply FApply; split; [ apply H1 in H15 | apply H7]; tauto.

   split.
    apply H3 in H15.
    tauto.

    apply FApply; split; [ apply H8 | apply H3 in H15]; tauto.

 (* If *)
 apply TVars.WFact.union_iff in H28.
 decompose [or] H28.
  split.
   apply H1 in H29.
   tauto.

   apply FIf.
   split.
    apply H1 in H29.
    tauto.

    split; [apply H9 | apply H10]; trivial.

  apply TVars.WFact.union_iff in H29.
  decompose [or] H29.
   split.
    apply H3 in H30.
    tauto.

    apply FIf.
    split.
     apply H11; trivial.

     split; [apply H3 in H30 | apply H12]; tauto.

   split.
    apply H5 in H30.
    tauto.

    apply FIf.
    split.
     apply H13; trivial.

     split; [apply H14 | apply H5 in H30]; tauto.

 trivial.
Qed.

Lemma use_t_not_fresh: forall x T,
  UseT x T -> ~ FreshT x T.
Proof.
induction T; intros.
 intro.
 inversion H; inversion H0.
 contradiction .

 inversion H.

 intro.
 inversion H0.
 decompose [and] H3.
 inversion H.
 decompose [or] H9.
  apply IHT1 in H11.
  contradiction .

  apply IHT2 in H11.
  contradiction .
Qed.

Lemma use_term_not_fresh: forall x T,
  UseTerm x T -> ~ FreshTerm x T.
Proof.
induction T; intros.
 inversion H.

 inversion H.

 intro.
 inversion H0; inversion H.
 decompose [and] H3.
 decompose [or] H8.
   apply use_t_not_fresh in H13; contradiction.

   apply IHT in H13; contradiction.

 intro.
 inversion H0; inversion H.
 decompose [and] H3.
 decompose [or] H7.
  apply IHT1 in H11; contradiction.

  apply IHT2 in H11; contradiction.

 intro.
 inversion H0; inversion H.
 decompose [and] H3.
 decompose [or] H8.
  apply IHT1 in H12; contradiction.

  apply IHT2 in H15; contradiction.

  apply IHT3 in H15; contradiction.
Qed.

Lemma use_c_not_fresh: forall x C,
  UseC x C -> ~ FreshC x C.
Proof.
unfold UseC in |- *; unfold FreshC in |- *.
intros.
decompose [ex] H.
decompose [and] H1.
intro.
specialize (H3 x0 x1).
apply H3 in H0.
decompose [and] H0.
decompose [or] H2;
 apply use_t_not_fresh in H6; contradiction.
Qed.*)