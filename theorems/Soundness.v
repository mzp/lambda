Require Import List.
Require Import String.

Require Import Tables.
Require Import Term.
Require Import Constraint.
Require Import ConstraintRule.
Require Import TypeSubst.
Require Import Solution.

Ltac Prepare H :=
 unfold CSolution in |- *;
 intros;
 decompose [ex and] H.

Lemma add_elim: forall x C tsubst,
 Unified (TConst.add x C) tsubst ->
 Unified C tsubst.
Proof.
intros.
destruct x.
apply unified_add_iff in H.
decompose [and] H.
assumption.
Qed.

Lemma var_solution_inv : forall T S tenv Ts tsubst x C,
  CSolution tsubst T tenv Ts (Var x) S C ->
  Table.MapsTo x T (tenv_subst tenv tsubst).
Proof.
Prepare H.
unfold tenv_subst in |- *.
apply <- TableWF.map_mapsto_iff.
exists S.
split; auto.
inversion H1.
tauto.
Qed.

Lemma lambda_solution_inv : forall tsubst T T1 T2 tenv Ts x t C,
  CSolution tsubst T tenv Ts (Lambda x T1 t) (FunT T1 T2) C ->
  T = FunT (type_subst T1 tsubst) (type_subst T2 tsubst) /\
  CSolution tsubst (type_subst T2 tsubst) (Table.add x T1 tenv) (T1::Ts) t T2 C.
Proof.
Prepare H.
split.
 simpl in H3.
 assumption.

 exists x0.
split; [ | split ]; auto.
inversion H1.
tauto.
Qed.

Lemma bool_solution_inv : forall tsubst T tenv Ts t C,
  CSolution tsubst T tenv Ts t BoolT C ->
  T = BoolT.
Proof.
Prepare H.
simpl in H3.
assumption.
Qed.

Lemma apply_solution_inv: forall tsubst tenv Ts t1 t2 T T1 T2 S C1 C2 X1 X2,
 TypeConstraint t1 tenv Ts T1 X1 C1 ->
 TypeConstraint t2 tenv Ts T2 X2 C2 ->
 CSolution tsubst S tenv Ts (Apply t1 t2) T (TConst.add (T1,FunT T2 T) (TConst.union C1 C2)) ->
   type_subst T1 tsubst = type_subst (FunT T2 T) tsubst /\
   CSolution tsubst (type_subst T1 tsubst) tenv Ts t1 T1 C1 /\
   CSolution tsubst (type_subst T2 tsubst) tenv Ts t2 T2 C2.
Proof.
Prepare H1.
split.
 apply unified_add_iff in H2.
 tauto.

 split;
  [ exists X1 |  exists X2 ];
  apply add_elim in H2;
  apply unified_union_iff in H2;
  tauto.
Qed.

Lemma if_solution_inv : forall t1 t2 t3 S T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv Ts tsubst,
  TypeConstraint t1 tenv Ts T1 X1 C1 ->
  TypeConstraint t2 tenv Ts T2 X2 C2 ->
  TypeConstraint t3 tenv Ts T3 X3 C3 ->
  CSolution tsubst S tenv Ts (If t1 t2 t3) T2
                  (TConst.add (T1, BoolT)
                            (TConst.add (T2, T3)
                                      (TConst.union C1 (TConst.union C2 C3)))) ->
  CSolution tsubst BoolT tenv Ts t1 T1 C1 /\
  CSolution tsubst S tenv Ts t2 T2 C2 /\
  CSolution tsubst S tenv Ts t3 T3 C3.
Proof.
Prepare H2.
split; [ | split].
 exists X1.
 split; [ | split]; auto.
  do 2 (apply add_elim in H3).
  apply unified_union_iff in H3.
  tauto.

  apply unified_add_iff in H3.
  decompose [and] H3.
  rewrite H5.
  reflexivity.

 exists X2.
 split; [ | split]; auto.
  do 2 (apply add_elim in H3).
  apply unified_union_iff in H3.
  decompose [and] H3.
  apply unified_union_iff in H7.
  tauto.

 exists X3.
 split; [ | split]; auto.
  do 2 (apply add_elim in H3).
  apply unified_union_iff in H3.
  decompose [and] H3.
  apply unified_union_iff in H7.
  tauto.

  apply add_elim in H3.
  apply unified_add_iff in H3.
  decompose [and] H3.
  rewrite <- H5,H6.
  reflexivity.
Qed.


Theorem soundness : forall t tenv Ts S X C T tsubst,
  TypeConstraint t tenv Ts S X C ->
  Constraint.Solution tsubst T tenv Ts t S C ->
  TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
generalize T.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; intros; unfold Solution in |- *; simpl in |- *.
 apply var_solution_inv in H1.
 apply TVar.
 trivial.

 apply lambda_solution_inv in H2.
 decompose [and] H2.
 apply H1 in H4.
 rewrite H3 in |- *.
 apply TLambda.
 rewrite add_eq in |- *.
 trivial.

 apply bool_solution_inv in H0.
 rewrite H0 in |- *.
 apply TBool.

 apply
  apply_solution_inv
   with
     (tsubst := tsubst)
     (T := VarT x)
     (t1 := t1)
     (T1 := T1)
     (S := T0)
     (C1 := C1)
     (X1 := X1) in H2.
  decompose [and] H2.
  apply TApply with (S := type_subst T2 tsubst).
   assert (T0 = type_subst (VarT x) tsubst).
    unfold Constraint.Solution in H13.
    decompose [ex] H13.
    decompose [and] H15.
    trivial.

    rewrite H15 in |- *.
    apply H1.
    simpl in |- *.
    simpl in H14.
    rewrite <- H14 in |- *.
    tauto.

   apply H3.
   tauto.

  trivial.

  rewrite <- H12 in |- *.
  trivial.

 apply (if_solution_inv t1 t2 t3 T0 T1 T2 T3 X1 X2 X3 C1 C2 C3 _ _ tsubst)
  in H4.
  decompose [and] H4.
  apply TIf; [apply H1 | apply H3 | apply H5]; trivial.

  trivial.

  trivial.

  rewrite <- H27 in |- *.
  trivial.

 trivial.
Qed.*)
