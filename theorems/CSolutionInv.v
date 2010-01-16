Require Import List.

Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TypeSubst.
Require Import Constraint.
Require Import ConstraintRule.
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

Lemma add_eq : forall x T tenv tsubst,
  Table.add x (type_subst T tsubst) (tenv_subst tenv tsubst) =
  tenv_subst (Table.add x T tenv) tsubst.
Proof.
intros.
unfold tenv_subst in |- *.
change (type_subst T tsubst)
  with ((fun T0 : type => type_subst T0 tsubst) T)
  in |- *.
rewrite <- map_add.
reflexivity.
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

Lemma apply_solution_inv: forall T T1 T2 S C1 C2 C X1 X2 tsubst tenv Ts t1 t2 ,
 CSolution tsubst S tenv Ts (Apply t1 t2) T C ->
 C = TConst.add (T1,FunT T2 T) (TConst.union C1 C2) ->
 TypeConstraint t1 tenv Ts T1 X1 C1 ->
 TypeConstraint t2 tenv Ts T2 X2 C2 ->
   type_subst T1 tsubst = type_subst (FunT T2 T) tsubst /\
   CSolution tsubst (type_subst T1 tsubst) tenv Ts t1 T1 C1 /\
   CSolution tsubst (type_subst T2 tsubst) tenv Ts t2 T2 C2.
Proof.
Prepare H.
split.
 rewrite H0 in H3.
 apply unified_add_iff in H3.
 tauto.

 rewrite H0 in H3.
 split;
  [ exists X1 |  exists X2 ];
  apply add_elim in H3;
  apply unified_union_iff in H3;
  tauto.
Qed.


Lemma if_solution_inv : forall S T1 T2 T3 X1 X2 X3 C C1 C2 C3 t1 t2 t3 tenv Ts tsubst,
  CSolution tsubst S tenv Ts (If t1 t2 t3) T2 C ->
  C = TConst.add (T1, BoolT)
                 (TConst.add (T2, T3)
                             (TConst.union C1 (TConst.union C2 C3))) ->

  TypeConstraint t1 tenv Ts T1 X1 C1 ->
  TypeConstraint t2 tenv Ts T2 X2 C2 ->
  TypeConstraint t3 tenv Ts T3 X3 C3 ->
  CSolution tsubst BoolT tenv Ts t1 T1 C1 /\
  CSolution tsubst S tenv Ts t2 T2 C2 /\
  CSolution tsubst S tenv Ts t3 T3 C3.
Proof.
Prepare H.
rewrite H0 in H4.
split; [ | split].
 exists X1.
 split; [ | split]; auto.
  do 2 (apply add_elim in H4).
  apply unified_union_iff in H4.
  tauto.

  apply unified_add_iff in H4.
  decompose [and] H4.
  rewrite H6.
  reflexivity.

 exists X2.
 split; [ | split]; auto.
  do 2 (apply add_elim in H4).
  apply unified_union_iff in H4.
  decompose [and] H4.
  apply unified_union_iff in H8.
  tauto.

 exists X3.
 split; [ | split]; auto.
  do 2 (apply add_elim in H4).
  apply unified_union_iff in H4.
  decompose [and] H4.
  apply unified_union_iff in H8.
  tauto.

  apply add_elim in H4.
  apply unified_add_iff in H4.
  decompose [and] H4.
  rewrite <- H6,H7.
  reflexivity.
Qed.
