Require Import List.
Require Import String.

Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TypingRule.
Require Import Constraint.
Require Import ConstraintRule.
Require Import TypeSubst.
Require Import Solution.
Require Import CSolutionInv.

Theorem soundness : forall t tenv Ts S X C T tsubst,
  TypeConstraint t tenv Ts S X C ->
  CSolution tsubst T tenv Ts t S C ->
  TSolution tsubst T tenv t.
Proof.
unfold TSolution.
intros until tsubst.
intro.
generalize T.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; simpl; intros; auto.
 apply var_solution_inv in H1.
 apply TVar.
 tauto.

 apply lambda_solution_inv in H2.
 decompose [and] H2.
 apply H1 in H4.
 rewrite H3 in |- *.
 apply TLambda.
 rewrite add_eq in |- *.
 tauto.

 apply bool_solution_inv in H0.
 rewrite H0 in |- *.
 apply TBool.

 Dup H8.
 apply (apply_solution_inv _ T1 T2 T0 C1 C2 _ X1 X2) in H8; auto.
 decompose [and] H8.
 apply TApply with (S := type_subst T2 tsubst).
  assert (T0 = type_subst (VarT x) tsubst).
   unfold CSolution in H9.
   decompose [ex and] H9.
   tauto.

   rewrite H11 in |- *.
   apply H1.
   simpl in H10.
   simpl.
   rewrite <- H10.
   tauto.

  apply H3.
  tauto.

 apply (if_solution_inv T0 T1 T2 T3 X1 X2 X3 _ C1 C2 C3) in H9; auto.
 decompose [and] H9.
 apply TIf;
  [ apply H1 | apply H3 | apply H5 ];
  trivial.
Qed.
