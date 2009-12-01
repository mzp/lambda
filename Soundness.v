Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Constraint.
Require Import TypeSubst.

Lemma lambda_solution: forall tsubst T S T1 T2 tenv x t C,
  Constraint.Solution tsubst T tenv (Lambda x T1 t) (FunT T1 T2) C ->
  TypeSubst T2 S tsubst ->
  Constraint.Solution tsubst S (TEnv.add x T1 tenv) t T2 C.
Proof.
unfold Constraint.Solution in |- *.
intros.
decompose [ex] H.
exists x0.
inversion H1.
inversion H3.
split.
 inversion H2.
 trivial.

 split.
  trivial.

  inversion H5.
  trivial.
Qed.

Lemma lambda_intro : forall T1 T2 S1 tsubst tenv x t,
  TypeSubst T1 S1 tsubst ->
  Solution tsubst T2 (TEnv.add x T1 tenv) t ->
  Solution tsubst (FunT S1 T2) tenv (Lambda x T1 t).
Proof.
unfold Solution in |- *.
intros.
inversion H2.
assert (S = S1).
 apply subst_uniq with (T := T1) (tsubst := tsubst).
  exact H8.

  exact H.

 rewrite H10 in |- *.
 apply TLambda.
 apply H0.
  apply subst_add.
   exact H1.

   exact H.

  exact H9.
Qed.


Lemma apply_solution: forall tsubst tenv x S S1 S2 t1 t2 C,
  Constraint.Solution tsubst S tenv (Apply t1 t2) (VarT x) C ->
  exists C1, exists C2, exists T1, exists T2,
  TypeSubst T1 S1 tsubst ->
  TypeSubst T2 S2 tsubst ->
  C = (AddConst (T1,FunT T2 (VarT x)) (UnionConst C1 C2)) /\
  Constraint.Solution tsubst S1 tenv t1 T1 C1 /\
  Constraint.Solution tsubst S2 tenv t2 T2 C2.
Proof.
unfold Constraint.Solution in |- *.
intros.
decompose [ex] H.
inversion H0.
inversion H2.
inversion H1.
exists C1; exists C2; exists T1; exists T2.
intros.
split.
 trivial.

 split.
  exists X1.
  split.
   trivial.

   split.
    apply Unified_Union with (C2 := C2).
    apply Unified_Add with (c := (T1, FunT T2 (VarT x))).
    rewrite <- H18 in |- *.
    trivial.

    trivial.

  exists X2.
  split.
   trivial.

   split.
    apply Unified_Union with (C2 := C1).
    unfold UnionConst in |- *.
    rewrite Union_sym in |- *.
    apply Unified_Add with (c := (T1, FunT T2 (VarT x))).
    unfold UnionConst in H16.
    unfold UnionConst in H18.
    rewrite <- H18 in |- *.
    trivial.

    trivial.
Qed.

Theorem soundness : forall tenv t T S X C tsubst,
  TypeConstraint t tenv S X C ->
  Constraint.Solution tsubst T tenv t S C ->
  TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
generalize T.
generalize C.
generalize S.
pattern t, tenv, S, X, C in |- *.
apply TypeConstraint_ind.
 intros.
 unfold Constraint.Solution in H1.
 unfold Solution in |- *.
 intros.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Var s) (tenv1 := tenv0) (T := S0).
  decompose [ex] H1.
  inversion H4.
  inversion H5.
  apply TVar.
  trivial.

  trivial.

  trivial.

  inversion H1.
  inversion H4.
  inversion H6.
  trivial.

 intros.
 generalize H2; intro.
 unfold Constraint.Solution in H3.
 decompose [ex] H3.
 inversion H4.
 inversion H5; inversion H6.
 rewrite <- H11 in H16.
 inversion H16.
 rewrite <- H11 in H2.
 apply lambda_solution with (S := S2) in H2.
  apply H1 in H2.
  apply lambda_intro.
   trivial.

   trivial.

  trivial.

 unfold Solution in |- *.
 unfold Constraint.Solution in |- *.
 intros.
 decompose [ex] H0.
 inversion H3.
 inversion H4; inversion H5.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Bool b) (tenv1 := tenv0) (T := BoolT).
  apply TBool.

  trivial.

  trivial.

  rewrite <- H8 in H12.
  trivial.

 intros.
