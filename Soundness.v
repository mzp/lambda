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
inversion H.
split.
 inversion H1.
 exact H10.

 inversion H2.
 split.
  exact H3.

  exact H0.
Qed.


Theorem soundness : forall tenv t T S C tsubst,
  TypeConstraint t tenv S nil C ->
  Constraint.Solution tsubst T tenv t S C ->
  TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
pattern t, tenv, S, (nil:tvars), C in |- *.
apply TypeConstraint_ind.
 intros.
 unfold Solution in |- *.
 intros.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Var s) (tenv1 := tenv0) (T := T0).
  apply TVar.
  exact H0.

  exact H2.

  exact H3.

  unfold Constraint.Solution in H1.
  inversion H1.
  inversion H5.
  exact H7.

(*intros.
unfold Solution in |- *.
intros.
apply
 subst_preserve
  with (tsubst := tsubst) (t := Var s) (tenv1 := tenv0) (T := T0).
 apply TVar.
 exact H0.

 exact H2.

 exact H3.

*)
