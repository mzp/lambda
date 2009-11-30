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


Lemma apply_solution: forall tsubst tenv x T S t1 t2 C,
  Constraint.Solution tsubst T tenv (Apply t1 t2) (VarT x) C ->
  (exists C, exists T1, TypeSubst T1 S tsubst -> Constraint.Solution tsubst S tenv t1 T1 C) /\
  (exists C, exists T1, TypeSubst T1 S tsubst -> Constraint.Solution tsubst S tenv t2 T1 C).
Proof.
unfold Constraint.Solution in |- *.
intros.
decompose [ex] H.
inversion H0.
inversion H1; inversion H2.
split.
 exists C1; exists T1; intro; exists X1.
 split.
  trivial.

  split.
   apply Unified_Union with (C2 := C2).
   apply Unified_Add with (c := (T1, FunT T2 (VarT x))).
   rewrite <- H16 in |- *.
   trivial.

   trivial.

 exists C2; exists T2.
 intro.
 exists X2.
 split.
  trivial.

  split.
   apply Unified_Union with (C2 := C1).
   unfold UnionConst in |- *.
   rewrite Union_sym in |- *.
   apply Unified_Add with (c := (T1, FunT T2 (VarT x))).
   unfold UnionConst in H16.
   rewrite <- H16 in |- *.
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
pattern t, tenv, S, X, C in |- *.
apply TypeConstraint_ind.
 (* var *)
 unfold Solution in |- *.
 intros.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Var s) (tenv1 := tenv0) (T := T0).
  apply TVar.
  trivial.

  trivial.

  trivial.

  unfold Constraint.Solution in H1.
  decompose [ex] H1.
  inversion H4.
  inversion H6.
  trivial.

 (* lambda *)
 intros.
 generalize H2; intro.
 unfold Constraint.Solution in H3.
 decompose [ex] H3.
 inversion H4.
 inversion H6.
 inversion H8.
 apply lambda_solution with (S := S2) in H2.
  apply H1 in H2.
  apply lambda_intro.
   trivial.

   trivial.

  trivial.

 (* bool *)
 unfold Solution in |- *.
 unfold Constraint.Solution in |- *.
 intros.
 decompose [ex] H0.
 inversion H3.
 inversion H5.
 inversion H7.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Bool b) (tenv1 := tenv0) (T := BoolT).
  apply TBool.

  trivial.

  trivial.

  apply SBoolT.

 intros.
 (* avoid coq bug: I cannot use "apply apply_solution in H10"  *)
 apply apply_solution in H10.
(* assert
  ((exists C : _,
      exists T1 : _,
        TypeSubst T1 S tsubst -> Constraint.Solution tsubst S tenv0 t1 T1 C) /\
   (exists C : _,
      exists T1 : _,
        TypeSubst T1 S tsubst -> Constraint.Solution tsubst S tenv0 t2 T1 C)).
  apply apply_solution with (x := x) (T := T0) (C := C0).
  trivial.

*)
