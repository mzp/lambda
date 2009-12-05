Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Constraint.
Require Import TypeSubst.

Theorem soundness : forall t tenv S X C T tsubst,
  TypeConstraint t tenv S X C -> Constraint.Solution tsubst T tenv t S C -> TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
generalize tenv, T, tsubst, C.
pattern t, tenv, S, X, C in |- *.
apply TypeConstraint_ind; intros; unfold Solution; simpl.
 apply var_solution_inv in H1.
 apply TVar.
 trivial.

 apply lambda_solution_inv in H2.
 inversion H2.
 apply H1 in H4.
 rewrite H3 in |- *.
 apply TLambda.
 unfold Solution in H4.
 rewrite add_eq in |- *.
 trivial.

 apply bool_solution_inv in H0.
 rewrite H0 in |- *.
 apply TBool.

(*gene
pattern t, tenv, S, X, C in |- *.

 apply var_solution_inv in H1.
 apply TVar.
 trivial.
*)

(*Lemma lambda_solution: forall tsubst T S T1 T2 tenv x t C,
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

Lemma apply_intro : forall T1 T2 tsubst tenv t1 t2,
  Solution tsubst (FunT T1 T2) tenv t1 ->
  Solution tsubst T1 tenv t2 ->
  Solution tsubst T2 tenv (Apply t1 t2).
Proof.
unfold Solution in |- *.
intros.
inversion H2.
apply TApply with (a := T1).
 apply H.
  trivial.

  trivial.

 apply H0.
  trivial.

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

Lemma apply_solution: forall tsubst tenv S T t1 t2 C,
  Constraint.Solution tsubst S tenv (Apply t1 t2) T C ->
  exists C1,exists C2, exists T1, exists T2,exists S1,exists S2,
  C = (AddConst (T1,FunT T2 T) (UnionConst C1 C2)) /\
  Constraint.Solution tsubst S1 tenv t1 T1 C1 /\
  Constraint.Solution tsubst S2 tenv t2 T2 C2.
Proof.
unfold Constraint.Solution in |- *.
intros.
decompose [ex] H.
inversion H0.
inversion H1.
exists C1; exists C2; exists T1; exists T2.
decompose [ex] (subst_exists T1 tsubst).
decompose [ex] (subst_exists T2 tsubst).
exists x1; exists x2.
split.
 trivial.

 split.
  exists X1.
  split.
   trivial.

   split.
    apply Unified_Union with (C2 := C2).
    apply Unified_Add with (c := (T1, FunT T2 (VarT x0))).
    rewrite <- H16 in |- *.
    inversion H2.
    trivial.

    trivial.

  exists X2.
  split.
   trivial.

   split.
    apply Unified_Union with (C2 := C1).
    unfold UnionConst in |- *.
    rewrite Union_sym in |- *.
    apply Unified_Add with (c := (T1, FunT T2 (VarT x0))).
    unfold UnionConst in H16.
    rewrite <- H16 in |- *.
    inversion H2.
    trivial.

    trivial.
Qed.


Proof.
intros until tsubst.
intro.
generalize T.
generalize S.
generalize C.
pattern t, tenv, S, X, C in |- *.
apply TypeConstraint_ind.
Focus 4.
 intros.
 assert
  (exists C1 : _,
     exists C2 : _,
       exists T1 : _,
         exists T2 : _,
           exists S1 : _,
             exists S2 : _,
               C3 = AddConst (T1, FunT T2 S0) (UnionConst C1 C2) /\
               Constraint.Solution tsubst S1 tenv0 t1 T1 C1 /\
               Constraint.Solution tsubst S2 tenv0 t2 T2 C2).
  apply apply_solution with (S := T0).
  trivial.

  decompose [ex] H11.
  inversion H13.
  inversion H14.
  apply H1 in H15.
  apply H3 in H16.
  inversion H14.
  apply unfold_tsubst in H17.
  apply unfold_tsubst in H18.
  generalize H10; intro.
  apply unfold_unified in H10.
  apply unfold_tsubst in H19.
  rewrite H12 in H10.
  apply unified_add in H10.
  inversion H10.
  inversion H20.
  inversion H22.
  assert (S2 = T0).
   apply subst_uniq with (tsubst := tsubst) (T := S0).
    trivial.

    trivial.

   rewrite <- H29 in |- *.
   apply apply_intro with (T1 := S1).
    rewrite H26 in |- *.
    assert (x6 = x4).
     apply subst_uniq with (tsubst := tsubst) (T := x2).
      trivial.

      trivial.

     rewrite H30 in |- *.
     trivial.

    assert (S1 = x5).
     apply subst_uniq with (tsubst := tsubst) (T := x3).
      trivial.

      trivial.

     rewrite H30 in |- *.
     trivial.

(* intros.
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

*)

*)

