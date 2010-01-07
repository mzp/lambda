Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Constraint.
Require Import TypeSubst.

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
Qed.
