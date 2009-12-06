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
generalize T, tsubst.
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

 apply
  apply_solution_inv
   with
     (tsubst := tsubst0)
     (T := VarT x)
     (t1 := t1)
     (T1 := T1)
     (S := T0)
     (C1 := C1)
     (X1 := X1) in H2.
  inversion H2.
  inversion H12.
  apply TApply with (a := type_subst T2 tsubst0).
   assert (T0 = type_subst (VarT x) tsubst0).
    unfold Constraint.Solution in H10.
    inversion H10.
    inversion H15.
    inversion H17.
    trivial.

    rewrite H15 in |- *.
    apply H1.
    simpl in |- *.
    simpl in H11.
    rewrite <- H11 in |- *.
    trivial.

   apply H3.
   trivial.

  trivial.

  rewrite <- H9 in |- *.
  trivial.

 apply (if_solution_inv t1 t2 t3 T0 T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv0 tsubst0)
  in H4.
  inversion H4.
  inversion H13.
  apply TIf.
   apply H1.
   trivial.

   apply H3.
   trivial.

   apply H5.
   trivial.

  trivial.

  trivial.

  rewrite <- H10 in |- *.
  trivial.

 trivial.
Qed.
