Require Import List.

Require Import String.

Require Import Util.
Require Import Term.
Require Import Eval.
Require Import TypingRule.
Require Import Tables.
Require Import CannonicalForm.

Theorem Progress : forall t tenv T,
  Typed t tenv T ->
  tenv = TypingRule.empty ->
  Value t \/ (exists t', Eval t t').
Proof.
intros until T.
intro.
pattern t, tenv, T in |- *.
apply Typed_ind; intros; auto; try (simpl in |- *; tauto).
 rewrite H1 in H0.
 inversion H0.

 right.
 do 2 Dup H4.
 apply H1 in H4.
 apply H3 in H5.
 decompose [ex or] H4.
  decompose [ex or] H5.
   assert (exists s : string, exists t : term, t1 = Lambda s S t).
    apply lambda_can with (T := T0); auto.
    rewrite <- H6 in |- *.
    tauto.

    decompose [ex] H9.
    rewrite H11 in |- *.
    exists (subst x0 x t2).
    apply ELambda.
    tauto.

   exists (Apply t1 x).
   apply EAppRight; tauto.

  exists (Apply x t2).
  apply EAppLeft.
  tauto.

 right.
 do 3 Dup H6.
 apply H1 in H6.
 apply H3 in H7.
 apply H5 in H8.
 decompose [ex or] H6.
  assert (t1 = Bool true \/ t1 = Bool false).
   apply bool_can; auto.
   rewrite <- H9 in |- *.
   tauto.

   decompose [or] H11; rewrite H12 in |- *.
    exists t2.
    apply EIfTrue.

    exists t3.
    apply EIfFalse.

  exists (If x t2 t3).
  apply EIfCond.
  tauto.
Qed.
