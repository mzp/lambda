Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import TypingRule.
Require Import Tables.
Require Import CannonicalForm.

Theorem Progress : forall t (r : type),
    Typed t TypingRule.empty r -> Value t \/ (exists t', Eval t t').
Proof.
induction t.
 intros.
 inversion H.
 apply Table.empty_1 in H1.
 contradiction .

 intros.
 left.
 simpl.
 tauto.

 intros.
 left.
 simpl.
 tauto.

 intros.
 right.
 inversion H.
 generalize H2, H5.
 apply IHt1 in H2; apply IHt2 in H5.
 intros.
 inversion H2.
  inversion H5.
   assert (exists s : string, exists body : term, t1 = Lambda s S body).
    apply lambda_can with (ty2 := r).
     exact H8.

     exact H6.

    decompose [ex] H10.
    rewrite H12 in |- *.
    exists (subst x0 x t2).
    apply ELambda.
    exact H9.

   decompose [ex] H9.
   exists (Apply t1 x).
   apply EAppRight.
    exact H8.

    exact H10.

  decompose [ex] H8.
  exists (Apply x t2).
  apply EAppLeft.
  exact H9.

 intros.
 right.
 inversion H.
 generalize H3, H6, H7.
 apply IHt1 in H3; apply IHt2 in H6; apply IHt3 in H7.
 intros.
 inversion H3.
  assert (t1 = Bool true \/ t1 = Bool false).
   apply bool_can.
    exact H11.

    exact H8.

   inversion H12.
    rewrite H13 in |- *.
    exists t2.
    apply EIfTrue.

    rewrite H13 in |- *.
    exists t3.
    apply EIfFalse.

  decompose [ex] H11.
  exists (If x t2 t3).
  apply EIfCond.
  exact H12.
Qed.

