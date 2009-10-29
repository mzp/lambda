Require Import List.
Require Import String.

Require Import Lambda.
Require Import CannonicalForm.

Theorem Progress :
  forall (t : term) (r : type),
    Typed t nil r -> Value t \/ Reducible t.
Proof.
 induction t.
 intros.
 left; apply ValVar.

 left; apply ValBool.

 intros.
 left; apply ValLambda.

 intros.
 right.
 inversion H.
 generalize H2, H5.
 apply IHt1 in H2.
 apply IHt2 in H5.
 case H2.
  case H5.
   intros.
   assert (exists s : string, exists body : term, t1 = Lambda s a body).
    generalize H7, H8.
    apply lambda_can.

    decompose [ex] H10.
    rewrite H12 in |- *.
    apply RLambda.

   intros.
   generalize H6.
   apply RAppRight.

  intros.
  generalize H6.
  apply RAppLeft.

 intros.
 right.
 inversion H.
 generalize H3.
 apply IHt1 in H3.
 destruct H3.
  intros.
  assert (t1 = Bool true \/ t1 = Bool false).
   generalize H3, H8.
   apply bool_can.

   decompose [or] H9.
    rewrite H10 in |- *.
    apply RIf.

    rewrite H10 in |- *; apply RIf.

  intro.
  generalize H3.
  apply RIfCond.
Qed.

