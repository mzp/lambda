Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import Typing.
Require Import CannonicalForm.

Theorem Progress : forall t r,
    Typed t empty_env r -> Value t \/ Reducible t.
Proof.
 induction t.
 (* var *)
 intros.
 inversion H.
 apply TEnv.empty_1 in H1.
 contradiction.

 (* bool *)
 left; apply VBool.

 (* lambda *)
 intros.
 left; apply VLambda.

 (* apply *)
 intros.
 right.
 inversion H.
 generalize H2, H5.
 apply IHt1 in H2.
 apply IHt2 in H5.
 case H2.
  case H5.
   (* App t1 t2, for t1 = Lambda x t body *)
   intros.
   assert (exists s : string, exists body : term, t1 = Lambda s a body).
    generalize H7, H8.
    apply lambda_can.

    decompose [ex] H10.
    rewrite H12 in |- *.
    apply RLambda.

   (* App t1 t2, for t2 is reducible *)
   intros.
   generalize H6.
   apply RAppRight.

  (* App t1 t2, for t1 is reducible *)
  intros.
  generalize H6.
  apply RAppLeft.

 (* if *)
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

