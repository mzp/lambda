Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Tables.


Theorem TypeUniq :
  forall (t : term) (tenv : tenv) (r1 r2 : type),
    Typed t tenv r1 -> Typed t tenv r2 -> r1 = r2.
Proof.
induction t.
 intros.
 inversion H.
 inversion H0.
 generalize H2 H6.
 apply TableWF.MapsTo_fun.

 intros.
 inversion H.
 inversion H0.
 reflexivity.

 intros.
 inversion H.
 inversion H0.
 assert (S = S0).
  generalize H6, H12.
  apply IHt.

  rewrite H13 in |- *.
  reflexivity.

 intros.
 inversion H.
 inversion H0.
 assert (FunT S r1 = FunT S0 r2).
  generalize H3, H9.
  apply IHt1.

  inversion H13.
  reflexivity.

 intros.
 inversion H.
 inversion H0.
 generalize H7, H15.
 apply IHt2.
Qed.
