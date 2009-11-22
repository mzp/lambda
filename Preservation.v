Require Import Term.
Require Import Eval.
Require Import Typing.
Require Import TypingFact.
Require Import Subst.

Theorem preservation: forall t t' tenv T,
  Typed t tenv T -> Eval t t' -> Typed t' tenv T.
Proof.
induction t.
 intros.
 inversion H0.

 intros.
 inversion H0.

 intros.
 inversion H0.

 intros.
 inversion H.
 inversion H0.
  apply TApply with (a := a).
   apply IHt1.
    exact H3.

    exact H10.

   exact H6.

  apply TApply with (a := a).
   exact H3.

   apply IHt2.
    exact H6.

    exact H11.

  apply subst_preserve with (S := a).
   rewrite <- H7 in H3.
   inversion H3.
   exact H15.

   exact H6.

 intros.
 inversion H.
 inversion H0.
  apply TIf.
   apply IHt1.
    exact H4.

    exact H13.

   exact H7.

   exact H8.

  rewrite <- H9 in |- *.
  exact H7.

  rewrite <- H9 in |- *.
  exact H8.
Qed.
