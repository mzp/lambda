Require Import Term.
Require Import Eval.
Require Import TypingRule.
Require Import SubstLemma.

Theorem preservation: forall t t' tenv T,
  Typed t tenv T -> Eval t t' -> Typed t' tenv T.
Proof.
intros until T.
intro.
generalize t'.
pattern t, tenv, T in |- *.
apply Typed_ind; intros; auto.
 inversion H1.

 inversion H0.

 inversion H2.

 inversion H4.
  apply TApply with (S := S);
   [ apply H1 | ];
   tauto.

  apply TApply with (S := S);
   [ | apply H3];
   tauto.

  apply subst_preserve with (S := S); auto.
  rewrite <- H5 in H0.
  inversion H0.
  tauto.

 inversion H6;
  [ apply TIf | rewrite <- H7 in |- * | rewrite <- H7 in |- * ];
  auto.
Qed.
