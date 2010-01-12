Require Import List.
Require Import String.

Require Import Term.
Require Import TypingRule.
Require Import Tables.

Theorem TypeUniq : forall t tenv S T,
  Typed t tenv S -> Typed t tenv T -> S = T.
Proof.
intros until T.
intro.
generalize T.
pattern t,tenv,S.
apply Typed_ind; intros; auto.
 inversion H1.
 apply TableWF.MapsTo_fun with (m:=tenv0) (x:=s); auto.

 inversion H0.
 reflexivity.

 inversion H2.
 assert (S0 = S1).
  apply H1.
  tauto.

  rewrite H9 in |- *.
  reflexivity.

 inversion H4.
 assert (FunT S0 T0 = FunT S1 T1).
  apply H1.
  tauto.

  inversion H11.
  reflexivity.

 inversion H6.
 apply H3.
 tauto.
Qed.

