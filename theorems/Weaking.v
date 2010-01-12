Require Import String.

Require Import Term.
Require Import Var.
Require Import TypingRule.
Require Import Tables.

Ltac Contrapositive H :=
  intro;
  apply H.

Lemma weaking_elim: forall t S T tenv s,
  ~ Free s t -> Typed t (Table.add s S tenv) T -> Typed t tenv T.
Proof.
intro.
induction t; intros; inversion H0.
 apply TVar.
 apply TableWF.add_mapsto_iff in H2.
 decompose [and or] H2.
  rewrite <- H6 in H.
  assert False.
   apply H.
   apply FVar.

   contradiction.

  tauto.

 apply TBool.

 apply TLambda.
 destruct (string_dec s s0).
  rewrite <- add_1 with (r2 := S) in |- *.
  rewrite <- e in H6.
  tauto.

  apply IHt with (S := S) (s := s0).
   apply not_free_lambda with (y := s) (T := t); auto.

   rewrite add_2 in |- *; auto.

 apply TApply with (S := S0);
 [ apply IHt1 with (S := S) (s := s)
 | apply IHt2 with (S := S) (s := s) ];
 auto;
 apply not_free_apply in H;
 tauto.

 apply TIf;
 [ apply IHt1 with (S := S) (s := s)
 | apply IHt2 with (S := S) (s := s)
 | apply IHt3 with (S := S) (s := s) ];
 apply not_free_if in H;
 tauto.
Qed.

Lemma weaking_intro: forall t S T tenv s,
  ~ Free s t -> ~ Bound s t -> Typed t tenv T -> Typed t (Table.add s S tenv) T.
Proof.
induction t; intros; inversion H1.
 apply TVar.
 apply <- TableWF.add_mapsto_iff.
 right.
 split; auto.
 Contrapositive H.
 rewrite H6 in |- *.
 apply FVar.

 apply TBool.

 apply TLambda.
 assert (s <> s0).
  Contrapositive H0.
  rewrite H8 in |- *.
  apply BLambda1.

  rewrite add_2 in |- *; auto.
  apply IHt; auto.
   Contrapositive H.
   apply FLambda; auto.

   Contrapositive H0.
   apply BLambda2.
   tauto.

 apply TApply with (S := S0);
  [ apply IHt1 | apply IHt2]; auto;
  try (Contrapositive H; apply FApply; tauto);
  try (Contrapositive H0; apply BApply; tauto).

 apply TIf;
  [ apply IHt1 | apply IHt2 | apply IHt3]; auto;
  try (Contrapositive H; apply FIf; tauto);
  try (Contrapositive H0; apply BIf; tauto).
Qed.
