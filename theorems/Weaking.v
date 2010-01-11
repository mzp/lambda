Require Import String.
Require Import Var.
Require Import Typing.
Require Import Term.
Require Import Tables.

Lemma add_elim: forall t S T tenv s,
    ~ Free s t -> Typed t (Table.add s S tenv) T -> Typed t tenv T.
Proof.
intro.
induction t.
 intros.
 inversion H0.
 apply TVar.
 apply TableWF.add_mapsto_iff in H2.
 inversion H2; inversion H5.
  assert (Free s0 (Var s)).
   rewrite H6 in |- *.
   apply FVar.

   contradiction.

  inversion H5.
  exact H7.

 intros.
 inversion H0.
 apply TBool.

 intros.
 inversion H0.
 apply TLambda.
 destruct (string_dec s s0).
  rewrite <- (add_1 _ tenv s t S) in |- *.
  rewrite <- e in H6.
  trivial.

  apply IHt with (S := S) (s := s0).
   apply not_free_lambda with (y := s) (T := t); auto.
   apply (add_2 _ tenv s s0 t S) in n.
   rewrite <- n in |- *.
   trivial.

 intros.
 inversion H0.
 apply TApply with (S := S0).
  apply IHt1 with (S := S) (s := s); auto.
   apply not_free_apply in H.
   tauto.

  apply IHt2 with (S := S) (s := s); auto.
   apply not_free_apply in H.
    tauto.

 intros.
 inversion H0.
 apply TIf.
  apply IHt1 with (S := S) (s := s); auto.
   apply not_free_if in H.
   tauto.

  apply IHt2 with (S := S) (s := s); auto.
   apply not_free_if in H.
   tauto.

  apply IHt3 with (S := S) (s := s); auto.
   apply not_free_if in H.
   tauto.
Qed.


Lemma add_intro: forall t S T tenv s,
    ~ Free s t -> ~ Bound s t -> Typed t tenv T -> Typed t (Table.add s S tenv) T.
Proof.
induction t.
 intros.
 apply TVar.
 apply Table.add_2.
  intro; apply H.
  rewrite H2 in |- *.
  apply FVar.

  inversion H1.
  trivial.

 intros.
 inversion H1.
 apply TBool.

 intros.
 inversion H1.
 apply TLambda.
 assert (s <> s0).
  intro.
  apply H0.
  rewrite H8 in |- *.
  apply BLambda1.

  generalize H8.
  intro.
  apply (add_2 _ tenv s s0 t S) in H8.
  rewrite H8 in |- *.
  apply IHt.
   intro.
   apply H.
   apply FLambda.
    apply sym_not_eq.
    trivial.

    trivial.

   intro.
   apply H0.
   apply BLambda2.
   trivial.

   trivial.

 intros.
 inversion H1.
 apply TApply with (S := S0).
  apply IHt1.
   intro; apply H.
   apply FApply.
   left; trivial.

   intro; apply H0.
   apply BApply.
   left; trivial.

   exact H4.

  apply IHt2.
   intro; apply H.
   apply FApply.
   right; trivial.

   intro; apply H0.
   apply BApply.
   right; trivial.

   exact H7.

 intros.
 inversion H1.
 apply TIf.
  apply IHt1.
   intro; apply H.
   apply FIf.
   left; trivial.

   intro; apply H0.
   apply BIf.
   left; trivial.

   exact H5.

  apply IHt2.
   intro; apply H.
   apply FIf.
   right; left; trivial.

   intro; apply H0.
   apply BIf.
   right; left; trivial.

   trivial.

  apply IHt3.
   intro; apply H.
   apply FIf.
   right; right; trivial.

   intro; apply H0.
   apply BIf.
   right; right; trivial.

   trivial.
Qed.
