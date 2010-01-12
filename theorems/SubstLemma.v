Require Import List.
Require Import String.

Require Import Term.
Require Import Var.
Require Import Weaking.
Require Import Eval.
Require Import Alpha.
Require Import TypingRule.
Require Import Tables.

Lemma alpha_preserve : forall t tenv x y T S,
  Typed t tenv T -> ~Free y t -> ~Bound y t -> Table.MapsTo x S tenv ->
     Typed (alpha t x y) (Table.add y S tenv) T.
Proof.
induction t.
 intros.
 simpl in |- *.
 destruct (string_dec s x).
  inversion H.
  apply TableWF.MapsTo_fun with (e := T) in H2.
   rewrite <- H2 in |- *.
   apply TVar.
   apply Table.add_1.
   reflexivity.

   rewrite <- e in |- *.
   exact H4.

  apply TVar.
  inversion H.
  apply Table.add_2.
   intro; apply H0.
   rewrite H7 in |- *.
   apply FVar.

   exact H4.

 intros.
 simpl in |- *.
 inversion H.
 apply TBool.

 intros.
 simpl in |- *.
 destruct (string_dec s x).
  inversion H.
  apply TLambda.
  assert (y <> s).
   intro.
   apply H1.
   rewrite H9 in |- *.
   apply BLambda1.

   generalize H9; intro.
   apply (add_2 _ tenv y s S t) in H9.
   rewrite <- H9 in |- *.
   apply weaking_intro.
    apply not_free_lambda with (y := s) (T := t); trivial.
    apply not_bound_lambda with (y := s) (T := t); trivial.
    trivial.

  inversion H.
  apply TLambda.
  assert (y <> s).
   intro.
   apply H1.
   rewrite H9 in |- *.
   apply BLambda1.

   generalize H9; intro.
   apply (add_2 _ tenv y s S t) in H9.
   rewrite <- H9 in |- *.
   apply IHt.
    trivial.
    apply not_free_lambda with (y := s) (T := t); trivial.
    apply not_bound_lambda with (y := s) (T := t).
    trivial.

    apply Table.add_2; trivial.

 intros.
 inversion H.
 simpl in |- *.
 apply TApply with (S := S0).
  apply IHt1.
   trivial.
   apply not_free_apply in H0; tauto.
   apply not_bound_apply in H1; tauto.
   tauto.

  apply IHt2.
   trivial.
   apply not_free_apply in H0; tauto.
   apply not_bound_apply in H1; tauto.
   tauto.

 intros.
 simpl in |- *.
 inversion H.
 apply TIf.
  apply IHt1.
   trivial.
   apply not_free_if in H0; tauto.
   apply not_bound_if in H1; tauto.
   trivial.

  apply IHt2.
   trivial.
   apply not_free_if in H0; tauto.
   apply not_bound_if in H1; tauto.
   trivial.

  apply IHt3.
   trivial.
   apply not_free_if in H0; tauto.
   apply not_bound_if in H1; tauto.
   trivial.
Qed.

Lemma subst_preserve : forall t s x T S tenv,
    Typed t (Table.add x S tenv) T -> Typed s tenv S -> Typed (subst t x s) tenv T.
Proof.
intros x0 s x.
functional induction (subst x0 x s) .
 intros.
 rewrite _x in H.
 inversion H.
 apply TableWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H5.
  rewrite <- H7 in |- *.
  trivial.

  inversion H5.
  tauto.

 intros.
 inversion H.
 apply TableWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H5.
  apply sym_eq in H6.
  contradiction .

  apply TVar.
  inversion H5.
  trivial.

 intros.
 inversion H.
 apply TBool.

 intros.
 inversion H.
 apply TLambda.
 rewrite _x in H6.
 rewrite (add_1 _ tenv old T S) in H6.
 rewrite _x in |- *.
 trivial.

 intros.
 inversion H.
 apply TLambda.
 apply IHt with (S := S).
  destruct (string_dec x (Fresh old new body)).
   rewrite <- e in |- *.
   rewrite alpha_id in |- *.
   generalize _x.
   intro.
   apply (add_2 _ tenv x old T S) in _x0.
   rewrite <- _x0 in |- *.
   trivial.

   assert (old <> Fresh old new body).
    apply Fresh_x.

    apply (add_2 _ tenv old (Fresh old new body) S T) in H7.
    rewrite H7 in |- *.
    apply weaking_elim with (s := x) (S := T).
     apply alpha_not_free.
     trivial.

     apply (add_2 _ (Table.add old S tenv) x (Fresh old new body) T T) in n.
     rewrite n in |- *.
     apply alpha_preserve.
      trivial.

      apply Fresh_fv2.

      apply Fresh_bv2.

      apply Table.add_1.
      reflexivity.

  apply weaking_intro; [apply Fresh_fv1 | apply Fresh_bv1 | trivial].

 intros.
 inversion H.
 apply TApply with (S := S0).
  apply IHt with (S := S); trivial.
  apply IHt0 with (S := S); trivial.

 intros.
 inversion H.
 apply TIf.
  apply IHt with (S := S); trivial.
  apply IHt0 with (S := S); trivial.
  apply IHt1 with (S := S); trivial.
Qed.
