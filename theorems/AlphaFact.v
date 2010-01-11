Require Import List.
Require Import String.

Require Import Term.
Require Import Var.
Require Import Alpha.
Require Import Typing.
Require Import Weaking.
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
   apply add_intro.
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

