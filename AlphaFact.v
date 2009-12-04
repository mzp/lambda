Require Import List.
Require Import String.

Require Import Term.
Require Import Alpha.
Require Import Typing.
Require Import Tables.

Lemma alpha_fv : forall t x y,
  x <> y -> ~ FV x (alpha t x y).
Proof.
induction t.
 intros.
 simpl in |- *.
 destruct (string_dec s x).
  intro.
  apply H.
  inversion H0.
  reflexivity.

  intro.
  apply n.
  inversion H0.
  reflexivity.

 intros.
 simpl in |- *.
 intro.
 inversion H0.

 intros.
 simpl in |- *.
 destruct (string_dec s x).
  rewrite e in |- *.
  intro.
  inversion H0.
  tauto.

  intro.
  inversion H0.
  generalize H6.
  fold not in |- *.
  apply IHt.
  exact H.

 intros.
 simpl in |- *.
 intro.
 inversion H0.
 inversion H3.
  generalize H5.
  apply IHt1.
  exact H.

  generalize H5.
  apply IHt2.
  exact H.

 simpl in |- *.
 intros.
 intro.
 inversion H0.
 inversion H3.
  generalize H6.
  apply IHt1.
  exact H.

  inversion H6.
   generalize H7.
   apply IHt2.
   exact H.

   generalize H7.
   apply IHt3.
   exact H.
Qed.

Lemma alpha_preserve : forall t tenv x y T S,
  Typed t tenv T -> ~FV y t -> ~BV y t -> Table.MapsTo x S tenv ->
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
   apply FVVar.

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
   apply BVLambda1.

   generalize H9; intro.
   apply (add_2 _ tenv y s S t) in H9.
   rewrite <- H9 in |- *.
   apply add_intro.
    apply FV_Lambda_inv with (y := s) (T := t); trivial.
    apply BV_Lambda_inv with (y := s) (T := t); trivial.
    trivial.

  inversion H.
  apply TLambda.
  assert (y <> s).
   intro.
   apply H1.
   rewrite H9 in |- *.
   apply BVLambda1.

   generalize H9; intro.
   apply (add_2 _ tenv y s S t) in H9.
   rewrite <- H9 in |- *.
   apply IHt.
    trivial.
    apply FV_Lambda_inv with (y := s) (T := t); trivial.
    apply BV_Lambda_inv with (y := s) (T := t).
    trivial.

    apply Table.add_2; trivial.

 intros.
 inversion H.
 simpl in |- *.
 apply TApply with (a := a).
  apply IHt1.
   trivial.
   apply (FV_Apply_inv_1 y t1 t2); trivial.
   apply (BV_Apply_inv_1 y t1 t2); trivial.
   trivial.

  apply IHt2.
   trivial.
   apply (FV_Apply_inv_2 y t1 t2); trivial.
   apply (BV_Apply_inv_2 y t1 t2); trivial.
   trivial.

 intros.
 simpl in |- *.
 inversion H.
 apply TIf.
  apply IHt1.
   trivial.
   apply (FV_If_inv_1 y t1 t2 t3); trivial.
   apply (BV_If_inv_1 y t1 t2 t3); trivial.
   trivial.

  apply IHt2.
   trivial.
   apply (FV_If_inv_2 y t1 t2 t3); trivial.
   apply (BV_If_inv_2 y t1 t2 t3); trivial.
   trivial.

  apply IHt3.
   trivial.
   apply (FV_If_inv_3 y t1 t2 t3); trivial.
   apply (BV_If_inv_3 y t1 t2 t3); trivial.
   trivial.
Qed.

Lemma alpha_id: forall t x,
  alpha t x x = t.
Proof.
induction t.
 intro.
 simpl in |- *.
 destruct (string_dec s x).
  rewrite e in |- *.
  reflexivity.

  reflexivity.

 intro.
 simpl in |- *.
 reflexivity.

 intro.
 simpl in |- *.
 destruct (string_dec s x).
  reflexivity.

  rewrite IHt in |- *.
  reflexivity.

 intro.
 simpl in |- *.
 rewrite IHt1,  IHt2 in |- *.
 reflexivity.

 intro.
 simpl in |- *.
 rewrite IHt1,  IHt2,  IHt3 in |- *.
 reflexivity.
Qed.

