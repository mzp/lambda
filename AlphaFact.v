Require Import List.
Require Import String.

Require Import Term.
Require Import Var.
Require Import Alpha.
Require Import Typing.
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
    apply Free_Lambda_inv with (y := s) (T := t); trivial.
    apply Bound_Lambda_inv with (y := s) (T := t); trivial.
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
    apply Free_Lambda_inv with (y := s) (T := t); trivial.
    apply Bound_Lambda_inv with (y := s) (T := t).
    trivial.

    apply Table.add_2; trivial.

 intros.
 inversion H.
 simpl in |- *.
 apply TApply with (a := a).
  apply IHt1.
   trivial.
   apply (Free_Apply_inv_1 y t1 t2); trivial.
   apply (Bound_Apply_inv_1 y t1 t2); trivial.
   trivial.

  apply IHt2.
   trivial.
   apply (Free_Apply_inv_2 y t1 t2); trivial.
   apply (Bound_Apply_inv_2 y t1 t2); trivial.
   trivial.

 intros.
 simpl in |- *.
 inversion H.
 apply TIf.
  apply IHt1.
   trivial.
   apply (Free_If_inv_1 y t1 t2 t3); trivial.
   apply (Bound_If_inv_1 y t1 t2 t3); trivial.
   trivial.

  apply IHt2.
   trivial.
   apply (Free_If_inv_2 y t1 t2 t3); trivial.
   apply (Bound_If_inv_2 y t1 t2 t3); trivial.
   trivial.

  apply IHt3.
   trivial.
   apply (Free_If_inv_3 y t1 t2 t3); trivial.
   apply (Bound_If_inv_3 y t1 t2 t3); trivial.
   trivial.
Qed.

