Require Import List.
Require Import String.

Require Import Util.
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
intros until S.
intro.
pattern t,tenv,T.
apply Typed_ind; auto; intros; simpl.
 destruct (string_dec s x).
  apply TableWF.MapsTo_fun with (e := T0) in H3.
  apply TVar.
  rewrite <- H3.
  apply Table.add_1; auto.
  rewrite <- e in |- *.
  tauto.

  apply TVar.
  apply Table.add_2; auto.
  Contrapositive H1.
  rewrite H4.
  apply FVar.

 apply TBool.

 destruct (string_dec x0 x).
  apply TLambda.
  assert (y <> x0).
   Contrapositive H3.
   rewrite H5 in |- *.
   apply BLambda1.

   rewrite <- add_2 in |- *; auto.
   apply weaking_intro;
    [ apply not_free_lambda with (y := x0) (T:=T0)
    | apply not_bound_lambda with (y := x0) (T := T0)
    | ];
    tauto.

  apply TLambda.
  assert (y <> x0).
   Contrapositive H3.
   rewrite H5 in |- *.
   apply BLambda1.

   rewrite <- add_2; auto.
   apply H1;
     [ apply not_free_lambda with (y := x0) (T := T0)
     | apply not_bound_lambda with (y := x0) (T := T0)
     | apply Table.add_2 ];
     tauto.

 apply TApply with (S := S0);
  [ apply H1 | apply H3 ];
  try (apply not_free_apply in H4; tauto);
  try (apply not_bound_apply in H5; tauto);
  tauto.

 apply TIf;
  [ apply H1 | apply H3 | apply H5];
  try (apply not_free_if  in H6; tauto);
  try (apply not_bound_if in H7; tauto);
  tauto.
Qed.

Lemma subst_preserve : forall t s x T S tenv,
  Typed t (Table.add x S tenv) T -> Typed s tenv S ->
  Typed (subst t x s) tenv T.
Proof.
intros x0 s x.
functional induction (subst x0 x s); intros; inversion H.
 rewrite _x in H2.
 apply TableWF.add_mapsto_iff in H2.
 decompose [or and] H2; try tauto.
 rewrite <- H7 in |- *.
 tauto.

 apply TableWF.add_mapsto_iff in H2.
 decompose [or and] H2.
  apply sym_eq in H6.
  contradiction.

  apply TVar.
  tauto.

 apply TBool.

 apply TLambda.
 rewrite _x,add_1 in H6.
 rewrite _x in |- *.
 trivial.

 apply TLambda.
 apply IHt with (S := S).
  destruct (string_dec x (Fresh old new body)).
   rewrite <- e, alpha_id in |- *.
   rewrite <- add_2; auto.

   assert (old <> Fresh old new body).
    apply Fresh_x.

    rewrite <- add_2; auto.
    apply weaking_elim with (s := x) (S := T).
     apply alpha_not_free.
     trivial.

     rewrite <- add_2 in |- *.
     apply alpha_preserve.
      trivial.

      apply Fresh_fv2.

      apply Fresh_bv2.

      apply Table.add_1.
      reflexivity.

      apply sym_not_eq.
      tauto.

  apply weaking_intro;
   [apply Fresh_fv1 | apply Fresh_bv1 | trivial].

 apply TApply with (S := S0);
  [ apply IHt with (S := S) | apply IHt0 with (S := S) ];
  tauto.

 apply TIf;
  [ apply IHt with (S := S) | apply IHt0 with (S := S) | apply IHt1 with (S := S) ];
  tauto.
Qed.
