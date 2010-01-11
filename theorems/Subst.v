Require Import List.
Require Import String.

Require Import Term.
Require Import Weaking.
Require Import Eval.
Require Import Alpha.
Require Import AlphaFact.
Require Import Typing.
Require Import Tables.

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
    apply add_elim with (s := x) (S := T).
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

  apply add_intro; [apply Fresh_fv1 | apply Fresh_bv1 | trivial].

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
