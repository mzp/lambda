Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import Alpha.
Require Import AlphaFact.
Require Import Typing.
Require Import TypingFact.

Lemma subst_preserve : forall t s x T S tenv,
    Typed t (TEnv.add x S tenv) T -> Typed s tenv S -> Typed (subst t x s) tenv T.
Proof.
intros x0 s x.
functional induction (subst x0 x s) .
 (* Var-1 *)
 intros.
 rewrite _x in H.
 inversion H.
 apply TEnvWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H5.
  rewrite <- H7 in |- *.
  exact H0.

  inversion H5.
  tauto.

 (* Var-2 *)
 intros.
 inversion H.
 apply TEnvWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H5.
  apply sym_eq in H6.
  contradiction .

  apply TVar.
  inversion H5.
  exact H7.

 (* Bool *)
 intros.
 inversion H.
 apply TBool.

 (* Lambda-1 *)
 intros.
 inversion H.
 apply TLambda.
 rewrite _x in H6.
 apply permutation with (tenv2 := TEnv.add x T tenv) in H6.
  exact H6.

  rewrite _x in |- *.
  apply Equal_add_1.
  reflexivity.

 (* Lambda-2 *)
 intros.
 inversion H.
 apply TLambda.
 apply IHt with (S := S).
  destruct (string_dec x (Flesh old new body)).
   rewrite <- e in |- *.
   rewrite alpha_id in |- *.
   apply permutation with (tenv1 := TEnv.add x T (TEnv.add old S tenv)).
    apply Equal_add_2.
    exact _x.

    exact H6.

   apply
    permutation
     with (tenv1 := TEnv.add (Flesh old new body) T (TEnv.add old S tenv)).
    apply Equal_add_2.
    apply sym_not_eq.
    apply Flesh_x.

    apply Typed_add_elim with (s := x) (S := T).
     apply alpha_fv.
     exact n.

     apply
      permutation
       with
         (tenv1 := TEnv.add (Flesh old new body) T
                     (TEnv.add x T (TEnv.add old S tenv))).
      apply Equal_add_2.
      apply sym_not_eq.
      exact n.

      apply alpha_preserve.
       exact H6.

       apply Flesh_fv2.

       apply Flesh_bv2.

       apply TEnv.add_1.
       reflexivity.

  apply Typed_add_intro.
   apply Flesh_fv1.

   apply Flesh_bv1.

   exact H0.

 (* Apply *)
 intros.
 inversion H.
 apply TApply with (a := a).
  apply IHt with (S := S).
   exact H3.

   exact H0.

  apply IHt0 with (S := S).
   exact H6.

   exact H0.

 (* If *)
 intros.
 inversion H.
 apply TIf.
  apply IHt with (S := S).
   exact H4.

   exact H0.

  apply IHt0 with (S := S).
   exact H7.

   exact H0.

  apply IHt1 with (S := S).
   exact H8.

   exact H0.
Qed.
