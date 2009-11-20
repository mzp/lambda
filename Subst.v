Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import Typing.
Require Import TypingFact.

Theorem subst_preserve : forall t s x T S tenv,
    Typed t (TEnv.add x S tenv) T -> Typed s tenv S -> Typed (subst t x s) tenv T.
Proof.
intros x0 s x.
functional induction (subst x0 x s) .
 intros.
 rewrite _x in H.
 inversion H.
 apply TEnvWF.add_mapsto_iff in H2.
 decompose [or] H2.
  inversion H5.
  rewrite <- H7 in |- *.
  exact H0.

  inversion H5.
  tauto.

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

 intros.
 inversion H.
 apply TBool.

 intros.
 inversion H.
 apply TLambda.
 rewrite _x in H6.
 apply permutation with (tenv2 := TEnv.add x T tenv) in H6.
  exact H6.

  rewrite _x in |- *.
  apply Equal_add_1.
  reflexivity.

 intros.
 simpl in |- *.
