Require Import List.
Require Import String.
Require Import Lambda.

Lemma bool_can :
  forall (v : term),
    Value v -> Typed v empty_env BoolT ->
      v = Bool true \/ v = Bool false.
Proof.
intros.
inversion H.
 rewrite <- H1 in H0.
 inversion H0.
 simpl in H3.
 discriminate.

 destruct b.
  left.
  reflexivity.

  right.
  reflexivity.

 rewrite <- H1 in H0.
 inversion H0.
Qed.

Lemma lambda_can :
  forall (v : term) (ty1 ty2 : type),
    Value v -> Typed v empty_env (FunT ty1 ty2) ->
      exists x : string, exists body : term, v = Lambda x ty1 body.
Proof.
intros.
inversion H.
 rewrite <- H1 in H0.
 inversion H0.
 simpl in H3.
 discriminate.

 rewrite <- H1 in H0.
 inversion H0.

 exists x; exists body.
 rewrite <- H1 in H0.
 inversion H0.
 reflexivity.
Qed.
