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
 apply TEnv.empty_1 in H3.
 tauto.

 destruct b.
  left; reflexivity.

  right; reflexivity.

 rewrite <- H1 in H0.
 inversion H0.
Qed.

Lemma lambda_can :
  forall (v : term) (ty1 ty2 : type),
    Value v -> Typed v empty_env (FunT ty1 ty2) ->
      exists x : string, exists body : term, v = Lambda x ty1 body.
Proof.
intros.
inversion H0.
 apply TEnv.empty_1 in H1.
 tauto.

 exists x.
 exists body.
 reflexivity.

 rewrite <- H3 in H.
 inversion H.

 rewrite <- H4 in H.
 inversion H.
Qed.
