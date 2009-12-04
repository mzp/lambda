Require Import List.
Require Import String.

Require Import Term.
Require Import Tables.
Require Import Eval.
Require Import Typing.

Lemma bool_can :
  forall (v : term),
    Value v -> Typed v empty BoolT ->
      v = Bool true \/ v = Bool false.
Proof.
intros.
inversion H.
 destruct b.
  left; reflexivity.

  right; reflexivity.

 rewrite <- H1 in H0.
 inversion H0.
Qed.

Lemma lambda_can :
  forall (v : term) (ty1 ty2 : type),
    Value v -> Typed v empty (FunT ty1 ty2) ->
      exists x : string, exists body : term, v = Lambda x ty1 body.
Proof.
intros.
inversion H0.
 apply Table.empty_1 in H1.
 contradiction .

 exists x.
 exists body.
 reflexivity.

 rewrite <- H3 in H.
 inversion H.

 rewrite <- H4 in H.
 inversion H.
Qed.

