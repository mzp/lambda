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
intros; induction v; simpl in H.
 contradiction.

 destruct b; tauto.

 inversion H0.

 contradiction.

 contradiction.
Qed.

Lemma lambda_can :
  forall (v : term) (ty1 ty2 : type),
    Value v -> Typed v empty (FunT ty1 ty2) ->
      exists x : string, exists t : term, v = Lambda x ty1 t.
Proof.
induction v; intros; simpl in H.
 contradiction.

 inversion H0.

 inversion H0.
 exists s.
 exists v.
 reflexivity.

 contradiction.

 contradiction.
Qed.

