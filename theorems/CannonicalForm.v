Require Import List.
Require Import String.

Require Import Term.
Require Import Tables.
Require Import Eval.
Require Import TypingRule.

Lemma bool_can : forall v,
  Value v -> Typed v empty BoolT ->
  v = Bool true \/ v = Bool false.
Proof.
intros; induction v; simpl in H; try contradiction.
 destruct b; tauto.

 inversion H0.
Qed.

Lemma lambda_can : forall v S T,
  Value v -> Typed v empty (FunT S T) ->
  exists x : string, exists t : term, v = Lambda x S t.
Proof.
induction v; intros; simpl in H; try contradiction.
 inversion H0.

 inversion H0.
 exists s.
 exists v.
 reflexivity.
Qed.

