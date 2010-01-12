Require Import List.
Require Import String.

Require Import Term.
Require Import TypingRule.
Require Import Tables.

Lemma var_inv : forall tenv T x,
  Typed (Var x) tenv T -> Table.MapsTo x T tenv.
Proof.
intros.
inversion H.
tauto.
Qed.

Lemma true_inv: forall tenv T,
  Typed  (Bool true) tenv T -> T = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma false_inv: forall tenv T,
  Typed  (Bool false) tenv T -> T = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma lambda_inv : forall tenv S T x t,
  Typed (Lambda x S t) tenv T ->
      exists U : type, Typed t (Table.add x S tenv) U /\ T = FunT S U.
Proof.
intros.
inversion H.
exists S0.
tauto.
Qed.

Lemma apply_inv : forall tenv T f x,
  Typed (Apply f x) tenv T ->
  exists S : type,  Typed f tenv (FunT S T) /\ Typed x tenv S.
Proof.
intros.
inversion H.
exists S.
tauto.
Qed.

Lemma if_inv: forall tenv T t1 t2 t3,
  Typed (If t1 t2 t3) tenv T ->
  Typed t1 tenv BoolT /\  Typed t2 tenv T /\ Typed t3 tenv T.
Proof.
intros.
inversion H.
tauto.
Qed.

