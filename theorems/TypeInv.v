Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Tables.

(* For Var *)
Lemma var_rel :
  forall (tenv : tenv) (r : type) (x : string),
  Typed (Var x) tenv r -> Table.MapsTo x r tenv.
Proof.
intros.
inversion H.
exact H1.
Qed.

(* For Bool *)
Lemma true_rel:
  forall  (tenv : tenv) (r : type) ,
  Typed  (Bool true) tenv r -> r = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma false_rel:
  forall (tenv : tenv) (r : type),
  Typed  (Bool false) tenv r -> r = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.

(* Lambda *)
Lemma lambda_rel :
  forall (tenv : tenv) (S T : type) (x : string) (t : term),
  Typed (Lambda x S t) tenv T ->
      exists U : type, Typed t (Table.add x S tenv) U /\ T = FunT S U.
Proof.
intros.
inversion H.
exists S0.
split; tauto.
Qed.

(* Apply *)
Lemma apply_rel :
  forall (tenv : tenv) (r : type) (f x : term),
    Typed (Apply f x) tenv r ->
      exists t : type,  Typed f tenv (FunT t r) /\ Typed x tenv t.
Proof.
intros.
inversion H.
exists S.
split.
 exact H2.

 exact H5.
Qed.

(* If *)
Lemma if_rel:
  forall (tenv : tenv) (r : type) (t1 t2 t3 : term),
    Typed (If t1 t2 t3) tenv r ->
      Typed t1 tenv BoolT /\  Typed t2 tenv r /\ Typed t3 tenv r.
Proof.
intros.
inversion H.
tauto.
Qed.

