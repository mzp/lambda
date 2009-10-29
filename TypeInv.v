Require Import Lambda.
Require Import List.
Require Import String.

(* For Var *)
Lemma VarRel :
  forall (tenv : tenv) (r : type) (x : string),
  Typed (Var x) tenv r -> Some r = assoc x tenv.
Proof.
intros.
inversion H.
exact H1.
Qed.

(* For Bool *)
Lemma TrueRel:
  forall  (tenv : tenv) (r : type) ,
  Typed  (Bool true) tenv r -> r = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma FalseRel:
  forall (tenv : tenv) (r : type),
  Typed  (Bool false) tenv r -> r = BoolT.
Proof.
intros.
inversion H.
reflexivity.
Qed.



Lemma LambdaRel :
  forall (tenv : tenv) (r a : type) (x : string) (body : term),
  Typed (Lambda x a body) tenv r ->
      exists b : type, Typed body ((x,a)::tenv) b /\ r = FunT a b.
Proof.
intros.
inversion H.
exists b.
split.
 exact H5.

 reflexivity.
Qed.

Lemma ApplyRel:
  forall (tenv : tenv) (r : type) (f x : term),
    Typed (Apply f x) tenv r ->
      exists t : type,  Typed f tenv (FunT t r) /\ Typed x tenv t.
Proof.
intros.
inversion H.
exists a.
split.
 exact H2.

 exact H5.
Qed.

Lemma IfRel:
  forall (tenv : tenv) (r : type) (t1 t2 t3 : term),
    Typed (If t1 t2 t3) tenv r ->
      Typed t1 tenv BoolT /\  Typed t2 tenv r /\ Typed t3 tenv r.
Proof.
intros.
inversion H.
tauto.
Qed.

