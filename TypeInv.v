Require Import Lambda.
Require Import List.
Require Import String.

(* Inversion of the typing relation *)
Lemma VarRel :
  forall (tenv : list (string * type)) (x : string) (r : type),
  Some r = typing (Var x) tenv -> In (x,r) tenv.
Proof.
simpl in |- *.
intro tenv.
induction tenv.
 intros.
 simpl in H.
 discriminate H.

 intros x r.
 simpl in |- *.
 destruct a.
 case (string_dec x s).
  intros.
  left.
  rewrite e in |- *.
  inversion H.
  reflexivity.

  intros.
  right.
  apply IHtenv.
  assumption.
Qed.

Lemma LambdaRel :
  forall (x : string)
         (t r1 : type)
      	 (body : term)
         (tenv : list (string * type)),
  Some r1 = typing (Lambda x t body) tenv ->
      exists r2 : type,
      Some r2 = typing body ((x,t)::tenv) /\
      r1 = FunT t r2.
Proof.
simpl in |- *.
intros until tenv.
case (typing body ((x, t) :: tenv)).
 intros.
 inversion H.
 exists t0.
 split; reflexivity; reflexivity.

 intro.
 discriminate H.
Qed.

Lemma ApplyRel:
  forall (r : type)
      	 (f x : term)
         (tenv : list (string * type)),
    Some r = typing (Apply f x) tenv ->
      exists t : type,
      Some (FunT t r) = typing f tenv /\
      Some t = typing x tenv.
