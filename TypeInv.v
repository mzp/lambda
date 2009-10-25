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
Proof.
intros until tenv.
simpl in |- *.
case (typing f tenv).
 intro.
 case t.
  intro.
  discriminate H.

  case (typing x tenv).
   intros t0 t1.
   case (type_dec t1 t0).
    intros.
    exists t1.
    rewrite e in |- *.
    inversion H.
    split; reflexivity; reflexivity.

    intros; discriminate.

   intros; discriminate.

 intro; discriminate.
Qed.

Lemma TrueRel:
  forall (tenv : list (string * type)) (r : type),
  Some r = typing (Bool true) tenv -> r = BoolT.
Proof.
  intros until r.
  simpl in |- *.
  intro.
  inversion H.
  reflexivity.
Qed.

Lemma FalseRel:
  forall (tenv : list (string * type)) (r : type),
  Some r = typing (Bool false) tenv -> r = BoolT.
Proof.
  intros until r.
  simpl in |- *.
  intro.
  inversion H.
  reflexivity.
Qed.

Lemma IfRel:
  forall (tenv : list (string * type)) (r : type) (t1 t2 t3 : term),
  Some r = typing (If t1 t2 t3) tenv ->
  Some BoolT = typing t1 tenv /\  Some r = typing t2 tenv /\  Some r = typing t3 tenv.
Proof.
intros until t3.
simpl in |- *.
case (typing t1 tenv).
 intro; case t.
  case (typing t2 tenv).
   intro; case (typing t3 tenv).
    intro t4; case (type_dec t0 t4).
     intros.
     rewrite e in |- *.
     inversion H.
     rewrite e in |- *.
     split.
      reflexivity.

      split.
       reflexivity.

       reflexivity.

     intros.
     discriminate.

    intro; discriminate.

   intro; discriminate.

  intros; discriminate.

 intro; discriminate.
Qed.
