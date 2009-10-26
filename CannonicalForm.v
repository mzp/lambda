Require Import List.
Require Import String.
Require Import Lambda.

Lemma BoolCan :
  forall (v : term),
  value v /\ Some BoolT = typing v nil -> v = Bool true \/ v = Bool false.
Proof.
intro.
destruct v.
 simpl in |- *.
 intro; decompose [and] H.
 discriminate.

 simpl in |- *.
 intros; destruct b.
  left; reflexivity; right; reflexivity.

  right; reflexivity.

 simpl in |- *.
 case (typing v ((s, t) :: nil)).
  intros.
  decompose [and] H.
  discriminate.

  intros; decompose [and] H.
  discriminate.

 simpl in |- *.
 intro.
 decompose [and] H.
 contradiction .

 simpl in |- *.
 intro.
 decompose [and] H.
 contradiction .
Qed.

Lemma LambdaCan :
  forall (v : term) (ty1 ty2 : type),
  value v /\ Some (FunT ty1 ty2) = typing v nil ->
  exists x : string, exists body : term, v = Lambda x ty1 body.
Proof.
intros v ty1 ty2.
destruct v.
 simpl in |- *.
 intros; decompose [and] H; discriminate.

 simpl in |- *.
 intros; decompose [and] H; discriminate.

 simpl in |- *.
 case (typing v ((s, t) :: nil)).
  intros.
  inversion H.
  inversion H1.
  exists s.
  exists v.
  reflexivity.

  intro; decompose [and] H; discriminate.

 simpl in |- *; intro; decompose [and] H.
 contradiction .

 simpl in |- *; intro; decompose [and] H; contradiction .
Qed.
