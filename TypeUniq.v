Require Import Lambda.
Require Import List.
Require Import String.

Theorem type_uniq :
  forall (tenv : list (string * type)) (r1 r2 : type) (t : term),
    Some r1 = typing t tenv /\ Some r2 = typing t tenv ->
      r1 = r2.
Proof.
destruct t.
 induction tenv.
  simpl in |- *.
  intros; decompose [and] H; discriminate.

  simpl in IHtenv.
  simpl in |- *.
  destruct a.
  case (string_dec s s0).
   intros; decompose [and] H; inversion H0; inversion H1.
   reflexivity.

   intro.
   exact IHtenv.

 simpl in |- *.
 intros; decompose [and] H.
 inversion H0; inversion H1.
 reflexivity.

 simpl in |- *.
 case (typing t0 ((s, t) :: tenv)).
  intros.
  decompose [and] H.
  inversion H0; inversion H1.
  reflexivity.

  intro; decompose [and] H.
  discriminate.

 simpl in |- *.
 case (typing t1 tenv).
  intro; case t.
   intro; decompose [and] H.
   discriminate.

   case (typing t2 tenv).
    intros t0 t3.
    case (type_dec t3 t0).
     intros.
     inversion H.
     inversion H0.
     inversion H1.
     reflexivity.

     intros; decompose [and] H; discriminate.

    intros; decompose [and] H; discriminate.

  intros; decompose [and] H; discriminate.

 simpl in |- *.
 case (typing t1 tenv).
  intro; case t.
   case (typing t2 tenv).
    case (typing t3 tenv).
     intros t0 t4; case (type_dec t4 t0).
      intros.
      inversion H.
      inversion H0; inversion H1.
      reflexivity.

      intros; decompose [and] H; discriminate.

     intros; decompose [and] H; discriminate.

    intros; decompose [and] H; discriminate.

   intros; decompose [and] H; discriminate.

  intros; decompose [and] H; discriminate.
Qed.
