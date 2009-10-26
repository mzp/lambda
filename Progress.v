Require Import List.
Require Import String.

Require Import Lambda.
Require Import TypeInv.
Require Import CannonicalForm.

Definition WellTyped (t : term) : Prop :=
  exists r : type, Some r = typing t nil.

Theorem Progress :
  forall (t : term),
    WellTyped t -> value t \/ exists t1 : term, eval t = Some t1.
Proof.
unfold WellTyped in |- *.
induction t.
 intro; left; simpl in |- *; tauto.

 intro; left; simpl in |- *; tauto.

 intro; left; simpl in |- *; tauto.

 intro.
 decompose [ex] H.
 apply ApplyRel in H0.
 decompose [ex] H0.
 decompose [and] H1.
 right.
 generalize H2.
 elim IHt1.
  destruct t1.
   simpl in |- *.
   intros; discriminate.

   simpl in |- *; intros; discriminate.

   intros.
   simpl in |- *.
   case (eval t2).
    intro.
    exists (Apply (Lambda s t t1) t0).
    reflexivity.

    exists (subst t1 s t2).
    reflexivity.

   simpl in |- *.
   intro; contradiction .

   simpl in |- *; intro; contradiction .

  simpl in |- *.
  case (eval t1).
   intros.
   exists (Apply t t2).
   reflexivity.

   intro.
   decompose [ex] H4.
   discriminate.

  exists (FunT x0 x).
  exact H2.

 intro.
 right.
 decompose [ex] H.
 apply IfRel in H0.
 inversion H0.
 inversion H2.
 simpl in |- *.
 generalize H1.
 destruct t1.
  simpl in |- *; intro; discriminate.

  intro; case b.
   exists t2.
   reflexivity.

   exists t3; reflexivity.

  simpl in |- *.
  case (typing t1 ((s, t) :: nil)).
   intro.
   intro.
   discriminate.

   intro; discriminate.

  elim IHt1.
   simpl in |- *; intro; contradiction .

   intro.
   intro.
   decompose [ex] H5.
   rewrite H7 in |- *.
   exists (If x0 t2 t3).
   reflexivity.

   rewrite <- H1 in |- *.
   exists BoolT.
   reflexivity.

  elim IHt1.
   simpl in |- *; intro; contradiction .

   intros.
   decompose [ex] H5.
   rewrite H7 in |- *.
   exists (If x0 t2 t3); reflexivity.

   exists BoolT.
   exact H1.
Qed.

