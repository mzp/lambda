Require Import List.
Require Import String.

Require Import Term.
Require Import TermFact.
Require Import Alpha.
Require Import Typing.
Require Import TypingFact.

Theorem alpha_fv : forall t x y,
  x <> y -> ~ FV x (alpha t x y).
Proof.
induction t.
 intros.
 simpl in |- *.
 destruct (string_dec s x).
  intro.
  apply H.
  inversion H0.
  reflexivity.

  intro.
  apply n.
  inversion H0.
  reflexivity.

 intros.
 simpl in |- *.
 intro.
 inversion H0.

 intros.
 simpl in |- *.
 destruct (string_dec s x).
  rewrite e in |- *.
  intro.
  inversion H0.
  tauto.

  intro.
  inversion H0.
  generalize H6.
  fold not in |- *.
  apply IHt.
  exact H.

 intros.
 simpl in |- *.
 intro.
 inversion H0.
 inversion H3.
  generalize H5.
  apply IHt1.
  exact H.

  generalize H5.
  apply IHt2.
  exact H.

 simpl in |- *.
 intros.
 intro.
 inversion H0.
 inversion H3.
  generalize H6.
  apply IHt1.
  exact H.

  inversion H6.
   generalize H7.
   apply IHt2.
   exact H.

   generalize H7.
   apply IHt3.
   exact H.
Qed.

Theorem alpha_preserve : forall t tenv x y T S,
  Typed t tenv T -> ~FV y t -> ~BV y t -> TEnv.MapsTo x S tenv ->
     Typed (alpha t x y) (TEnv.add y S tenv) T.
Proof.
induction t.
 (* Var *)
 intros.
 simpl in |- *.
 destruct (string_dec s x).
  inversion H.
  apply TEnvWF.MapsTo_fun with (e := T) in H2.
   rewrite <- H2 in |- *.
   apply TVar.
   apply TEnv.add_1.
   reflexivity.

   rewrite <- e in |- *.
   exact H4.

  apply TVar.
  inversion H.
  apply TEnv.add_2.
   intro; apply H0.
   rewrite H7 in |- *.
   apply FVVar.

   exact H4.

 (* Bool *)
 intros.
 simpl in |- *.
 inversion H.
 apply TBool.

 (* Lambda *)
 intros.
 simpl in |- *.
 destruct (string_dec s x).
  inversion H.
  apply TLambda.
  apply permutation with (tenv1 := TEnv.add y S (TEnv.add s t tenv)).
   apply Equal_add_2.
   intro; apply H1.
   rewrite H9 in |- *.
   apply BVLambda1.

   apply Typed_add_intro.
    intro.
    apply H0.
    apply FVLambda.
     intro; apply H1.
     rewrite H10 in |- *.
     apply BVLambda1.

     exact H9.

    intro; apply H1.
    apply BVLambda2.
    exact H9.

    apply H8.

  inversion H.
  apply TLambda.
  apply permutation with (tenv1 := TEnv.add y S (TEnv.add s t tenv)).
   apply Equal_add_2.
   intro.
   apply H1.
   rewrite H9 in |- *.
   apply BVLambda1.

   apply IHt.
    exact H8.

    intro.
    apply H0.
    apply FVLambda.
     intro; apply H1.
     rewrite H10 in |- *.
     apply BVLambda1.

     exact H9.

    intro.
    apply H1.
    apply BVLambda2.
    exact H9.

    apply TEnv.add_2.
     exact n.

     exact H2.

 (* Apply *)
 intros.
 inversion H.
 simpl in |- *.
 apply TApply with (a := a).
  apply IHt1.
   exact H5.

   intro; apply H0.
   apply FVApply.
   left; exact H9.

   intro; apply H1.
   apply BVApply.
   left; exact H9.

   exact H2.

  apply IHt2.
   exact H8.

   intro; apply H0.
   apply FVApply.
   right; exact H9.

   intro; apply H1.
   apply BVApply.
   right; exact H9.

   exact H2.

 (* If *)
 intros.
 simpl in |- *.
 inversion H.
 apply TIf.
  apply IHt1.
   exact H6.

   intro; apply H0.
   apply FVIf.
   left; exact H11.

   intro; apply H1.
   apply BVIf.
   left; exact H11.

   exact H2.

  apply IHt2.
   exact H9.

   intro; apply H0.
   apply FVIf.
   right; left; exact H11.

   intro; apply H1.
   apply BVIf.
   right; left; exact H11.

   exact H2.

  apply IHt3.
   exact H10.

   intro; apply H0.
   apply FVIf.
   right; right; exact H11.

   intro; apply H1.
   apply BVIf.
   right; right; exact H11.

   exact H2.
Qed.

Lemma alpha_id: forall t x,
  alpha t x x = t.
Proof.
induction t.
 intro.
 simpl in |- *.
 destruct (string_dec s x).
  rewrite e in |- *.
  reflexivity.

  reflexivity.

 intro.
 simpl in |- *.
 reflexivity.

 intro.
 simpl in |- *.
 destruct (string_dec s x).
  reflexivity.

  rewrite IHt in |- *.
  reflexivity.

 intro.
 simpl in |- *.
 rewrite IHt1,  IHt2 in |- *.
 reflexivity.

 intro.
 simpl in |- *.
 rewrite IHt1,  IHt2,  IHt3 in |- *.
 reflexivity.
Qed.
