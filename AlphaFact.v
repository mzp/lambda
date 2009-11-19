Require Import List.
Require Import String.

Require Import Term.
Require Import Alpha.
Require Import Typing.
Require Import Weaking.

Lemma weaking_FV:
  forall (t : term) (S T : type) (tenv : tenv) (s : string),
    ~ FV s t -> ~ BV s t -> Typed t tenv T -> Typed t (TEnv.add s S tenv) T.
Proof.
induction t
 (* Var *).
 intros.
 apply TVar.
 apply TEnv.add_2.
  unfold not in |- *; intro; apply H.
  rewrite H2 in |- *.
  apply FVVar.

  inversion H1.
  exact H3.

 (* Bool *)
 intros.
 inversion H1.
 apply TBool.

 (* Lambda *)
 intros.
 inversion H1.
 apply TLambda.
 apply permutation with (tenv1 := TEnv.add s0 S (TEnv.add s t tenv)).
  apply Equal_add_2.
  unfold not in |- *; intro; apply H0.
  rewrite H8 in |- *.
  apply BVLambda1.

  apply IHt.
   unfold not in |- *.
   intro.
   apply H.
   apply FVLambda.
    unfold not in |- *; intro; apply H0.
    rewrite H9 in |- *.
    apply BVLambda1.

    exact H8.

   unfold not in |- *; intro; apply H0.
   apply BVLambda2.
   exact H8.

   exact H7.

 (* If *)
 intros.
 inversion H1.
 apply TApply with (a := a).
  apply IHt1.
   unfold not in |- *; intro; apply H.
   apply FVApply.
   left; exact H8.

   unfold not in |- *; intro; apply H0.
   apply BVApply.
   left; exact H8.

   exact H4.

  apply IHt2.
   unfold not in |- *; intro; apply H.
   apply FVApply.
   right; exact H8.

   unfold not in |- *; intro; apply H0.
   apply BVApply.
   right; exact H8.

   exact H7.

 (* If *)
 intros.
 inversion H1.
 apply TIf.
  apply IHt1.
   unfold not in |- *; intro; apply H.
   apply FVIf.
   left; exact H10.

   unfold not in |- *; intro; apply H0.
   apply BVIf.
   left; exact H10.

   exact H5.

  apply IHt2.
   unfold not in |- *; intro; apply H.
   apply FVIf.
   right; left; exact H10.

   unfold not in |- *; intro; apply H0.
   apply BVIf.
   right; left; exact H10.

   exact H8.

  apply IHt3.
   unfold not in |- *; intro; apply H.
   apply FVIf.
   right; right; exact H10.

   unfold not in |- *; intro; apply H0.
   apply BVIf.
   right; right; exact H10.

   exact H9.
Qed.
(*
Theorem alpha_preserve : forall t tenv x y T S,
  Typed t tenv T -> ~FV y t -> ~BV y t -> TEnv.MapsTo x S tenv ->
     Typed (alpha t x y) (TEnv.add y S tenv) T.
Proof.
induction t.
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
   unfold not in |- *.
   unfold not in H0.
   intro.
   apply H0.
   rewrite H7 in |- *.
   apply FVVar.

   exact H4.

 intros.
 simpl in |- *.
 inversion H.
 apply TBool.

 intros.
 simpl in |- *.
 destruct (string_dec s x).
  inversion H.
  apply TLambda.

*)
