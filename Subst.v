Require Import List.
Require Import String.

Require Import Lambda.

Lemma swap:
  forall (tenv1 tenv2 : tenv) (x : string) (r : type),
    TEnv.Equal tenv1 tenv2 ->
      TEnv.Equal (TEnv.add x r tenv1) (TEnv.add x r tenv2).
Proof.
intros.
eapply TEnvWF.Equal_mapsto_iff.
split.
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  inversion H1.
  rewrite H2 in |- *; rewrite H3 in |- *.
  apply TEnv.add_1.
  reflexivity.

  inversion H1.
  apply TEnv.add_2.
   exact H2.

   eapply TEnvWF.Equal_mapsto_iff in H.
   apply H.
   exact H3.

 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  inversion H1.
  rewrite H3 in |- *; rewrite H2 in |- *.
  apply TEnv.add_1.
  reflexivity.

  inversion H1.
  apply TEnv.add_2.
   exact H2.

   eapply TEnvWF.Equal_mapsto_iff.
    apply H.

    exact H3.
Qed.

Lemma add_add :
  forall (tenv : tenv) (x y : string) (r1 r2 : type),
    (x <> y -> TEnv.Equal (TEnv.add x r1 (TEnv.add y r2 tenv)) (TEnv.add y r2 (TEnv.add x r1 tenv)))  /\
    (x =  y -> TEnv.Equal (TEnv.add x r1 (TEnv.add y r2 tenv)) (TEnv.add x r1 tenv)).
Proof.
split.
 intros.
 eapply TEnvWF.Equal_mapsto_iff.
 split.
  intros.
  apply TEnvWF.add_mapsto_iff in H0.
  decompose [or] H0.
   inversion H1.
   rewrite H2 in |- *.
   rewrite H3 in |- *.
   rewrite H2 in H.
   apply TEnv.add_2.
    auto.

    apply TEnv.add_1.
    reflexivity.

   decompose [and] H1.
   apply TEnvWF.add_mapsto_iff in H3.
   decompose [or] H3.
    inversion H4.
    rewrite H5 in |- *; rewrite H6 in |- *.
    apply TEnv.add_1.
    reflexivity.

    decompose [and] H4.
    apply TEnv.add_2.
     exact H5.

     apply TEnv.add_2.
      exact H2.

      exact H6.

  intros.
  apply TEnvWF.add_mapsto_iff in H0.
  decompose [or] H0.
   inversion H1.
   rewrite H2 in |- *; rewrite H3 in |- *.
   rewrite H2 in H.
   apply TEnv.add_2.
    exact H.

    apply TEnv.add_1.
    reflexivity.

   inversion H1.
   apply TEnvWF.add_mapsto_iff in H3.
   decompose [or] H3.
    inversion H4.
    rewrite H6 in |- *.
    rewrite H5 in |- *.
    apply TEnv.add_1.
    reflexivity.

    decompose [and] H4.
    apply TEnv.add_2.
     exact H5.

     apply TEnv.add_2.
      exact H2.

      exact H6.

 intros.
 rewrite H in |- *.
 eapply TEnvWF.Equal_mapsto_iff.
 split.
  intros.
  apply TEnvWF.add_mapsto_iff in H0.
  decompose [or] H0.
   decompose [and] H1.
   rewrite H3 in |- *.
   rewrite H2 in |- *.
   apply TEnv.add_1.
   reflexivity.

   decompose [and] H1.
   apply TEnv.add_2.
    exact H2.

    apply TEnv.add_3 in H3.
     exact H3.

     exact H2.

  intros.
  apply TEnvWF.add_mapsto_iff in H0.
  decompose [or] H0.
   inversion H1.
   rewrite H2 in |- *.
   rewrite H3 in |- *.
   apply TEnv.add_1.
   reflexivity.

   decompose [and] H1.
   apply TEnv.add_2.
    exact H2.

    apply TEnv.add_2.
     exact H2.

     exact H3.
Qed.

Lemma permutation:
  forall (t : term) (tenv1 tenv2 : tenv) (r : type),
    TEnv.Equal tenv1 tenv2 ->
      Typed t tenv1 r -> Typed t tenv2 r.
Proof.
induction t.
 intros.
 inversion H0.
 apply TVar.
 eapply TEnvWF.Equal_mapsto_iff in H.
 apply H.
 exact H2.

 intros.
 inversion H0.
 apply TBool.

 intros.
 inversion H0.
 apply TLambda.
 apply swap with (x := s) (r := t) in H.
 apply IHt with (r := b) in H.
  exact H.

  exact H6.

 intros.
 inversion H0.
 apply TApply with (a := a).
  eapply IHt1 in H3.
   apply H3.

   exact H.

  eapply IHt2 in H6.
   apply H6.

   exact H.

 intros.
 inversion H0.
 apply TIf.
  eapply IHt1.
   apply H.

   exact H4.

  eapply IHt2.
   apply H.

   exact H7.

  eapply IHt3.
   apply H.

   exact H8.
Qed.

