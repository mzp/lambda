Require Import String.

Require Import Term.
Require Import Typing.

Definition tsubst := tenv.
Module Tsubst := TEnv.

Inductive TypeSubst : type -> type -> tsubst -> Prop :=
  SVarT1 : forall tsubst x T, Tsubst.MapsTo x T tsubst -> TypeSubst (VarT x) T tsubst
| SVarT2 : forall tsubst x, ~ Tsubst.In x tsubst -> TypeSubst (VarT x) (VarT x) tsubst
| SBoolT : forall tsubst    , TypeSubst BoolT BoolT tsubst
| SFunT  : forall tsubst T1 T2 S1 S2 ,
    TypeSubst T1 S1 tsubst -> TypeSubst T2 S2 tsubst -> TypeSubst (FunT T1 T2) (FunT S1 S2) tsubst.

Definition TEnvSubst (tenv1 tenv2 : tenv) (tsubst : tsubst):= forall x T S,
  TEnv.MapsTo x T tenv1 -> TypeSubst T S tsubst -> TEnv.MapsTo x S tenv2.

Inductive TermSubst : term -> term -> tsubst -> Prop :=
   SVar    : forall tsubst x, TermSubst (Var x) (Var x) tsubst
 | SBool   : forall tsubst b, TermSubst (Bool b) (Bool b) tsubst
 | SLambda : forall tsubst x T S t s,
               TypeSubst T S tsubst ->
               TermSubst t s tsubst ->
               TermSubst (Lambda x T t) (Lambda x S s) tsubst
 | SApply  : forall tsubst t1 t2 s1 s2,
               TermSubst t1 s1 tsubst ->
               TermSubst t2 s2 tsubst ->
               TermSubst (Apply t1 t2) (Apply s1 s2) tsubst
 | SIf     : forall tsubst t1 t2 t3 s1 s2 s3,
               TermSubst t1 s1 tsubst ->
               TermSubst t2 s2 tsubst ->
               TermSubst t3 s3 tsubst ->
               TermSubst (If t1 t2 t3) (If s1 s2 s3) tsubst.

Definition Solution tsubst T tenv t := forall tenv' s,
  TEnvSubst tenv tenv' tsubst -> TermSubst t s tsubst ->
  Typed s tenv' T.

Lemma MapsTo_In : forall (A : Type) (tsubst : TEnv.t A) x (T : A),
  TEnv.MapsTo x T tsubst -> TEnv.In x tsubst.
Proof.
intros.
unfold TEnv.In in |- *.
unfold TEnv.Raw.PX.In in |- *.
unfold TEnv.MapsTo in H.
exists T.
exact H.
Qed.

Lemma subst_uniq : forall tsubst T S U,
  TypeSubst T S tsubst -> TypeSubst T U tsubst -> S = U.
Proof.
induction T.
 intros.
 inversion H; inversion H0.
  apply TEnvWF.MapsTo_fun with (m := tsubst0) (x := s).
   exact H2.

   exact H6.

  apply MapsTo_In in H2.
  contradiction .

  apply MapsTo_In in H6.
  contradiction .

  reflexivity.

 intros.
 inversion H; inversion H0.
 reflexivity.

 intros.
 inversion H; inversion H0.
 assert (S1 = S0).
  apply IHT1.
   exact H3.

   exact H9.

  assert (S2 = S3).
   apply IHT2.
    exact H6.

    exact H12.

   rewrite H13 in |- *; rewrite H14 in |- *.
   reflexivity.
Qed.

Lemma subst_add : forall tsubst tenv1 tenv2 x S T,
   TEnvSubst tenv1 tenv2 tsubst ->
   TypeSubst S T tsubst ->
   TEnvSubst (TEnv.add x S tenv1) (TEnv.add x T tenv2) tsubst.
Proof.
intros.
unfold TEnvSubst in |- *.
intros.
apply TEnvWF.add_mapsto_iff in H1.
inversion H1.
 inversion H3.
 rewrite <- H5 in H2.
 rewrite <- H4 in |- *.
 assert (S0 = T).
  apply subst_uniq with (T := S) (tsubst := tsubst0).
   exact H2.

   exact H0.

  rewrite H6 in |- *.
  apply TEnv.add_1.
  reflexivity.

 inversion H3.
 apply TEnv.add_2.
  exact H4.

  unfold TEnvSubst in H.
  apply H with (T := T0).
   exact H5.

   exact H2.
Qed.

Lemma subst_exists : forall T tsubst,
   exists S, TypeSubst T S tsubst.
Proof.
intros.
induction T.
 destruct (TEnvWF.In_dec tsubst0 s).
  inversion i.
  exists x.
  apply SVarT1.
  unfold TEnv.MapsTo in |- *.
  trivial.

  exists (VarT s).
  apply SVarT2.
  trivial.

 exists BoolT.
 apply SBoolT.

 decompose [ex] IHT1.
 decompose [ex] IHT2.
 exists (FunT x x0).
 apply SFunT.
  trivial.

  trivial.
Qed.


Theorem subst_preserve : forall tsubst s tenv2 S t tenv1 T,
  Typed t tenv1 T -> (TEnvSubst tenv1 tenv2 tsubst -> TermSubst t s tsubst -> TypeSubst T S tsubst ->
  Typed s tenv2 S).
Proof.
intros until T.
intro.
generalize tsubst0, s, tenv2, S.
pattern t, tenv1, T in |- *.
apply Typed_ind.
 intros.
 inversion H2.
 apply TVar.
 unfold TEnvSubst in H1.
 apply H1 with (T := ty).
  exact H0.

  exact H3.

 intros.
 inversion H1.
 inversion H2.
 apply TBool.

 intros.
 inversion H3.
 inversion H4.
 assert (S1 = S2).
  apply subst_uniq with (tsubst := tsubst1) (T := a).
   exact H10.

   exact H14.

  rewrite H18 in |- *.
  apply TLambda.
  apply H1 with (tsubst0 := tsubst1).
   apply subst_add.
    exact H2.

    exact H14.

   exact H11.

   exact H17.

 intros.
 inversion H5.
 assert (exists T : type, TypeSubst a T tsubst1).
  apply subst_exists.

  decompose [ex] H13.
  apply TApply with (a := x).
   apply H1 with (tsubst0 := tsubst1).
    exact H4.

    exact H9.

    apply SFunT.
     exact H14.

     exact H6.

   apply H3 with (tsubst0 := tsubst1).
    exact H4.

    exact H12.

    exact H14.

 intros.
 inversion H7.
 apply TIf.
  apply H1 with (tsubst0 := tsubst1).
   exact H6.

   exact H12.

   apply SBoolT.

  apply H3 with (tsubst0 := tsubst1).
   exact H6.

   exact H15.

   exact H8.

  apply H5 with (tsubst0 := tsubst1).
   exact H6.

   exact H16.

   exact H8.

 exact H.
Qed.


