Require Import String.

Require Import Term.
Require Import Typing.

Definition ctx := tenv.
Module Ctx := TEnv.

Inductive TypeSubst : type -> type -> ctx -> Prop :=
  SVarT1 : forall ctx x T, Ctx.MapsTo x T ctx -> TypeSubst (VarT x) T ctx
| SVarT2 : forall ctx x, ~ Ctx.In x ctx -> TypeSubst (VarT x) (VarT x) ctx
| SBoolT : forall ctx    , TypeSubst BoolT BoolT ctx
| SFunT  : forall ctx T1 T2 S1 S2 ,
    TypeSubst T1 S1 ctx -> TypeSubst T2 S2 ctx -> TypeSubst (FunT T1 T2) (FunT S1 S2) ctx.

Definition TEnvSubst (tenv1 tenv2 : tenv) (ctx : ctx):= forall x T S,
  TEnv.MapsTo x T tenv1 -> TypeSubst T S ctx -> TEnv.MapsTo x S tenv2.

Inductive TermSubst : term -> term -> ctx -> Prop :=
   SVar  : forall ctx x, TermSubst (Var x) (Var x) ctx
 | SBool : forall ctx b, TermSubst (Bool b) (Bool b) ctx
 | SLambda : forall ctx x T S t s, TypeSubst T S ctx -> TermSubst t s ctx ->
              TermSubst (Lambda x T t) (Lambda x S s) ctx
 | SApply : forall ctx t1 t2 s1 s2,       TermSubst t1 s1 ctx -> TermSubst t2 s2 ctx ->
              TermSubst (Apply t1 t2) (Apply s1 s2) ctx
 | SIf    : forall ctx t1 t2 t3 s1 s2 s3, TermSubst t1 s1 ctx -> TermSubst t2 s2 ctx -> TermSubst t3 s3 ctx ->
              TermSubst (If t1 t2 t3) (If s1 s2 s3) ctx.

Lemma MapsTo_In : forall (A : Type) (ctx : TEnv.t A) x (T : A),
  TEnv.MapsTo x T ctx -> TEnv.In x ctx.
Proof.
intros.
unfold TEnv.In in |- *.
unfold TEnv.Raw.PX.In in |- *.
unfold TEnv.MapsTo in H.
exists T.
exact H.
Qed.

Lemma subst_uniq : forall ctx T S U,
  TypeSubst T S ctx -> TypeSubst T U ctx -> S = U.
Proof.
induction T.
 intros.
 inversion H; inversion H0.
  apply TEnvWF.MapsTo_fun with (m := ctx0) (x := s).
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

Lemma subst_add : forall ctx tenv1 tenv2 x S T,
   TEnvSubst tenv1 tenv2 ctx ->
   TypeSubst S T ctx ->
   TEnvSubst (TEnv.add x S tenv1) (TEnv.add x T tenv2) ctx.
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
  apply subst_uniq with (T := S) (ctx := ctx0).
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

Lemma subst_exists : forall T ctx,
   exists S, TypeSubst T S ctx.
Proof.
intros.
induction T.
 destruct (TEnvWF.In_dec ctx0 s).
  inversion i.
  exists x.
  apply SVarT1.
  unfold TEnv.MapsTo in |- *.
  exact H.

  exists (VarT s).
  apply SVarT2.
  exact n.

 exists BoolT.
 apply SBoolT.

 decompose [ex] IHT1.
 decompose [ex] IHT2.
 exists (FunT x x0).
 apply SFunT.
  exact H.

  exact H0.
Qed.

Theorem subst_preserve : forall ctx s tenv2 S t tenv1 T,
  Typed t tenv1 T -> (TEnvSubst tenv1 tenv2 ctx -> TermSubst t s ctx -> TypeSubst T S ctx ->
  Typed s tenv2 S).
Proof.
intros until T.
intro.
generalize ctx0, s, tenv2, S.
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
  apply subst_uniq with (ctx := ctx1) (T := a).
   exact H10.

   exact H14.

  rewrite H18 in |- *.
  apply TLambda.
  apply H1 with (ctx0 := ctx1).
   apply subst_add.
    exact H2.

    exact H14.

   exact H11.

   exact H17.

 intros.
 inversion H5.
 assert (exists T : type, TypeSubst a T ctx1).
  apply subst_exists.

  decompose [ex] H13.
  apply TApply with (a := x).
   apply H1 with (ctx0 := ctx1).
    exact H4.

    exact H9.

    apply SFunT.
     exact H14.

     exact H6.

   apply H3 with (ctx0 := ctx1).
    exact H4.

    exact H12.

    exact H14.

 intros.
 inversion H7.
 apply TIf.
  apply H1 with (ctx0 := ctx1).
   exact H6.

   exact H12.

   apply SBoolT.

  apply H3 with (ctx0 := ctx1).
   exact H6.

   exact H15.

   exact H8.

  apply H5 with (ctx0 := ctx1).
   exact H6.

   exact H16.

   exact H8.

 exact H.
Qed.
