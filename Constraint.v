Require Import List.
Require Import Sets.Ensembles.
Require Import String.

Require Import Typing.
Require Import Term.
Require Import TypeSubst.


Definition tconst := Ensemble (type * type).
Definition InConst x xs     := Ensembles.In (type*type) xs x.
Definition UnionConst xs ys := Ensembles.Union (type*type) xs ys.
Definition AddConst x xs    := Ensembles.Add (type*type) xs x.

Definition Unified (c : tconst) (t : tsubst) := forall S T,
  InConst (S,T) c -> exists U, TypeSubst S U t /\ TypeSubst T U t.

Definition tvars := Ensemble string.
Definition InTVars x xs := Ensembles.In string xs x.
Definition UnionTVars xs ys := Ensembles.Union string xs ys.
Definition AddTVars x xs    := Ensembles.Add string xs x.
Definition DisjointTVars xs ys := Ensembles.Disjoint string xs ys.


Definition FvTConst x c := forall S T,
  InConst (S,T) c -> FvT x S \/ FvT x T.

Definition FvTEnv x tenv := forall y T,
  TEnv.MapsTo y T tenv -> FvT x T.

Definition DisjointFV xs T := forall x,
  (FvT x T -> ~ InTVars x xs) /\ (InTVars x xs -> ~ FvT x T).

(*Definition Disjoint {A : Type} (xs ys : list A) := forall x,
  (In x xs -> ~ In x ys) /\ (In x ys -> ~ In x xs).*)

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 :=
  ~ InTVars x X1  /\ ~ InTVars x X2 /\
  ~ FvT x T1 /\ ~ FvT x T2 /\
  ~ FvTConst x C1 /\ ~ FvTConst x C2 /\
  ~ FvTEnv x tenv /\
  ~ FvTt x t1 /\ ~ FvTt x t2.

Inductive TypeConstraint : term -> tenv -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv T X C,
    TEnv.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv T X C
| CTLambda : forall x T1 T2 t tenv X C,
    TypeConstraint t (TEnv.add x T1 tenv) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv (FunT T1 T2) X C
| CTBool : forall b tenv X C,
    TypeConstraint (Bool b) tenv BoolT X C
| CTApply : forall x t1 t2 T1 T2 tenv X1 X2 X C1 C2 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    DisjointTVars X1 X2 -> DisjointFV X2 T1 -> DisjointFV X1 T2 ->
    X = AddTVars x (UnionTVars X1 X2) ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 ->
    C = AddConst (T1,FunT T2 (VarT x)) (UnionConst C1 C2) ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C3 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = UnionTVars X1 (UnionTVars X2 X3) ->
    DisjointTVars X1 X2 -> DisjointTVars X2 X3 -> DisjointTVars X3 X1 ->
    C = AddConst (T1,BoolT) (AddConst (T2,T3) (UnionConst C1 (UnionConst C2 C3))) ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

Definition Solution tsubst T tenv t S C := exists X,
  TypeConstraint t tenv S X C /\ Unified C tsubst /\ TypeSubst S T tsubst.

Lemma Disjoint_union : forall A (X Y Z: Ensemble A),
  Disjoint A (Union A X Z) Y ->
  Disjoint A X Y.
Proof.
intros.
inversion H.
apply Disjoint_intro.
intro.
specialize (H0 x).
intro.
apply H0.
inversion H1.
apply Intersection_intro.
 apply Union_introl.
 trivial.

 trivial.
Qed.

Lemma Disjoint_add : forall A (X Y : Ensemble A) x,
  Disjoint A (Add A X x) Y -> Disjoint A X Y.
Proof.
unfold Add in |- *.
intros.
apply Disjoint_union with (Z := Singleton A x).
trivial.
Qed.

Lemma Disjoint_sym : forall A (X Y : Ensemble A),
  Disjoint A X Y -> Disjoint A Y X.
Proof.
intros.
inversion H.
apply Disjoint_intro.
intros.
specialize (H0 x).
intro.
apply H0.
inversion H1.
apply Intersection_intro.
 trivial.

 trivial.
Qed.

Lemma Union_sym : forall A (X Y : Ensemble A),
  Union A X Y = Union A Y X.
Proof.
intros.
apply Extensionality_Ensembles.
unfold Same_set in |- *.
unfold Included in |- *.
split; intros.
 inversion H.
  apply Union_intror.
  trivial.

  apply Union_introl.
  trivial.

 inversion H.
  apply Union_intror.
  trivial.

  apply Union_introl.
  trivial.
Qed.

Lemma Unified_Union : forall C1 C2 tsubst,
  Unified (UnionConst C1 C2) tsubst -> Unified C1 tsubst.
Proof.
unfold Unified in |- *.
unfold InConst in |- *.
intros.
apply H.
unfold UnionConst in |- *.
apply Union_introl.
trivial.
Qed.

Lemma Unified_Add : forall c C tsubst,
  Unified (AddConst c C) tsubst -> Unified C tsubst.
Proof.
unfold AddConst in |- *.
unfold Add in |- *.
intros.
apply Unified_Union with (C2 := Singleton (type * type) c).
trivial.
Qed.


Lemma unfold_tsubst : forall T S tsubst tenv t C,
  Solution tsubst T tenv t S C -> TypeSubst S T tsubst.
Proof.
intros.
unfold Solution in H.
inversion H.
inversion H0.
inversion H2.
trivial.
Qed.

Lemma unfold_unified : forall T S tsubst tenv t C,
  Solution tsubst T tenv t S C -> Unified C tsubst.
Proof.
intros.
unfold Solution in H.
inversion H.
inversion H0.
inversion H2.
trivial.
Qed.

Lemma unified_add : forall S T C tsubst,
  Unified (AddConst (T,S) C) tsubst ->
  exists U, TypeSubst T U tsubst /\ TypeSubst S U tsubst.
Proof.
intros.
unfold Unified in H.
specialize (H T S).
apply H.
unfold InConst in |- *; unfold AddConst in |- *.
unfold Add in |- *.
apply Union_intror.
apply In_singleton.
Qed.

(*Lemma Unified_equal : forall T1 T2 C tsubst,
  Unified C tsubst ->
  InConst (T1,T2) C ->
  exists S, TypeSubst T1 S tsubst /\ TypeSubst T2 S tsubst.*)
