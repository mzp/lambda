Require Import List.
Require Import String.
Require Import Typing.

Require Import Term.
Require Import TypeSubst.

Definition tconst := list (type * type).
Definition Unified (c : tconst) (t : tsubst) := forall S T U,
  In (S,T) c -> TypeSubst S U t /\ TypeSubst T U t.
Definition tvars := list string.

Definition FvTConst x c := forall S T,
  In (S,T) c -> FvT x S \/ FvT x T.

Definition FvTEnv x tenv := forall y T,
  TEnv.MapsTo y T tenv -> FvT x T.

Definition DisjointFV xs T := forall x,
  (FvT x T -> ~ In x xs) /\ (In x xs -> ~ FvT x T).

Definition Disjoint {A : Type} (xs ys : list A) := forall x,
  (In x xs -> ~ In x ys) /\ (In x ys -> ~ In x xs).

Lemma Disjoint_sym : forall A (xs ys : list A),
  Disjoint xs ys -> Disjoint ys xs.
Proof.
unfold Disjoint in |- *.
intros.
specialize (H x).
inversion H.
split; [ apply H1 | apply H0 ].
Qed.

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 :=
  ~ In x X1  /\ ~ In x X2 /\
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
    Disjoint X1 X2 -> DisjointFV X T1 -> DisjointFV X T2 ->
    X = x :: X1 ++ X2 ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 ->
    C = (T1,FunT T2 (VarT x)) :: C1 ++ C2 ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C3 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = X1 ++ X2 ++ X3 ->
    Disjoint X1 X2 -> Disjoint X2 X3 -> Disjoint X3 X1 ->
    C = (T1,BoolT) :: (T2,T3) :: C1 ++ C2 ++ C3 ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

Definition Solution tsubst T tenv t S C :=
  TypeConstraint t tenv S nil C -> Unified C tsubst /\ TypeSubst S T tsubst.
