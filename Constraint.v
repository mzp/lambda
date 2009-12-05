Require Import List.
Require Import Ensembles.
Require Import String.

Require Import Typing.
Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import TypeSubst.

Definition tconst := set (type * type).
Definition tvars := set string.

Definition Unified (c : tconst) (t : tsubst) := forall S T,
  In (S,T) c -> type_subst S t = type_subst T t.

Definition FvTConst x c := forall S T,
  In (S,T) c -> FvT x S \/ FvT x T.

Definition FvTable x tenv := forall y T,
  Table.MapsTo y T tenv -> FvT x T.

Definition DisjointFV xs T := forall x,
  (FvT x T -> ~ In x xs) /\ (In x xs -> ~ FvT x T).

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 :=
  ~ In x X1  /\ ~ In x X2 /\
  ~ FvT x T1 /\ ~ FvT x T2 /\
  ~ FvTConst x C1 /\ ~ FvTConst x C2 /\
  ~ FvTable x tenv /\
  ~ FvTt x t1 /\ ~ FvTt x t2.

Inductive TypeConstraint : term -> tenv -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv T X C,
    Table.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv T X C
| CTLambda : forall x T1 T2 t tenv X C,
    TypeConstraint t (Table.add x T1 tenv) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv (FunT T1 T2) X C
| CTBool : forall b tenv X C,
    TypeConstraint (Bool b) tenv BoolT X C
| CTApply : forall x t1 t2 T1 T2 tenv X1 X2 X C1 C2 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    Disjoint X1 X2 -> DisjointFV X2 T1 -> DisjointFV X1 T2 ->
    X = Add x (Union X1 X2) ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 ->
    C = Add (T1,FunT T2 (VarT x)) (Union C1 C2) ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C3 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = Union X1 (Union X2 X3) ->
    Disjoint X1 X2 -> Disjoint X2 X3 -> Disjoint X3 X1 ->
    C = Add (T1,BoolT) (Add (T2,T3) (Union C1 (Union C2 C3))) ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

Definition Solution tsubst T tenv t S C := exists X,
  TypeConstraint t tenv S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

Lemma Unified_Union : forall C1 C2 tsubst,
  Unified (Union C1 C2) tsubst -> Unified C1 tsubst.
Proof.
unfold Unified in |- *.
unfold In in |- *.
intros.
apply H.
unfold Union in |- *.
apply Union_introl.
trivial.
Qed.

Lemma Unified_Add : forall c C tsubst,
  Unified (Add c C) tsubst -> Unified C tsubst.
Proof.
unfold Add in |- *.
intros.
apply Unified_Union with (C2 := Singleton (type * type) c).
trivial.
Qed.
