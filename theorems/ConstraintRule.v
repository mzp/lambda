Require Import List.
Require Import String.

Require Import Tables.
Require Import Term.
Require Import TVar.
Require Import TVars.
Require Import Constraint.
Require Import TypingRule.

Definition FreeE x tenv := exists y, exists T,
  Table.MapsTo y T tenv /\ FreeT x T.

Definition FreeTs x Ts := exists T,
  List.In T Ts /\ FreeT x T.

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv ts t1 t2 :=
  ~ TVars.In x X1  /\ ~ TVars.In x X2 /\
  ~ FreeT x T1     /\ ~ FreeT x T2    /\
  ~ FreeC x C1     /\ ~ FreeC x C2    /\
  ~ FreeE x tenv   /\ ~ FreeTs x ts   /\
  ~ FreeTerm x t1  /\ ~ FreeTerm x t2.

Definition DisjointT    := DisjointBy FreeT.
Definition DisjointTerm := DisjointBy FreeTerm.
Definition DisjointC    := DisjointBy FreeC.

Definition CTApplyDisjoint t1 t2 T1 T2 X1 X2 C1 C2 :=
    TVars.Disjoint X1 X2 /\
    DisjointT X2 T1      /\ DisjointT X1 T2    /\
    DisjointTerm X1 t2   /\ DisjointTerm X2 t1 /\
    DisjointC X1 C2      /\ DisjointC X2 C1.

Definition CTIfDIsjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3:=
    TVars.Disjoint X1 X2 /\ TVars.Disjoint X2 X3 /\ TVars.Disjoint X3 X1 /\
    DisjointTerm X1 t2 /\ DisjointTerm X1 t3 /\
    DisjointTerm X2 t1 /\ DisjointTerm X2 t3 /\
    DisjointTerm X3 t1 /\ DisjointTerm X3 t2 /\
    DisjointC X1 C2 /\ DisjointC X1 C3 /\
    DisjointC X2 C1 /\ DisjointC X2 C3 /\
    DisjointC X3 C1 /\ DisjointC X3 C2 /\
    DisjointT X1 T2 /\ DisjointT X1 T3 /\
    DisjointT X2 T1 /\ DisjointT X2 T3 /\
    DisjointT X3 T1 /\ DisjointT X3 T2.

Inductive TypeConstraint : term -> tenv -> list type -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv Ts T,
    Table.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv Ts T TVars.empty TConst.empty
| CTLambda : forall x T1 T2 t tenv Ts X C,
    TypeConstraint t (Table.add x T1 tenv) (T1::Ts) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv Ts (FunT T1 T2) X C
| CTBool : forall b tenv Ts,
    TypeConstraint (Bool b) tenv Ts BoolT TVars.empty TConst.empty
| CTApply : forall x t1 t2 T1 T2 tenv Ts X X1 X2 C1 C2 C,
    TypeConstraint t1 tenv Ts T1 X1 C1 ->
    TypeConstraint t2 tenv Ts T2 X2 C2 ->
    CTApplyDisjoint t1 t2 T1 T2 X1 X2 C1 C2 ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv Ts t1 t2 ->
    C = TConst.add (T1,FunT T2 (VarT x)) (TConst.union C1 C2) ->
    X = TVars.add x (TVars.union X1 X2) ->
    TypeConstraint (Apply t1 t2) tenv Ts (VarT x) X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv Ts X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv Ts T1 X1 C1 ->
    TypeConstraint t2 tenv Ts T2 X2 C2 ->
    TypeConstraint t3 tenv Ts T3 X3 C3 ->
    CTIfDIsjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3 ->
    C = TConst.add (T1,BoolT) (TConst.add (T2,T3) (TConst.union C1 (TConst.union C2 C3))) ->
    X = TVars.union X1 (TVars.union X2 X3) ->
    TypeConstraint (If t1 t2 t3) tenv Ts T2 X C.
