Require Import List.
Require Import String.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.

Definition Disjoint (tsubst : tsubst) tvars := forall x,
  Table.In x tsubst -> ~ Sets.In x tvars /\
  Sets.In x tvars   -> ~ Table.In x tsubst.

Definition Sub s1 tvars s2 := forall x (T : type),
  Table.MapsTo x T s1 -> ~ Sets.In x tvars -> Table.MapsTo x T s2 /\
  Table.MapsTo x T s1 ->   Sets.In x tvars -> ~ Table.In x s2.

Theorem completeness: forall t tenv S T X C tsubst1 tsubst2,
  TypeConstraint t tenv S X C ->
  TypeSubst.Solution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  Sub tsubst1 X tsubst2 ->
  Constraint.Solution tsubst2 T tenv t S C.

