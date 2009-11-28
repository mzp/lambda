Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Constraint.
Require Import TypeSubst.

Theorem soundness : forall tenv t T S C tsubst,
  TypeConstraint t tenv S nil C ->
  Constraint.Solution tsubst T tenv t S C ->
  TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
pattern t, tenv, S, (nil:tvars), C in |- *.
apply TypeConstraint_ind.
