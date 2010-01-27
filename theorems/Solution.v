Require Import List.
Require Import String.

Require Import TypeSubst.
Require Import Constraint.
Require Import TypingRule.
Require Import ConstraintRule.

Definition TSolution tsubst T tenv t :=
  Typed (term_subst t tsubst) (tenv_subst tenv tsubst) T.

Definition CSolution tsubst T tenv Ts t S C := exists X,
  TypeConstraint t tenv Ts S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

