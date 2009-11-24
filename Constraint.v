Require Import List.
Require Import Term.
Require Import TypeSubst.

Definition constraints := list (type * type).
Definition Unified (c : constraints) (t : tsubst) := forall S T U,
  In (S,T) c -> TypeSubst S U t /\ TypeSubst T U t.
