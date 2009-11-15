Require Import List.
Require Import String.

Require Import Term.
Require Import Alpha.
Require Import Typing.

Theorem alpha_preserve : forall t tenv x y T S,
  Typed t tenv T -> ~FV y t -> ~BV y t -> TEnv.MapsTo x S tenv ->
     Typed (alpha t x y) (TEnv.add y S tenv) T.
