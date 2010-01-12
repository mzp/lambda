Require Import List.
Require Import String.

Require Import Tables.
Require Import Term.

Definition tenv := table type.
Definition empty := Table.empty type.

Inductive Typed : term -> tenv -> type -> Prop :=
  | TVar    : forall tenv s T,
     Table.MapsTo s T tenv -> Typed (Var s) tenv T
  | TBool   : forall tenv b,
     Typed (Bool b) tenv BoolT
  | TLambda : forall tenv x S T t,
     Typed t (Table.add x T tenv) S -> Typed (Lambda x T t) tenv (FunT T S)
  | TApply  : forall tenv t1 t2 S T,
     Typed t1 tenv (FunT S T) -> Typed t2 tenv S ->
     Typed (Apply t1 t2) tenv T
  | TIf     : forall tenv t1 t2 t3 T,
     Typed t1 tenv BoolT -> Typed t2 tenv T -> Typed t3 tenv T ->
     Typed (If t1 t2 t3) tenv T.


