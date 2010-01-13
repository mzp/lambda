Require Import Util.
Require Import String.
Require Import Term.

Inductive FreeT : string -> type -> Prop :=
  | FVarT : forall x, FreeT x (VarT x)
  | FFunT : forall x T1 T2, FreeT x T1 \/ FreeT x T2 -> FreeT x (FunT T1 T2).

Inductive FreeTerm : string -> term -> Prop :=
    FLambda : forall x y T t,
      FreeT x T \/ FreeTerm x t -> FreeTerm x (Lambda y T t)
  | FApply  : forall x t1 t2,
      FreeTerm x t1 \/ FreeTerm x t2 -> FreeTerm x (Apply t1 t2)
  | FIf     : forall x t1 t2 t3,
      FreeTerm x t1 \/ FreeTerm x t2 \/ FreeTerm x t3 -> FreeTerm x (If t1 t2 t3).
