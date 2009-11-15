(* simple typed lambda calculus *)
Require Import List.
Require Import String.

Require Import FSets.FMapWeakList.
Require Import FSets.FMapInterface.
Require Import FSets.FMapFacts.
Require Import Logic.DecidableType.

(* simple type *)
Inductive type : Set :=
    BoolT : type
  | FunT  : type -> type -> type.

Inductive term : Set :=
    Var     : string -> term
  | Bool    : bool   -> term
  | Lambda  : string -> type -> term -> term
  | Apply   : term  -> term -> term
  | If      : term -> term -> term -> term.

Fixpoint term_length (t : term) :=
  match t with
  |  Var _ | Bool _ =>
    1
  | Lambda _ _ body =>
    1 + term_length body
  | Apply t1 t2 =>
    1 + term_length t1 + term_length t2
  | If t1 t2 t3 =>
    1 + term_length t1 + term_length t2 + term_length t3
  end.

Inductive FV : string -> term -> Prop :=
  | FVVar    : forall s, FV s (Var s)
  | FVLambda : forall x y t T, x <> y -> FV x t -> FV x (Lambda y T t)
  | FVApply  : forall x t1 t2, FV x t1 \/ FV x t2 -> FV x (Apply t1 t2)
  | FVIf     : forall x t1 t2 t3, FV x t1 \/ FV x t2 \/ FV x t3 -> FV x (If t1 t2 t3).

Inductive BV : string -> term -> Prop :=
  | BVLambda1 : forall x T t, BV x (Lambda x T t)
  | BVLambda2 : forall x y T t, BV x t -> BV x (Lambda y T t)
  | BVApply   : forall x t1 t2, BV x t1 \/ BV x t2 -> BV x (Apply t1 t2)
  | BVIf      : forall x t1 t2 t3, BV x t1 \/ BV x t2 \/ BV x t3 -> BV x (If t1 t2 t3).
