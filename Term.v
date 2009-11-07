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

