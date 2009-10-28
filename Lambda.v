(* simple typed lambda calculus *)
Require Import Arith.EqNat.
Require Import Arith.
Require Import Recdef.
Require Import List.
Require Import String.
Require Import Bool.DecBool.

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

(* equality *)
Definition type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(* Prop *)
Inductive Value  : term -> Prop :=
  | ValVar    : forall s : string, Value (Var s)
  | ValBool   : forall b : bool,   Value (Bool b)
  | ValLambda : forall (x : string) (ty : type) (body : term), Value (Lambda x ty body).

Inductive Reducible : term -> Prop :=
  | RAppLeft  : forall t1 t2 : term, Reducible t1 -> Reducible (Apply t1 t2)
  | RAppRight : forall t1 t2 : term, Reducible t2 -> Reducible (Apply t1 t2)
  | RLambda   : forall (x : string) (ty : type) (body arg : term), Reducible (Apply (Lambda x ty body) arg)
  | RIfCond   : forall (t1 t2 t3 : term), Reducible t1 -> Reducible (If t1 t2 t3)
  | RIf       : forall (b : bool) (t1 t2 : term), Reducible (If (Bool b) t1 t2).

Definition tenv := list (string * type).

Fixpoint assoc {A : Type} (x : string) (xs : list (string * A)) :=
  match xs with
  | nil =>
      None
  | (key, v) :: ys =>
      if string_dec x key then
        Some v
       else
      	assoc x ys
  end.

Inductive Typed : term -> tenv -> type -> Prop :=
  | TVar    : forall (tenv : tenv) (s : string) (ty : type), Some ty = assoc s tenv -> Typed (Var s) tenv ty
  | TBool   : forall (tenv : tenv) (b : bool) , Typed (Bool b) tenv BoolT
  | TLambda : forall (tenv : tenv) (x : string)      (a b : type) (body : term), Typed body ((x,a)::tenv) b -> Typed (Lambda x a body) tenv (FunT a b)
  | TApply  : forall (tenv : tenv) (t1 t2 : term)    (a b : type), Typed t1 tenv (FunT a b) -> Typed t2 tenv a -> Typed (Apply t1 t2) tenv b
  | TIf     : forall (tenv : tenv) (t1 t2 t3 : term) (ty : type), Typed t1 tenv BoolT -> Typed t2 tenv ty -> Typed t3 tenv ty -> Typed (If t1 t2 t3) tenv ty.


(* obsolute *)
Definition value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      True
  | Apply _ _  | If _ _ _ =>
      False
  end.
