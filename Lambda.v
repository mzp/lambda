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

(* equality *)
Definition type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(* bound *)
Inductive NotFV : string -> term -> Prop :=
  | BLambda : forall (x : string) (T : type) (body : term), NotFV x (Lambda x T body)
  | BApply  : forall (x : string) (t1 t2 : term)          , NotFV x t1 -> NotFV x t2 -> NotFV x (Apply t1 t2)
  | BIf     : forall (x : string) (t1 t2 t3 : term)       , NotFV x t1 -> NotFV x t2 -> NotFV x t3 -> NotFV x (If t1 t2 t3).

(* subst *)
Inductive Subst : term -> term -> string -> term -> Prop :=
  | SVar1    : forall (s x : string) (t : term),
      x = s  -> Subst (Var x) t s t
  | SVar2    : forall (s x : string) (t : term),
      x <> s -> Subst (Var x) (Var x) s t
  | SBool    : forall (s : string) (b : bool) (t : term),
      Subst (Bool b) (Bool b) s t
  | SLambda1 : forall (x s : string) (body1 body2 t : term) (ty : type),
      x <> s -> NotFV x t -> Subst body1 body2 s t ->
      	Subst (Lambda x ty body1) (Lambda x ty body2) s t
  | SLambda2 : forall (x s : string) (body t : term) (ty : type),
      x = s  -> Subst (Lambda x ty body) (Lambda x ty body) s t
  | SApply   : forall (t1 t2 s1 s2 t : term) (x : string),
      Subst t1 s1 x t -> Subst t2 s2 x t -> Subst (Apply t1 t2) (Apply s1 s2) x t
  | SIf      : forall (t1 t2 t3 s1 s2 s3 t : term) (x : string),
      Subst t1 s1 x t -> Subst t2 s2 x t -> Subst t3 s3 x t ->
      	Subst (If t1 t2 t3) (If s1 s2 s3) x t.


(* reduce *)
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

(* type *)
Module StrDec : DecidableType
    with Definition t := string
    with Definition eq := fun (x y : string) => x = y.
  Definition t := string.
  Definition eq_dec := string_dec.
  Definition eq (x y : string) := x = y.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    unfold eq.
    intros.
    reflexivity.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    unfold eq.
    apply sym_eq.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq.
    apply trans_eq.
  Qed.
End StrDec.

Module TEnv := FMapWeakList.Make StrDec.
Module TEnvWF := FMapFacts.WFacts_fun StrDec TEnv.
Module TEnvProp := WProperties_fun StrDec TEnv.
Definition tenv := TEnv.t type.
Definition empty_env : tenv := TEnv.empty type.

Inductive Typed : term -> tenv -> type -> Prop :=
  | TVar    : forall (tenv : tenv) (s : string) (ty : type),
                TEnv.MapsTo s ty tenv -> Typed (Var s) tenv ty
  | TBool   : forall (tenv : tenv) (b : bool) ,
                Typed (Bool b) tenv BoolT
  | TLambda : forall (tenv : tenv) (x : string) (a b : type) (body : term),
                Typed body (TEnv.add x a tenv) b -> Typed (Lambda x a body) tenv (FunT a b)
  | TApply  : forall (tenv : tenv) (t1 t2 : term) (a b : type),
                Typed t1 tenv (FunT a b) -> Typed t2 tenv a -> Typed (Apply t1 t2) tenv b
  | TIf     : forall (tenv : tenv) (t1 t2 t3 : term) (ty : type),
                Typed t1 tenv BoolT -> Typed t2 tenv ty -> Typed t3 tenv ty ->
                   Typed (If t1 t2 t3) tenv ty.
