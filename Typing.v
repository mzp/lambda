Require Import List.
Require Import String.
Require Import FSets.FMapWeakList.
Require Import FSets.FMapInterface.
Require Import FSets.FMapFacts.
Require Import Logic.DecidableType.

Require Import Term.

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
