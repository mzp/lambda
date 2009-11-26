Require Import List.
Require Import String.
Require Import Typing.

Require Import Term.
Require Import TypeSubst.

Definition tconst := list (type * type).
Definition Unified (c : tconst) (t : tsubst) := forall S T U,
  In (S,T) c -> TypeSubst S U t /\ TypeSubst T U t.
Definition tvars := list string.

Inductive TypeConstraint : term -> tenv -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv T X C,
    TEnv.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv T X C
| CTLambda : forall x T1 T2 t tenv X C,
    TypeConstraint t (TEnv.add x T1 tenv) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv (FunT T1 T2) X C
| CTApply : forall x t1 t2 T1 T2 tenv X1 X2 X C1 C2 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    X = x :: X1 ++ X2 -> NoDup X ->
    (* memo:
        - NoUnion X (FV T2)
        - NoUnion X (FV T1)
        -X is not in (X1 X2 T1 T2 C1 C2 tenv t1 t2)
    *)
    C = (T1,FunT T2 (VarT x)) :: C1 ++ C2 ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) X C
| CTBool : forall b tenv X C,
    TypeConstraint (Bool b) tenv BoolT X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C3 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = X1 ++ X2 ++ X3 -> NoDup X ->
    C = (T1,BoolT) :: (T2,T3) :: C1 ++ C2 ++ C3 ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

