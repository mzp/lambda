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

Definition type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

Inductive term : Set :=
    Var     : string -> term
  | Bool    : bool   -> term
  | Lambda  : string -> type -> term -> term
  | Apply   : term  -> term -> term.

(* Eval *)
Fixpoint subst (t : term) (old : string) (new : term) :=
  match t with
    | Bool _ =>
      t
    | Var x =>
      if string_dec x old then
        new
      else
      	t
  | Lambda x type body =>
      if string_dec x old then
      	t
      else
        Lambda x type (subst body old new)
  | Apply t1 t2 =>
      Apply (subst t1 old new) (subst t2 old new)
  end.

Definition is_value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      true
  | Apply _ _  =>
      false
  end.

Fixpoint step (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      t
  | Apply (Lambda x _ body as t1) t2 =>
      if is_value t2 then
        subst body x t2
      else
      	Apply t1 (step t2)
  | Apply t1 t2 =>
      Apply (step t1) t2
  end.

Fixpoint term_length (t : term) :=
  match t with
    Bool _ | Var _  =>
      1
  | Lambda _ _ body =>
      1 + term_length body
  | Apply t1 t2 =>
      1 + term_length t1 + term_length t2
  end.

(* typing *)
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

Fixpoint typing (t : term) (tenv : list (string * type)) :=
  match t with
    Bool _ =>
      Some BoolT
  | Var x =>
      assoc x tenv
  | Lambda x ty1 body =>
    match typing body ((x,ty1)::tenv) with
      None => None
    | Some ty2 => Some (FunT ty1 ty2)
   end
  | Apply t1 t2 =>
    match (typing t1 tenv, typing t2 tenv) with
       (Some (FunT ty11 ty12),Some ty13) =>
        if type_dec ty11 ty13 then
          Some ty12
      	else
	  None
      | _ => None
    end
  end.

(* theorem *)
Definition value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      True
  | Apply _ _  =>
      False
  end.

