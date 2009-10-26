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
  | Apply   : term  -> term -> term
  | If      : term -> term -> term -> term.

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
    | If t1 t2 t3 =>
      If (subst t1 old new) (subst t2 old new) (subst t3 old new)
  end.

Definition is_value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      true
  | Apply _ _  | If _ _ _ =>
      false
  end.

Fixpoint eval (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      None
  | Apply t1 t2 =>
      match eval t1 with
        Some t => Some (Apply t t2)
      | None =>
      	 match eval t2 with
	  Some t => Some (Apply t1 t)
       	| None   =>
      	   match t1 with
	   Lambda x _ body => Some (subst body x t2)
      	 | _ => None
      	   end
         end
      end
  | If (Bool true) t2 t3 =>
      Some t2
  | If (Bool false) t2 t3 =>
      Some t3
  | If t1 t2 t3 =>
      match eval t1 with
      	None   => None
      | Some t => Some (If t t2 t3)
      end
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
  | If t1 t2 t3 =>
    match typing t1 tenv with
      Some BoolT =>
      	match (typing t2 tenv, typing t3 tenv) with
      	(Some ty1, Some ty2) =>
          if type_dec ty1 ty2 then
      	    Some ty1
      	  else
	    None
      	| _ =>
      	  None
      	end
    | _ =>
        None
    end
  end.

(* theorem *)
Definition value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      True
  | Apply _ _  | If _ _ _ =>
      False
  end.

