Require Import List.
Require Import ListSet.
Require Import String.
Require Import Recdef.

Require Import Util.
Require Import Term.
Require Import Alpha.

Definition Value v :=
  match v with
  | Bool _ => True
  | Lambda _ _ _ => True
  | _ => False
  end.

Function subst (t : term) (old : string) (new : term) {measure term_length t}: term :=
  match t with
  |  Var s =>
    if string_dec s old then
      new
    else
      t
  | Bool _  =>
      t
  | Lambda x T body =>
      if string_dec x old then
      	Lambda x T body
      else
      	let y := Fresh old new body in
          Lambda y T (subst (alpha body x y) old new)
  | Apply t1 t2 =>
      Apply (subst t1 old new) (subst t2 old new)
  | If t1 t2 t3 =>
      If (subst t1 old new) (subst t2 old new) (subst t3 old new)
  end.
Proof.
 intros.
 rewrite <- alpha_length in |- *.
 apply Lt.le_lt_n_Sm.
 apply le_n.

 intros.
 simpl.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_l.

 intros.
 simpl.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_trans.
 apply Plus.le_plus_r.

 intros.
 simpl.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_trans.
 apply Plus.le_plus_l.
Qed.


Inductive Eval : term -> term -> Prop :=
  | EAppLeft  : forall t1 t2 t' : term, Eval t1 t' -> Eval (Apply t1 t2) (Apply t' t2)
  | EAppRight : forall t1 t2 t' : term, Value t1   -> Eval t2 t' -> Eval (Apply t1 t2) (Apply t1 t')
  | ELambda   : forall (x : string) (T : type) (t v : term), Value v -> Eval (Apply (Lambda x T t) v) (subst t x v)
  | EIfCond   : forall (t1 t2 t3 : term) t', Eval t1 t' -> Eval (If t1 t2 t3) (If t' t2 t3)
  | EIfTrue   : forall (t1 t2 : term), Eval (If (Bool true) t1 t2) t1
  | EIfFalse  : forall (t1 t2 : term), Eval (If (Bool false) t1 t2) t2.

Definition value_dec : forall (t : term), {Value t} + {~ Value t}.
Proof.
intros.
induction t; simpl; tauto.
Qed.

