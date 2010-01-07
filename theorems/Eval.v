Require Import List.
Require Import ListSet.
Require Import String.
Require Import Recdef.

Require Import Term.
Require Import Alpha.

(** * Propotion *)
Inductive Value  : term -> Prop :=
  | VBool   : forall b : bool,   Value (Bool b)
  | VLambda : forall (x : string) (ty : type) (body : term), Value (Lambda x ty body).

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
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply le_n.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_l.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_trans.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
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

Definition mbind {A : Type} (x : option A) (f : A -> option A) : option A :=
  match x with
  | None => None
  | Some y => f y
  end.

Infix ">>=" := mbind (at level 50).

Definition value_dec : forall (t : term), {Value t} + {~ Value t}.
Proof.
destruct t.
 right.
 intro.
 inversion H.

 left.
 apply VBool.

 left.
 apply VLambda.

 right; intro.
 inversion H.

 right.
 intro.
 inversion H.
Qed.

Fixpoint eval (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      None
  | Apply t1 t2 =>
      if value_dec t1 then
      	if value_dec t2 then
       	  match t1 with
      	    Lambda x _ body => Some (subst body x t2)
          | _ => None
      	  end
      	else
	  eval t2 >>= (fun t => Some (Apply t1 t))
      else
      	eval t1 >>= (fun t => Some (Apply t t2))
  | If (Bool true) t2 t3 =>
      Some t2
  | If (Bool false) t2 t3 =>
      Some t3
  | If t1 t2 t3 =>
      eval t1 >>= (fun x => Some (If x t2 t3))
  end.

Lemma not_eval : forall t,
  Value t -> None = eval t.
Proof.
destruct t.
 simpl in |- *; intro.
 inversion H.

 simpl in |- *; intro.
 reflexivity.

 simpl in |- *; intro.
 reflexivity.

 intro.
 inversion H.

 intro.
 inversion H.
Qed.

Theorem eval_equal1 : forall t r,
  Some r = eval t -> Eval t r.
Proof.
induction t.
 simpl in |- *; intros; discriminate.

 simpl in |- *; intros; discriminate.

 simpl in |- *; intros; discriminate.

 simpl in |- *.
 destruct (value_dec t1).
  destruct (value_dec t2).
   destruct t1.
    inversion v.

    intros; discriminate.

    intros.
    inversion H.
    apply ELambda.
    exact v0.

    intros; discriminate.

    intros; discriminate.

   destruct (eval t2).
    simpl in |- *.
    intros.
    inversion H.
    apply EAppRight.
     exact v.

     apply IHt2.
     reflexivity.

    simpl in |- *.
    intros; discriminate.

  destruct (eval t1).
   simpl in |- *.
   intros.
   inversion H.
   apply EAppLeft.
   apply IHt1.
   reflexivity.

   simpl in |- *.
   intros; discriminate.

 simpl in |- *.
 destruct t1.
  simpl in |- *; intros; discriminate.

  destruct b.
   simpl in |- *.
   intros.
   inversion H.
   apply EIfTrue.

   intros.
   inversion H.
   apply EIfFalse.

  simpl in |- *; intros; discriminate.

  destruct (eval (Apply t1_1 t1_2)).
   simpl in |- *.
   intros.
   inversion H.
   apply EIfCond.
   apply IHt1.
   reflexivity.

   simpl in |- *; intros; discriminate.

  destruct (eval (If t1_1 t1_2 t1_3)).
   simpl in |- *; intros.
   inversion H.
   apply EIfCond.
   apply IHt1.
   reflexivity.

   simpl in |- *; intros; discriminate.
Qed.

Theorem eval_equal2 : forall t r,
  Eval t r -> Some r = eval t.
Proof.
apply Eval_ind.
 intros.
 simpl in |- *.
 destruct (value_dec t1).
  apply not_eval in v.
  rewrite <- v in H0.
  discriminate.

  rewrite <- H0 in |- *.
  simpl in |- *.
  reflexivity.

 intros.
 simpl in |- *.
 destruct (value_dec t1).
  destruct (value_dec t2).
   apply not_eval in v0.
   rewrite <- v0 in H1.
   discriminate.

   rewrite <- H1 in |- *.
   simpl in |- *.
   reflexivity.

  contradiction .

 intros.
 simpl in |- *.
 destruct (value_dec (Lambda x T t)).
  destruct (value_dec v).
   reflexivity.

   contradiction .

  assert (Value (Lambda x T t)).
   apply VLambda.

   contradiction .

 intros.
 simpl in |- *.
 rewrite <- H0 in |- *.
 simpl in |- *.
 destruct t1.
  reflexivity.

  simpl in H0.
  discriminate.

  reflexivity.

  reflexivity.

  reflexivity.

 simpl in |- *.
 intros.
 reflexivity.

 simpl in |- *.
 intros.
 reflexivity.
Qed.
