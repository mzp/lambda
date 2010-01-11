Require Import Term.
Require Import Util.
Require Import Eval.

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
destruct t; simpl; intros; auto.
 contradiction.

 contradiction.
Qed.

Theorem eval_equal1 : forall t r,
  Some r = eval t -> Eval t r.
Proof.
induction t; simpl; intros.
 discriminate.

 discriminate.

 discriminate.

 destruct (value_dec t1).
  destruct (value_dec t2).
   destruct t1.
    inversion v.

    discriminate.

    inversion H.
    apply ELambda.
    tauto.

    discriminate.

    discriminate.

   destruct (eval t2).
    inversion H.
    apply EAppRight.
     tauto.

     apply IHt2.
     reflexivity.

    discriminate.

  destruct (eval t1).
   inversion H.
   apply EAppLeft.
   apply IHt1.
   reflexivity.

   discriminate.

 destruct t1.
  discriminate.

  destruct b.
   inversion H.
   apply EIfTrue.

   inversion H.
   apply EIfFalse.

  discriminate.

  destruct (eval (Apply t1_1 t1_2)).
   inversion H.
   apply EIfCond.
   apply IHt1.
   reflexivity.

   discriminate.

  destruct (eval (If t1_1 t1_2 t1_3)).
   inversion H.
   apply EIfCond.
   apply IHt1.
   reflexivity.

   discriminate.
Qed.

Theorem eval_equal2 : forall t r,
  Eval t r -> Some r = eval t.
Proof.
apply Eval_ind; simpl; intros.
 destruct (value_dec t1).
  apply not_eval in v.
  rewrite <- v in H0.
  discriminate.

  rewrite <- H0 in |- *.
  reflexivity.

 destruct (value_dec t1).
  destruct (value_dec t2).
   apply not_eval in v0.
   rewrite <- v0 in H1.
   discriminate.

   rewrite <- H1 in |- *.
   reflexivity.

  contradiction.

 destruct (value_dec (Lambda x T t)).
  destruct (value_dec v).
   reflexivity.

   contradiction.

  assert (Value (Lambda x T t)).
   simpl.
   tauto.

   contradiction.

 rewrite <- H0 in |- *.
 destruct t1; auto.
  discriminate.

 reflexivity.

 reflexivity.
Qed.
