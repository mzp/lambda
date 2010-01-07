Require Import List.
Require Import String.

Require Import Term.
Require Import Var.

Variable Fresh : string -> term -> term -> string.
Hypothesis Fresh_x : forall x s t, x <> Fresh x s t.
Hypothesis Fresh_fv1 : forall x s t, ~Free (Fresh x s t) s.
Hypothesis Fresh_fv2 : forall x s t, ~Free (Fresh x s t) t.

Hypothesis Fresh_bv1 : forall x s t, ~Bound (Fresh x s t) s.
Hypothesis Fresh_bv2 : forall x s t, ~Bound (Fresh x s t) t.

Fixpoint alpha (t : term) (old new : string) :=
  match t with
  |  Var s =>
    if string_dec s old then
      Var new
    else
      t
  | Bool _  =>
      t
  | Lambda x T body =>
      if string_dec x old then
      	Lambda x T body
      else
        Lambda x T (alpha body old new)
  | Apply t1 t2 =>
      Apply (alpha t1 old new) (alpha t2 old new)
  | If t1 t2 t3 =>
      If (alpha t1 old new) (alpha t2 old new) (alpha t3 old new)
  end.

Lemma alpha_length : forall t x y,
  term_length t = term_length (alpha t x y).
Proof.
induction t.
 simpl in |- *.
 intros.
 destruct string_dec; simpl in |- *; reflexivity.

 simpl in |- *.
 intros; reflexivity.

 simpl in |- *.
 intros.
 destruct (string_dec s x); simpl in |- *.
  reflexivity.

  rewrite (IHt x y) in |- *.
  reflexivity.

 simpl in |- *.
 intros.
 rewrite (IHt1 x y) in |- *.
 rewrite (IHt2 x y) in |- *.
 reflexivity.

 simpl in |- *.
 intros.
 rewrite (IHt1 x y) in |- *; rewrite (IHt2 x y) in |- *;
  rewrite (IHt3 x y) in |- *.
 reflexivity.
Qed.
