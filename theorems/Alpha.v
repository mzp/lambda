Require Import List.
Require Import String.

Require Import Util.
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
induction t; simpl in |- *; intros; auto.
 destruct (string_dec s x); reflexivity.

 destruct (string_dec s x).
  reflexivity.

  simpl in |- *.
  rewrite <- IHt in |- *.
  reflexivity.
Qed.

Lemma alpha_id: forall t x,
  alpha t x x = t.
Proof.
induction t; intros; simpl; auto.
 destruct (string_dec s x).
  rewrite e.
  reflexivity.

  reflexivity.

 destruct (string_dec s x).
  reflexivity.

  rewrite IHt in |- *.
  reflexivity.

 rewrite IHt1, IHt2 in |- *.
 reflexivity.

 rewrite IHt1,  IHt2,  IHt3 in |- *.
 reflexivity.
Qed.

Lemma alpha_not_free : forall t x y,
  x <> y -> ~ Free x (alpha t x y).
Proof.
induction t; intros; simpl; auto.
 destruct (string_dec s x).
  Contrapositive H.
  inversion H0.
  reflexivity.

  Contrapositive n.
  inversion H0.
  reflexivity.

 intro.
 inversion H0.

 destruct (string_dec s x).
  rewrite e in |- *.
  intro.
  inversion H0.
  tauto.

  intro.
  inversion H0.
  generalize H6.
  apply IHt.
  tauto.

 intro.
 inversion H0.
 decompose [or] H3.
  generalize H5.
  apply IHt1.
  tauto.

  generalize H5.
  apply IHt2.
  tauto.

 intro.
 inversion H0.
 decompose [or] H3;
  [ unfold not in IHt1; apply (IHt1 x y) |
    unfold not in IHt2; apply (IHt2 x y) |
    unfold not in IHt3; apply (IHt3 x y) ];
  tauto.
Qed.
