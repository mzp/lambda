Require Import String.
Require Import DecidableType.
Require Import Term.

Open Scope type_scope.

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

Module typeDec : DecidableType
    with Definition t := type
    with Definition eq := fun (x y : type) => x = y.
  Definition t := type.
  Definition eq (x y : type) := x = y.
  Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
  Proof.
  unfold eq.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  Qed.

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
End typeDec.

Module PairDec (A B : DecidableType) : DecidableType
    with Definition t := A.t * B.t
    with Definition eq := fun (x y : A.t * B.t) => A.eq (fst x) (fst y) /\ B.eq (snd x) (snd y).
  Definition t := A.t * B.t.
  Definition eq := fun (x y : A.t * B.t) => A.eq (fst x) (fst y) /\ B.eq (snd x) (snd y).
  Definition eq_dec (x y : A.t * B.t) : {eq x y} + {~ eq x y}.
  Proof.
  intros.
  destruct x.
  destruct y.
  unfold eq in |- *.
  simpl in |- *.
  destruct (A.eq_dec t0 t2).
  destruct (B.eq_dec t1 t3).
    left.
    split; trivial.

    right.
    intro.
    apply n.
    inversion H.
    trivial.

  right.
  intro.
  apply n.
  inversion H; trivial.
  Qed.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
  unfold eq in |- *.
  destruct x.
  simpl in |- *.
  split; [ apply A.eq_refl | apply B.eq_refl ].
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
  unfold eq in |- *.
  destruct x; destruct y.
  simpl in |- *.
  intros.
  inversion H.
  split.
   apply A.eq_sym; trivial.

   apply B.eq_sym; trivial.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
  unfold eq in |- *.
  destruct x; destruct y; destruct z.
  simpl in |- *.
  intros.
  inversion H; inversion H0.
  split.
   apply A.eq_trans with (y := t2); trivial.

   apply B.eq_trans with (y := t3); trivial.
  Qed.

End PairDec.
