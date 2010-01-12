Definition mbind {A : Type} (x : option A) (f : A -> option A) : option A :=
  match x with
  | None => None
  | Some y => f y
  end.

Infix ">>=" := mbind (at level 50).

Ltac Contrapositive H :=
  intro;
  apply H.

Ltac Dup H :=
  generalize H;
  intro.
