Definition mbind {A : Type} (x : option A) (f : A -> option A) : option A :=
  match x with
  | None => None
  | Some y => f y
  end.
Infix ">>=" := mbind (at level 50).

Definition app {A B : Type} (f : A -> B) (x : A) := f x.
Infix "$" := app (at level 51, right associativity).


Ltac Contrapositive H :=
  intro;
  apply H.

Ltac Dup H :=
  generalize H;
  intro.

