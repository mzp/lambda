Require Import String.

Inductive type : Set :=
  | VarT  : string -> type
  | BoolT : type
  | FunT  : type -> type -> type.

Inductive term : Set :=
    Var     : string -> term
  | Bool    : bool   -> term
  | Lambda  : string -> type -> term -> term
  | Apply   : term  -> term -> term
  | If      : term -> term -> term -> term.

Fixpoint term_length (t : term) :=
  match t with
  |  Var _ | Bool _ =>
    1
  | Lambda _ _ body =>
    1 + term_length body
  | Apply t1 t2 =>
    1 + term_length t1 + term_length t2
  | If t1 t2 t3 =>
    1 + term_length t1 + term_length t2 + term_length t3
  end.


Definition type_dec (x y : type) : {x = y} + {x <> y}.
Proof.
intros.
decide equality.
apply string_dec.
Qed.