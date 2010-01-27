Require Import String.

Require Import Util.
Require Import Term.
Require Import TypingRule.
Require Import Tables.

Definition tsubst := table type.

Fixpoint type_subst t (tsubst : tsubst) :=
  match t with
  | VarT x => match Table.find x tsubst with
              | Some y => y
      	      | None   => VarT x
              end
  | BoolT =>  BoolT
  | FunT T1 T2 => FunT (type_subst T1 tsubst) (type_subst T2 tsubst)
  end.

Definition tenv_subst tenv tsubst :=
  Table.map (fun T => type_subst T tsubst) tenv.

Fixpoint term_subst t tsubst :=
  match t with
  | Var x => Var x
  | Bool b => Bool b
  | Lambda x T t =>
     Lambda x (type_subst T tsubst) (term_subst t tsubst)
  | Apply t1 t2 =>
     Apply (term_subst t1 tsubst) (term_subst t2 tsubst)
  | If t1 t2 t3 =>
     If (term_subst t1 tsubst) (term_subst t2 tsubst) (term_subst t3 tsubst)
  end.

