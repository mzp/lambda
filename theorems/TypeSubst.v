Require Import String.

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

Definition Solution tsubst T tenv t :=
  Typed (term_subst t tsubst) (tenv_subst tenv tsubst) T.

Lemma add_eq : forall x T tenv tsubst,
  (Table.add x (type_subst T tsubst) (tenv_subst tenv tsubst)) = (tenv_subst (Table.add x T tenv) tsubst).
Proof.
intros.
unfold tenv_subst in |- *.
apply sym_eq.
change (type_subst T tsubst0)
  with ((fun T0 : type => type_subst T0 tsubst0) T)
  in |- *.
apply map_add.
Qed.

Theorem tsubst_preserve : forall t tenv T tsubst,
  Typed t tenv T ->
  Typed (term_subst t tsubst) (tenv_subst tenv tsubst) (type_subst T tsubst).
Proof.
intros.
pattern t, tenv, T in |- *.
apply Typed_ind; simpl in |- *; intros.
 apply TVar.
 unfold tenv_subst in |- *.
 change (type_subst T0 tsubst0)
  with ((fun T1 : type => type_subst T1 tsubst0) T0)
  in |- *.
 apply Table.map_1.
 trivial.

 apply TBool.

 apply TLambda.
 rewrite add_eq in |- *.
 trivial.

 apply TApply with (S := type_subst S tsubst0); trivial.

 simpl in |- *.
 apply TIf; trivial.

 trivial.
Qed.
