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

Definition union {A : Type} (tsubst1 tsubst2 : table A) :=
  Table.fold (fun key e m => Table.add key e m) tsubst1 tsubst2.

Definition filter {A : Type} {P : string -> Prop} (dec : forall x, {P x} + {~ P x}) (tsubst : table A) :=
  TableProp.filter
    (fun key _ => if dec key then true else false)
    tsubst.

Lemma mapsto_type_subst: forall x tsubst1 tsubst2,
 (forall U, Table.MapsTo x U tsubst1 <-> Table.MapsTo x U tsubst2) ->
 type_subst (VarT x) tsubst1 = type_subst (VarT x) tsubst2.
Proof.
intros; simpl.
destruct (TableWF.In_dec tsubst1 x).
 unfold Table.In, Table.Raw.PX.In in i.
 decompose [ex] i.
 Dup H0.
 apply H in H0.
 apply TableWF.find_mapsto_iff in H0.
 apply TableWF.find_mapsto_iff in H1.
 rewrite H0,H1 in |- *.
 reflexivity.

 assert (~ Table.In (elt:=type) x tsubst2).
  Contrapositive n.
  unfold Table.In, Table.Raw.PX.In in H0.
  decompose [ex] H0.
  unfold Table.In, Table.Raw.PX.In in |- *.
  exists x0.
  apply <- H.
  tauto.

  apply TableWF.not_find_mapsto_iff in n.
  apply TableWF.not_find_mapsto_iff in H0.
  rewrite n,H0 in |- *.
  reflexivity.
Qed.

Lemma union_iff: forall A x (T : A) (X Y : table A),
  Table.MapsTo x T (union X Y) <->
  Table.MapsTo x T X \/ (~ Table.In x X /\ Table.MapsTo x T Y).
Proof.
intros.
unfold union in |- *.
pattern X,
 (Table.fold
    (fun (key : Table.key) (e : A) (m : Table.t A) => Table.add key e m) X Y)
 in |- *.
apply TableProp.fold_rec_bis; intros.
 apply Extensionality_Table in H.
 rewrite <- H in |- *.
 tauto.

 split; intros; auto.
  right.
  split; auto.
  intro.
  apply TableWF.empty_in_iff in H0.
  contradiction.

  decompose [or and] H; auto.
  inversion H0.

 split; intros.
  apply TableWF.add_mapsto_iff in H2.
  decompose [or and] H2.
   left.
   rewrite H4, H5 in |- *.
   apply <- TableWF.add_mapsto_iff.
   tauto.

   apply H1 in H5.
   decompose [or and] H5.
    left.
    apply <- TableWF.add_mapsto_iff.
    tauto.

    right.
    split; auto.
    Contrapositive H6.
    apply TableWF.add_in_iff in H3.
    decompose [or] H3; auto.
    contradiction.

  decompose [or and] H2.
   apply TableWF.add_mapsto_iff in H3.
   decompose [or and] H3.
    rewrite H5, H6 in |- *.
    apply <- TableWF.add_mapsto_iff.
    tauto.

    apply <- TableWF.add_mapsto_iff.
    tauto.

   apply <- TableWF.add_mapsto_iff.
   right.
   split.
    Contrapositive H4.
    apply <- TableWF.add_in_iff.
    tauto.

    apply H1.
    right.
    split; auto.
    Contrapositive H4.
    apply <- TableWF.add_in_iff.
    tauto.
Qed.

Lemma filter_iff : forall A x P (dec : forall x, {P x} + {~ P x}) (T : A) (m : table A),
  Table.MapsTo x T (filter dec m) <->
  Table.MapsTo x T m /\ (P x).
Proof.
unfold filter in |- *.
split; intros.
 apply TableProp.filter_iff in H.
  unfold Morphisms.Morphism,Morphisms.respectful in |- *.
  intros.
  rewrite H0 in |- *.
  reflexivity.

  decompose [and] H.
  split; auto.
  destruct (dec x); auto.
  discriminate.

 apply <- TableProp.filter_iff.
  decompose [and] H.
  split; auto.
  destruct (dec x); auto.

  unfold Morphisms.Morphism, Morphisms.respectful in |- *.
  intros.
  rewrite H0 in |- *.
  reflexivity.
Qed.



(*Lemma add_eq : forall x T tenv tsubst,
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
*)