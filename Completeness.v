Require Import List.
Require Import String.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.

Definition sub tsubst tvars :=
  TVars.FSet.fold (fun x (table : table type) => Table.remove x table) tvars tsubst.

Lemma sub_find : forall tsubst x X,
  ~ TVars.In x X ->
  Table.find x (sub tsubst X) = Table.find x tsubst.
Proof.
intros.
unfold sub in |- *.
pattern X,
 (TVars.FSet.fold
    (fun (x0 : TVars.FSet.elt) (table : table type) =>
     Table.remove (elt:=type) x0 table) X tsubst) in |- *.
apply TVars.WProp.fold_rec; intros.
 reflexivity.

 rewrite TableWF.remove_o in |- *.
 destruct (TVars.WProp.Dec.F.eq_dec x0 x).
  unfold Dec.StrDec.eq in e.
  rewrite e in H0.
  contradiction .

  rewrite H3 in |- *.
  reflexivity.
Qed.

Lemma fun_fresh_inv : forall (X : TVars.t) T1 T2,
  (forall x, TVars.In x X -> FreshT x (FunT T1 T2)) ->
  (forall x, TVars.In x X -> FreshT x T1) /\
  (forall x, TVars.In x X -> FreshT x T2).
Proof.
intros.
split; intros;
 apply H in H0;
 inversion H0;
 tauto.
Qed.

Lemma subst_eq : forall T X tsubst1 tsubst2,
  (forall x,TVars.In x X -> FreshT x T) ->
  tsubst1 = sub tsubst2 X ->
  type_subst T tsubst1 = type_subst T tsubst2.
Proof.
induction T; intros; simpl in |- *.
 destruct (TVars.WProp.In_dec s X).
  apply H in i.
  inversion i.
  tauto.

  apply (sub_find tsubst2 _ _) in n.
  rewrite <- n in |- *.
  rewrite H0 in |- *.
  reflexivity.

 reflexivity.

 apply fun_fresh_inv in H.
 decompose [and] H.
 apply (IHT1 _ tsubst1 tsubst2) in H1.
  apply (IHT2 _ tsubst1 tsubst2) in H2.
   rewrite H1 in |- *.
   rewrite H2 in |- *.
   reflexivity.

   trivial.

  trivial.
Qed.

Definition Disjoint (tsubst : tsubst) tvars := forall x,
  Table.In x tsubst -> ~ TVars.In x tvars /\
  TVars.In x tvars  -> ~ Table.In x tsubst.

Lemma sub_empty : forall tsubst,
  tsubst = sub tsubst TVars.empty.
Proof.
intro tubst.
reflexivity.
Qed.

(* inversion *)
Lemma var_inv : forall s T S tenv tsubst ,
  Table.MapsTo s S tenv ->
  Solution tsubst T tenv (Var s) ->
  T = type_subst S tsubst.
Proof.
unfold Solution in |- *.
simpl in |- *.
intros.
inversion H0.
unfold tenv_subst in H2.
apply (TableWF.map_mapsto_iff tenv s T (fun T : type => type_subst T tsubst))
 in H2.
inversion H2.
inversion H5.
rewrite H6 in |- *.
assert (x = S).
 apply TableWF.MapsTo_fun with (m := tenv) (x := s); trivial.

 rewrite H8 in |- *.
 reflexivity.
Qed.

Lemma lambda_inv : forall T tenv tsubst x T1 t,
  Solution tsubst T tenv (Lambda x T1 t) ->
  exists T2,
  Solution tsubst T2 (Table.add x T1 tenv) t /\
  T = FunT (type_subst T1 tsubst) T2.
Proof.
unfold Solution in |- *; simpl in |- *.
intros.
inversion H.
exists b.
split.
 unfold tenv_subst in |- *.
 rewrite map_add in |- *.
 trivial.

 reflexivity.
Qed.

(* main theorem *)
Theorem completeness: forall t tenv Ts S T X C tsubst1 tsubst2,
  TypeConstraint t tenv Ts S X C ->
  TypeSubst.Solution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  tsubst1 = sub tsubst2 X ->
  Constraint.Solution tsubst2 T tenv Ts t S C.
