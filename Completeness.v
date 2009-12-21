Require Import List.
Require Import String.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.

Definition sub tsubst tvars :=
  TVars.FSet.fold (fun x (table : table type) => Table.remove x table) tvars tsubst.

Lemma sub_not_in : forall X tsubst x,
  Table.In x tsubst -> TVars.In x X -> ~ Table.In x (sub tsubst X).
Proof.
intros until x.
intro.
unfold sub in |- *.
pattern X,
 (TVars.FSet.fold
    (fun (x0 : TVars.FSet.elt) (table : table type) =>
     Table.remove (elt:=type) x0 table) X tsubst) in |- *.
apply TVars.WProp.fold_rec_bis; intros.
 apply H1.
 unfold TVars.FSet.Equal in H0.
 apply (H0 x).
 trivial.

 inversion H0.

 intro.
 apply (TableWF.remove_in_iff a x0 x) in H4.
 decompose [and] H4.
 apply TVars.WFact.add_iff in H3.
 decompose [or] H3.
  contradiction .

  apply H2 in H7.
  contradiction .
Qed.

Lemma sub_in : forall tsubst x X,
  Table.In x tsubst -> ~ TVars.In x X -> Table.In x (sub tsubst X).
Proof.
intros.
unfold sub in |- *.
pattern X,
 (TVars.FSet.fold
    (fun (x0 : TVars.FSet.elt) (table : table type) =>
     Table.remove (elt:=type) x0 table) X tsubst) in |- *.
apply TVars.WProp.fold_rec; intros.
 trivial.

 apply (TableWF.remove_in_iff a x0 x).
 split.
  intro.
  apply H0.
  rewrite <- H5 in |- *.
  trivial.

  trivial.
Qed.

Lemma subst_eq : forall T X tsubst1 tsubst2,
  (forall x,TVars.In x X -> FreshT x T) ->
  tsubst1 = sub tsubst2 X ->
  type_subst T tsubst1 = type_subst T tsubst2.


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
(*Theorem completeness: forall t tenv S T X C tsubst1 tsubst2,
  TypeConstraint t tenv S X C ->
  TypeSubst.Solution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  tsubst1 = sub tsubst2 X ->
  Constraint.Solution tsubst2 T tenv t S C.
Proof.
intros until tsubst2.
intro.
generalize T.
pattern t, tenv, S, X, C in |- *.
apply TypeConstraint_ind; unfold Constraint.Solution; simpl; intros.
 exists TVars.empty.
 split.
  apply CTVar.
  trivial.

  split.
   apply Unified_empty.

   apply var_inv with (S := T0) in H1.
    rewrite <- sub_empty in H3.
    rewrite <- H3 in |- *.
    trivial.

    trivial.

 exists X0.
 split.
  apply CTLambda.
  trivial.

  apply lambda_inv in H2.
  decompose [ex] H2.
  inversion H5.
  apply H1 in H6.
   inversion H6.
   inversion H8.
   inversion H10.
   split.
    trivial.

    rewrite H12 in H7.
*)
