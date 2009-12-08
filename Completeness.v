Require Import List.
Require Import String.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.


Definition sub tsubst tvars :=
  TVars.FSet.fold (fun x (table : table type) => Table.remove x table) tvars tsubst.

Definition Disjoint (tsubst : tsubst) tvars := forall x,
  Table.In x tsubst -> ~ TVars.In x tvars /\
  TVars.In x tvars  -> ~ Table.In x tsubst.

Lemma sub_empty : forall tsubst,
  tsubst = sub tsubst TVars.empty.
Proof.
intro tubst.
reflexivity.
Qed.

Theorem completeness: forall t tenv S T X C tsubst1 tsubst2,
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
apply TypeConstraint_ind; unfold Solution; unfold Constraint.Solution; simpl; intros.
 intros.
 exists TVars.empty.
 split.
  apply CTVar.
  trivial.

  split.
   apply Unified_empty.

   rewrite <- sub_empty in H3.
   rewrite <- H3 in |- *.
   inversion H1.
   unfold tenv_subst in H5.
   apply
    (TableWF.map_mapsto_iff tenv0 s T1 (fun T : type => type_subst T tsubst1))
    in H5.
   inversion H5.
   inversion H8.
   assert (x = T0).
    apply TableWF.MapsTo_fun with (m := tenv0) (x := s); trivial.

    trivial.

