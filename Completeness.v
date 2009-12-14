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
(*
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

*)
