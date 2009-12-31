Require Import List.
Require Import String.
Require Import Sumbool.
Require Import Classical.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.
Require Import TypeSubstFact.

(* Lemma *)

(* for var *)
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

(* for lambda *)
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

  apply sub_find with (A:=type) (tsubst:=tsubst2) in n.
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

(* for apply *)
Lemma apply_inv: forall T tenv tsubst t1 t2,
  Solution tsubst T tenv (Apply t1 t2) ->
  exists T1,
  Solution tsubst (FunT T1 T) tenv t1 /\ Solution tsubst T1 tenv t2.
Proof.
intros.
inversion H.
exists a.
split; trivial.
Qed.

Definition ApplyTSubst X X1 X2 tsubst tsubst1 tsubst2 x T :=
  union (filter (fun x => not_sumbool $ TVars.WProp.In_dec x X) tsubst) $
  union (filter (fun x => TVars.WProp.In_dec x X1) tsubst1) $
  union (filter (fun x => TVars.WProp.In_dec x X2) tsubst2) $
  Table.add x T (Table.empty type).

Lemma ApplyTSubst_sub : forall tsubst tsubst1 tsubst2 X X1 X2 x T,
  ~ TVars.In x X1 -> ~ TVars.In x X2 ->   Disjoint tsubst X ->
  X = TVars.add x (TVars.union X1 X2) ->
  tsubst = sub (ApplyTSubst X X1 X2 tsubst tsubst1 tsubst2 x T) X.
Proof.
intros.
apply Extensionality_Table.
apply <- TableWF.Equal_mapsto_iff (* Generic printer *).
unfold sub in |- *; unfold ApplyTSubst in |- *; unfold app in |- *.
split; intros.
 apply <- filter_iff (* Generic printer *).
 unfold Disjoint in H1.
 specialize (H1 k).
 decompose [and] H1.
 destruct (TVars.WProp.In_dec k X).
  apply H5 in i.
  unfold Table.In in i.
  unfold Table.Raw.PX.In in i.
  assert False.
   apply i.
   exists e.
   trivial.

   contradiction .

  split.
   apply <- union_iff (* Generic printer *).
   left.
   apply <- filter_iff (* Generic printer *).
   split; trivial.

   trivial.

 apply filter_iff in H3.
 decompose [and] H3.
 apply union_iff in H4.
 decompose [or] H4.
  apply filter_iff in H6.
  tauto.

  decompose [and] H6.
  apply union_elim in H8.
   apply union_elim in H8.
    assert False.
     apply H7.
     apply TableWF.add_mapsto_iff in H8.
     decompose [or] H8.
      inversion H9.
      assert False.
       apply H5.
       rewrite <- H10 in |- *.
       rewrite H2 in |- *.
       apply <- TVars.WFact.add_iff (* Generic printer *).
       left; reflexivity.

       contradiction .

      decompose [and] H9.
      inversion H11.

     contradiction .

    intro.
    apply H5.
    rewrite H2 in |- *.
    apply <- TVars.WFact.add_iff (* Generic printer *).
    right.
    apply <- TVars.WFact.union_iff (* Generic printer *).
    right.
    trivial.

   intro.
   apply H5.
   rewrite H2 in |- *.
   apply <- TVars.WFact.add_iff (* Generic printer *).
   right.
   apply <- TVars.WFact.union_iff (* Generic printer *).
   left.
   trivial.
Qed.

(* main theorem *)
Theorem completeness: forall t tenv Ts S T X C tsubst1,
  TypeConstraint t tenv Ts S X C ->
  TypeSubst.Solution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  exists tsubst2,
    tsubst1 = sub tsubst2 X /\
    Constraint.Solution tsubst2 T tenv Ts t S C.
Proof.
intros until tsubst1.
intro.
generalize T.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; unfold Constraint.Solution in |- *; simpl in |- *;
 intros.
 exists tsubst1.
 split.
  apply sub_empty.

  exists TVars.empty.
  split.
   apply CTVar.
   trivial.

   split.
    apply Unified_empty.

    apply var_inv with (S := T0) in H1.
     trivial.

     trivial.

 apply lambda_inv in H2.
 decompose [ex] H2.
 decompose [and] H4.
 apply H1 in H5.
  decompose [ex] H5.
  decompose [and] H7.
  exists x1.
  split.
   trivial.

   exists X0.
   split.
    apply CTLambda.
    trivial.

    split.
     decompose [ex] H9.
     tauto.

     assert (type_subst T1 tsubst1 = type_subst T1 x1).
      apply subst_eq with (X := X0).
       intros.
       apply tvars_free with (x := x2) in H0.
        decompose [and] H0.
        unfold FreshTs in H11.
        apply H11.
        apply in_eq.

        trivial.

       trivial.

      rewrite H6 in |- *.
      rewrite H10 in |- *.
      decompose [ex] H9.
      decompose [and] H11.
      rewrite H15 in |- *.
      trivial.

  trivial.

 exists tsubst1.
 split.
  apply sub_empty.

  exists TVars.empty.
  split.
   apply CTBool.

   split.
    apply Unified_empty.

    inversion H0.
    reflexivity.

 apply apply_inv in H11.
 decompose [ex] H11.
 decompose [and] H13.
 apply H1 in H14.
  apply H3 in H15.
   decompose [ex] H14; decompose [ex] H15.
   decompose [and] H16; decompose [and] H17.

