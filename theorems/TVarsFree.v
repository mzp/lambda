Require Import List.
Require Import String.

Require Import Util.
Require Import Term.
Require Import TVar.
Require Import TVars.
Require Import ConstraintRule.

Lemma free_apply_inv : forall x t1 t2,
  ~ FreeTerm x t1 -> ~ FreeTerm x t2 -> ~ FreeTerm x (Apply t1 t2).
Proof.
intros.
intro.
inversion H1.
decompose [or] H4; contradiction.
Qed.

Lemma free_if_inv : forall x t1 t2 t3,
  ~ FreeTerm x t1 -> ~ FreeTerm x t2 -> ~ FreeTerm x t3 ->
  ~ FreeTerm x (If t1 t2 t3).
Proof.
intros.
intro.
inversion H2.
decompose [or] H5; contradiction.
Qed.

Lemma tvars_not_free : forall t X x tenv Ts S C,
  TypeConstraint t tenv Ts S X C ->
  TVars.In x X ->
  ~ FreeTs x Ts /\ ~ FreeTerm x t.
Proof.
unfold FreeTs.
intros until C.
intro.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; intros; auto.
 inversion H1.

 apply H1 in H2.
 decompose [and] H2.
 split.
  Contrapositive H3.
  decompose [ex and] H5.
  exists x1.
  split; auto.
  apply in_cons.
  assumption.

  intro.
  inversion H5.
  decompose [or] H8; auto.
  apply H3.
  exists T1.
  split; auto.
  apply in_eq.

 inversion H0.

 rewrite H7 in H8.
 rewrite TVars.WFact.add_iff, TVars.WFact.union_iff in H8.
 decompose [or] H8.
  rewrite <- H9 in |- *.
  split.
   intro.
   decompose [ex and] H10.
   unfold Fresh in H5.
   decompose [and] H5.
   contradiction.

   unfold Fresh in H5.
   decompose [and] H5.
   apply free_apply_inv; auto.

  apply (apply_disjoint_term x) in H4; auto.
  apply H1 in H10.
  decompose [and] H10.
  split; auto.
  apply free_apply_inv; auto.

  apply apply_disjoint_sym, (apply_disjoint_term x) in H4; auto.
  apply H3 in H10.
  decompose [and] H10.
  split; auto.
  apply free_apply_inv; auto.

 rewrite H8 in H9.
 do 2 (rewrite TVars.WFact.union_iff in H9).
 decompose [or] H9.
  apply (if_disjoint_term x) in H6; auto.
  decompose [and] H6.
  apply H1 in H10.
  decompose [and] H10.
  split; auto.
  apply free_if_inv; auto.

  apply if_disjoint_sym1, (if_disjoint_term x) in H6; auto.
  decompose [and] H6.
  apply H3 in H11.
  decompose [and] H11.
  split; auto.
  apply free_if_inv; auto.

  apply if_disjoint_sym2, (if_disjoint_term x) in H6; auto.
  decompose [and] H6.
  apply H5 in H11.
  decompose [and] H11.
  split; auto.
  apply free_if_inv; auto.
Qed.
