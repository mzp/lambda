Require Import List.
Require Import String.

Require Import Util.
Require Import Term.
Require Import TVar.
Require Import TVars.
Require Import ConstraintRule.

Lemma apply_disjoint_term: forall x t1 t2 T1 T2 X1 X2 C1 C2,
  CTApplyDisjoint t1 t2 T1 T2 X1 X2 C1 C2 ->
  TVars.In x X1 -> ~FreeTerm x t2.
Proof.
unfold CTApplyDisjoint, DisjointTerm, DisjointBy.
intros.
decompose [and] H.
auto.
Qed.

Lemma apply_disjoint_sym: forall t1 t2 T1 T2 X1 X2 C1 C2,
  CTApplyDisjoint t1 t2 T1 T2 X1 X2 C1 C2 ->
  CTApplyDisjoint t2 t1 T2 T1 X2 X1 C2 C1.
Proof.
unfold CTApplyDisjoint.
intros.
decompose [and] H.
split.
 apply TVars.disjoint_sym.
 auto.

 split; auto.
Qed.

Lemma free_apply_inv : forall x t1 t2,
  ~ FreeTerm x t1 -> ~ FreeTerm x t2 -> ~ FreeTerm x (Apply t1 t2).
Proof.
intros.
intro.
inversion H1.
decompose [or] H4; contradiction.
Qed.

Lemma if_disjoint_term: forall x t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3,
 CTIfDisjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3 ->
 TVars.In x X1 -> ~FreeTerm x t2 /\ ~FreeTerm x t3.
Proof.
unfold CTIfDisjoint,DisjointTerm,DisjointBy.
intros.
decompose [and] H.
auto.
Qed.

Lemma if_disjoint_sym1: forall t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3,
 CTIfDisjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3 ->
 CTIfDisjoint t2 t1 t3 T2 T1 T3 X2 X1 X3 C2 C1 C3.
Proof.
unfold CTIfDisjoint.
intros.
decompose [and] H.
repeat (split;
        try (apply TVars.disjoint_sym);
        auto).
Qed.

Lemma if_disjoint_sym2: forall t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3,
 CTIfDisjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3 ->
 CTIfDisjoint t3 t2 t1 T3 T2 T1 X3 X2 X1 C3 C2 C1.
Proof.
unfold CTIfDisjoint.
intros.
decompose [and] H.
repeat (split;
        try (apply TVars.disjoint_sym);
        auto).
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
