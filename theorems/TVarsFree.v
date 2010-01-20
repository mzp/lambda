Require Import List.
Require Import String.

Require Import Util.
Require Import TVar.
Require Import TVars.
Require Import ConstraintRule.

Lemma apply_disjoint_term: forall x t1 t2 T1 T2 X1 X2 C1 C2,
  CTApplyDisjoint t1 t2 T1 T2 X1 X2 C1 C2 ->
  (TVars.In x X1 -> ~FreeTerm x t2) /\
  (TVars.In x X2 -> ~FreeTerm x t1).
Proof.
unfold CTApplyDisjoint, DisjointTerm, DisjointBy.
intros.
decompose [and] H.
auto.
Qed.

Lemma if_disjoint_term: forall x t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3,
 CTIfDisjoint t1 t2 t3 T1 T2 T3 X1 X2 X3 C1 C2 C3 ->
 (TVars.In x X1 -> ~FreeTerm x t2 /\ ~FreeTerm x t3) /\
 (TVars.In x X2 -> ~FreeTerm x t1 /\ ~FreeTerm x t3) /\
 (TVars.In x X3 -> ~FreeTerm x t1 /\ ~FreeTerm x t2).
Proof.
unfold CTIfDisjoint,DisjointTerm,DisjointBy.
intros.
decompose [and] H.
auto.
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
 apply TVars.WFact.add_iff in H8.
 decompose [or] H8.
  rewrite <- H9 in |- *.
  split.
   intro.
   decompose [ex and] H10.
   unfold Fresh in H5.
   decompose [and] H5.
   contradiction.

   intro.
   inversion H10.
   decompose [or] H13;
    unfold Fresh in H5;
    decompose [and] H5;
    contradiction.

  apply TVars.WFact.union_iff in H9.
  apply (apply_disjoint_term x) in H4.
  decompose [and] H4.
  decompose [or] H9.
   Dup H12.
   apply H1 in H12.
   apply H10 in H13.
   decompose [and] H12.
   split; auto.
   intro.
   inversion H16.
   decompose [or] H19; contradiction.

   Dup H12.
   apply H3 in H12.
   apply H11 in H13.
   decompose [and] H12.
   split; auto.
   intro.
   inversion H16.
   decompose [or] H19; contradiction.

 apply (if_disjoint_term x) in H6.
 decompose [and] H6.
 rewrite H8 in H9.
 apply TVars.WFact.union_iff in H9.
 decompose [or] H9.
  split; try (apply H1 in H11; tauto).
  Dup H11.
  apply H1 in H11.
  decompose [and] H11.
  apply H10 in H14.
  decompose [and] H14.
  intro.
  inversion H19.
  decompose [or] H22; contradiction.

  apply TVars.WFact.union_iff in H11.
   decompose [or] H11.
   split; (try (apply H3 in H14; tauto)).
   Dup H14.
   apply H3 in H14.
   decompose [and] H14.
   apply H12 in H15.
   decompose [and] H15.
   intro.
   inversion H20.
   decompose [or] H23; contradiction.

   split; try (apply H5 in H14; tauto).
   Dup H14.
   apply H5 in H14.
   decompose [and] H14.
   apply H13 in H15.
   decompose [and] H15.
   intro.
   inversion H20.
   decompose [or] H23; contradiction.
Qed.
