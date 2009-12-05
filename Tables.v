Require Import String.
Require Import FMapWeakList.
Require Import FMapInterface.
Require Import FMapFacts.
Require Import DecidableType.

Module StrDec : DecidableType
    with Definition t := string
    with Definition eq := fun (x y : string) => x = y.
  Definition t := string.
  Definition eq_dec := string_dec.
  Definition eq (x y : string) := x = y.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    unfold eq.
    intros.
    reflexivity.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    unfold eq.
    apply sym_eq.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq.
    apply trans_eq.
  Qed.
End StrDec.

Module Table := FMapWeakList.Make StrDec.
Module TableWF := FMapFacts.WFacts_fun StrDec Table.
Module TableProp := WProperties_fun StrDec Table.

Definition table t := Table.t t.
Definition empty t := Table.empty t.

Axiom Extensionality_Table : forall (t : Type) (A B : table t),
   Table.Equal A B -> A = B.

Lemma equal_ind : forall (t : Type) A B,
 (forall k (e : t), Table.MapsTo k e A -> Table.MapsTo k e B) ->
 (forall k (e : t), Table.MapsTo k e B -> Table.MapsTo k e A) ->
 A = B.
Proof.
intros.
apply Extensionality_Table.
apply (TableWF.Equal_mapsto_iff A B).
split.
 apply H.

 apply H0.
Qed.

Lemma add_1 : forall (t : Type) (A : table t) x r1 r2,
  Table.add x r1 (Table.add x r2 A) = Table.add x r1 A.
Proof.
intros.
apply equal_ind.
 intros.
 apply TableWF.add_mapsto_iff in H.
 decompose [or] H.
  inversion H0.
  rewrite H1 in |- *.
  rewrite H2 in |- *.
  apply Table.add_1.
  reflexivity.

  decompose [and] H0.
  apply Table.add_2.
   trivial.

   apply Table.add_3 in H2; trivial.

 intros.
 apply TableWF.add_mapsto_iff in H.
 decompose [or] H.
  inversion H0.
  rewrite H1 in |- *.
  rewrite H2 in |- *.
  apply Table.add_1.
  reflexivity.

  inversion H0.
  apply Table.add_2.
   trivial.

   apply Table.add_2; trivial.
Qed.

Lemma add_2 : forall (t : Type) (A : table t) x y r1 r2,
  x <> y -> Table.add x r1 (Table.add y r2 A) = Table.add y r2 (Table.add x r1 A).
Proof.
intros.
apply equal_ind.
 intros.
 apply TableWF.add_mapsto_iff in H0.
 inversion H0.
  inversion H1.
  rewrite H2 in |- *.
  rewrite H3 in |- *.
  apply Table.add_2.
   apply sym_not_eq.
   rewrite <- H2.
   trivial.

   apply Table.add_1.
   reflexivity.

  decompose [and] H1.
  apply TableWF.add_mapsto_iff in H3.
  decompose [or] H3.
   inversion H4.
   rewrite H5 in |- *; rewrite H6 in |- *.
   apply Table.add_1.
   reflexivity.

   decompose [and] H4.
   apply Table.add_2.
    trivial.

    apply Table.add_2; trivial.

 intros.
 apply TableWF.add_mapsto_iff in H0.
 decompose [or] H0.
  inversion H1.
  rewrite H2 in |- *; rewrite H3 in |- *.
  apply Table.add_2.
   trivial.
   inversion H1.
   decompose [or] H3.
   inversion H4.
   decompose [and] H4.
   trivial.

   rewrite <- H6.
   trivial.

   apply Table.add_1.
   reflexivity.

  inversion H1.
  apply TableWF.add_mapsto_iff in H3.
  decompose [or] H3.
   inversion H4.
   rewrite H6 in |- *.
   rewrite H5 in |- *.
   apply Table.add_1.
   reflexivity.

   decompose [and] H4.
   apply Table.add_2.
    trivial.

    apply Table.add_2; trivial.
Qed.

Lemma map_add : forall (A : Type) (f : A -> A) x T table,
  Table.map f (Table.add x T table) = Table.add x (f T) (Table.map f table).
Proof.
intros.
apply equal_ind.
 intros.
 apply TableWF.map_mapsto_iff in H.
 inversion H.
 inversion H0.
 apply TableWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H3.
  rewrite H4 in |- *.
  rewrite H5 in |- *.
  rewrite H1 in |- *.
  apply Table.add_1.
  reflexivity.

  inversion H3.
  apply Table.add_2.
   trivial.

   apply (TableWF.map_mapsto_iff table0 k e f).
   exists x0.
   split.
    trivial.

    trivial.

 intros.
 apply TableWF.add_mapsto_iff in H.
 apply (TableWF.map_mapsto_iff (Table.add x T table0) k e f).
 inversion H.
  inversion H0.
  exists T.
  split.
   rewrite H2 in |- *.
   reflexivity.

   apply Table.add_1.
   trivial.

  inversion H0.
  apply (TableWF.map_mapsto_iff table0 k e f) in H2.
  inversion H2.
  inversion H3.
  exists x0.
  split.
   trivial.

   apply Table.add_2.
    trivial.

    trivial.
Qed.
