Require Import String.
Require Import FSets.FMapWeakList.
Require Import FSets.FMapInterface.
Require Import FSets.FMapFacts.
Require Import Logic.DecidableType.

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

Lemma add_1 : forall (t : Type) (A : table t) x r1 r2,
  Table.add x r1 (Table.add x r2 A) = Table.add x r1 A.
Proof.
intros.
apply Extensionality_Table.
apply
 (TableWF.Equal_mapsto_iff (Table.add x r1 (Table.add x r2 A)) (Table.add x r1 A)).
 (* Table.MapsTo k e (Table.add y r1 (Table.add y r2 tenv)) ->
    Table.MapsTo k e (Table.add y r1 tenv) *)
split.
 intros.
 apply TableWF.add_mapsto_iff in H.
 decompose [or] H.
  (* k = y *)
  inversion H0.
  rewrite H1 in |- *.
  rewrite H2 in |- *.
  apply Table.add_1.
  reflexivity.

  (* k <> y *)
  decompose [and] H0.
  apply Table.add_2.
   trivial.

   apply Table.add_3 in H2; trivial.

 (* Table.MapsTo k e (Table.add y r1 tenv) ->
    Table.MapsTo k e (Table.add y r1 (Table.add y r2 tenv)) *)
 intros.
 apply TableWF.add_mapsto_iff in H.
 decompose [or] H.
  (* k = y *)
  inversion H0.
  rewrite H1 in |- *.
  rewrite H2 in |- *.
  apply Table.add_1.
  reflexivity.

  (* k <> y *)
  inversion H0.
  apply Table.add_2.
   trivial.

   apply Table.add_2; trivial.
Qed.

Lemma add_2 : forall (t : Type) (A : table t) x y r1 r2,
  x <> y -> Table.add x r1 (Table.add y r2 A) = Table.add y r2 (Table.add x r1 A).
Proof.
intros.
apply Extensionality_Table.
apply
 (TableWF.Equal_mapsto_iff (Table.add x r1 (Table.add y r2 A))
                           (Table.add y r2 (Table.add x r1 A))).
split.
 intros.
 apply TableWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = x *)
  inversion H1.
  rewrite H2 in |- *.
  rewrite H3 in |- *.
  rewrite H2 in H.
  apply Table.add_2.
   apply sym_not_eq.
   trivial.

   apply Table.add_1.
   reflexivity.

  (* k <> x*)
  decompose [and] H1.
  apply TableWF.add_mapsto_iff in H3.
  decompose [or] H3.
   (* y = k*)
   inversion H4.
   rewrite H5 in |- *; rewrite H6 in |- *.
   apply Table.add_1.
   reflexivity.

   (* y <> k *)
   decompose [and] H4.
   apply Table.add_2.
    trivial.

    apply Table.add_2; trivial.

 (* Table.MapsTo k e (Table.add y r2 (Table.add x r1 tenv)) ->
    Table.MapsTo k e (Table.add x r1 (Table.add y r2 tenv)) *)
 intros.
 apply TableWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = y *)
  inversion H1.
  rewrite H2 in |- *; rewrite H3 in |- *.
  rewrite H2 in H.
  apply Table.add_2.
   trivial.

   apply Table.add_1.
   reflexivity.

  (* k <> y *)
  inversion H1.
  apply TableWF.add_mapsto_iff in H3.
  decompose [or] H3.
   (* k = x *)
   inversion H4.
   rewrite H6 in |- *.
   rewrite H5 in |- *.
   apply Table.add_1.
   reflexivity.

   (* k <> x *)
   decompose [and] H4.
   apply Table.add_2.
    trivial.

    apply Table.add_2; trivial.
Qed.
