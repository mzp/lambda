Require Import String.

Require Import Constraint.
Require Import Tables.

Definition app {A B : Type} (f : A -> B) (x : A) := f x.
Infix "$" := app (at level 51, right associativity).

Definition union {A : Type} (tsubst1 tsubst2 : table A) :=
  Table.fold (fun key e m => Table.add key e m) tsubst1 tsubst2.

Definition remove {A : Type} {P : string -> Prop} (dec : forall x, {P x} + {~ P x}) (tsubst : table A) :=
  TableProp.filter
    (fun key _ => if dec key then true else false)
    tsubst.

Lemma union_iff: forall A x (T : A) (X Y : table A),
  Table.MapsTo x T (union X Y) <-> Table.MapsTo x T X \/ (~ Table.In x X /\ Table.MapsTo x T Y).
Proof.
intros.
unfold union in |- *.
pattern X,
 (Table.fold
    (fun (key : Table.key) (e : A) (m : Table.t A) => Table.add key e m) X Y)
 in |- *.
apply TableProp.fold_rec_bis; intros.
 apply Extensionality_Table in H.
 rewrite <- H in |- *.
 trivial.

 split; intros.
  right.
  split.
   intro.
   apply TableWF.empty_in_iff in H0.
   contradiction .

   trivial.

  decompose [or] H.
   inversion H0.

   decompose [and] H0.
   trivial.

 split; intros.
  apply TableWF.add_mapsto_iff in H2.
  decompose [or] H2.
   left.
   decompose [and] H3.
   rewrite H4 in |- *; rewrite H5 in |- *.
   apply <- TableWF.add_mapsto_iff (* Generic printer *).
   left; split; reflexivity.

   decompose [and] H3.
   apply H1 in H5.
   decompose [or] H5.
    left.
    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    right.
    split; trivial.

    decompose [and] H6.
    right.
    split.
     intro.
     apply H7.
     apply TableWF.add_in_iff in H9.
     decompose [or] H9.
      contradiction .

      trivial.

     trivial.

  decompose [or] H2.
   apply TableWF.add_mapsto_iff in H3.
   decompose [or] H3.
    decompose [and] H4.
    rewrite H5 in |- *; rewrite H6 in |- *.
    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    left.
    split; reflexivity.

    decompose [and] H4.
    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    right.
    split.
     trivial.

     apply H1.
     left.
     trivial.

   decompose [and] H3.
   apply <- TableWF.add_mapsto_iff (* Generic printer *).
   right.
   split.
    intro.
    apply H4.
    apply <- TableWF.add_in_iff (* Generic printer *).
    left.
    trivial.

    apply H1.
    right.
    split.
     intro.
     apply H4.
     apply <- TableWF.add_in_iff (* Generic printer *).
     right.
     trivial.

     trivial.
Qed.

Lemma remove_iff : forall A x P (dec : forall x, {P x} + {~ P x}) (T : A) (m : table A),
  Table.MapsTo x T (remove dec m) <-> Table.MapsTo x T m /\ (P x).
Proof.
unfold remove in |- *.
intros; split; intros.
 apply TableProp.filter_iff in H.
  intro.
  unfold Morphisms.respectful in |- *.
  intros.
  rewrite H0 in |- *.
  reflexivity.

  decompose [and] H.
  split.
   trivial.

   destruct (dec x).
    trivial.

    discriminate.

 apply <- TableProp.filter_iff (* Generic printer *).
  decompose [and] H.
  split.
   trivial.

   destruct (dec x).
    reflexivity.

    contradiction .

  unfold Morphisms.Morphism in |- *.
  unfold Morphisms.respectful in |- *.
  intros.
  rewrite H0 in |- *.
  reflexivity.
Qed.
