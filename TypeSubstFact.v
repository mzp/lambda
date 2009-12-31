Require Import String.
Require Import Sumbool.

Require Import Term.
Require Import Constraint.
Require Import Tables.

Definition app {A B : Type} (f : A -> B) (x : A) := f x.
Infix "$" := app (at level 51, right associativity).

Definition union {A : Type} (tsubst1 tsubst2 : table A) :=
  Table.fold (fun key e m => Table.add key e m) tsubst1 tsubst2.

Definition filter {A : Type} {P : string -> Prop} (dec : forall x, {P x} + {~ P x}) (tsubst : table A) :=
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

Lemma filter_iff : forall A x P (dec : forall x, {P x} + {~ P x}) (T : A) (m : table A),
  Table.MapsTo x T (filter dec m) <-> Table.MapsTo x T m /\ (P x).
Proof.
unfold filter in |- *.
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

Definition not_sumbool {P : Prop} : {P} + {~ P} -> {~ P} + {~ ~ P}.
Proof.
intros.
apply sumbool_not.
inversion H.
 left.
 intro.
 contradiction .

 right.
 trivial.
Qed.

Lemma union_elim : forall (A : Type) (P : string -> Prop) x (dec : forall x,{ P x } + {~ P x }) (T : A) tsubst1 tsubst2,
  ~ P x -> Table.MapsTo x T (union (filter dec tsubst1) tsubst2) ->
  Table.MapsTo x T tsubst2.
Proof.
intros.
apply union_iff in H0.
decompose [or] H0.
 apply filter_iff in H1.
 decompose [and] H1.
 contradiction .

 tauto.
Qed.

Definition ApplyTSubst X X1 X2 tsubst tsubst1 tsubst2 x T :=
  union (filter (fun x => not_sumbool $ TVars.WProp.In_dec x X) tsubst) $
  union (filter (fun x => TVars.WProp.In_dec x X1) tsubst1) $
  union (filter (fun x => TVars.WProp.In_dec x X2) tsubst2) $
  Table.add x T (Table.empty type).

Definition sub {A : Type} (tsubst : table A) X :=
  filter (fun x => not_sumbool (TVars.WProp.In_dec x X)) tsubst.

Definition Disjoint {A : Type} (tsubst : table A) tvars := forall x,
  (Table.In x tsubst -> ~ TVars.In x tvars) /\
  (TVars.In x tvars  -> ~ Table.In x tsubst).

Lemma ApplyTSubst_tsubst : forall tsubst tsubst1 tsubst2 X X1 X2 x T,
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
