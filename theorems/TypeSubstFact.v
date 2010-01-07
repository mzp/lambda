Require Import String.
Require Import Sumbool.

Require Import Term.
Require Import Constraint.
Require Import Tables.
Require Import TypeSubst.

Definition app {A B : Type} (f : A -> B) (x : A) := f x.
Infix "$" := app (at level 51, right associativity).

Definition union {A : Type} (tsubst1 tsubst2 : table A) :=
  Table.fold (fun key e m => Table.add key e m) tsubst1 tsubst2.

Definition filter {A : Type} {P : string -> Prop} (dec : forall x, {P x} + {~ P x}) (tsubst : table A) :=
  TableProp.filter
    (fun key _ => if dec key then true else false)
    tsubst.

Lemma mapsto_type_subst: forall x tsubst1 tsubst2,
 (forall U,Table.MapsTo x U tsubst1 <-> Table.MapsTo x U tsubst2) ->
 type_subst (VarT x) tsubst1 = type_subst (VarT x) tsubst2.
Proof.
intros.
simpl in |- *.
destruct (TableWF.In_dec tsubst1 x).
 unfold Table.In in i.
 unfold Table.Raw.PX.In in i.
 decompose [ex] i.
 generalize H0.
 intro.
 apply H in H1.
 apply TableWF.find_mapsto_iff in H0.
 apply TableWF.find_mapsto_iff in H1.
 rewrite H0 in |- *; rewrite H1 in |- *.
 reflexivity.

 assert (~ Table.In (elt:=type) x tsubst2).
  intro; apply n.
  unfold Table.In in H0.
  unfold Table.Raw.PX.In in H0.
  decompose [ex] H0.
  unfold Table.In in |- *.
  unfold Table.Raw.PX.In in |- *.
  exists x0.
  apply <- H (* Generic printer *).
  trivial.

  apply TableWF.not_find_mapsto_iff in n.
  apply TableWF.not_find_mapsto_iff in H0.
  rewrite n in |- *; rewrite H0 in |- *.
  reflexivity.
Qed.

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


Definition sub {A : Type} (tsubst : table A) X :=
  filter (fun x => not_sumbool (TVars.WProp.In_dec x X)) tsubst.

Definition Disjoint {A : Type} (tsubst : table A) tvars := forall x,
  (Table.In x tsubst -> ~ TVars.In x tvars) /\
  (TVars.In x tvars  -> ~ Table.In x tsubst).


Lemma sub_empty : forall A (tsubst : table A),
  tsubst = sub tsubst TVars.empty.
Proof.
intros.
apply Extensionality_Table.
apply <- TableWF.Equal_mapsto_iff (* Generic printer *).
split; intros.
 unfold sub in |- *.
 apply <- filter_iff (* Generic printer *).
 split.
  trivial.

  intro.
  inversion H0.

 unfold sub in H.
 apply filter_iff in H.
 tauto.
Qed.

Lemma sub_find : forall A (tsubst : table A) x X,
  ~ TVars.In x X ->
  Table.find x (sub tsubst X) = Table.find x tsubst.
Proof.
intros.
destruct (TableWF.In_dec tsubst x).
 assert (exists a : _, Table.find (elt:=A) x tsubst = Some a).
  apply TableWF.in_find_iff in i.
  destruct (Table.find (elt:=A) x tsubst).
   exists a; reflexivity.

   tauto.

  inversion H0.
  rewrite H1 in |- *.
  apply (TableWF.find_mapsto_iff (sub tsubst X) _ _).
  unfold sub in |- *.
  apply <- filter_iff (* Generic printer *).
  split.
   apply TableWF.find_mapsto_iff in H1.
   trivial.

   trivial.

 apply TableWF.not_find_mapsto_iff in n.
 rewrite n in |- *.
 apply (TableWF.not_find_mapsto_iff (sub tsubst X) x).
 unfold Table.In in |- *; unfold sub in |- *.
 unfold Table.Raw.PX.In in |- *.
 intro.
 inversion H0.
 apply filter_iff in H1.
 inversion H1.
 apply TableWF.find_mapsto_iff in H2.
 rewrite n in H2.
 discriminate.
Qed.

Lemma type_subst_sub : forall (tsubst : tsubst) x X,
  ~ TVars.In x X ->
  type_subst (VarT x) (sub tsubst X) =  type_subst (VarT x) tsubst.
Proof.
intros.
unfold sub.
apply mapsto_type_subst.
split; intros.
 apply filter_iff in H0.
 tauto.

 apply <- filter_iff (* Generic printer *).
 tauto.
Qed.
