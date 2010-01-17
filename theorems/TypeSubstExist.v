Require Import List.
Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TVars.
Require Import TypeSubst.
Require Import TVarsSub.
Require Import String.

Definition ApplyTSubst {A : Type} tsubst' X X1 X2 (tsubst tsubst1 tsubst2 : table A) x T :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U tsubst <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U tsubst1 <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U tsubst2 <-> Table.MapsTo Y U tsubst')) /\
  Table.MapsTo x T tsubst'.

Lemma union_in : forall A k (m1 m2 : table A),
  Table.In k (union m1 m2) <-> Table.In k m1 \/ Table.In k m2.
Proof.
split; intros.
 UnfoldIn H.
 apply union_iff in H0.
 decompose [or and] H0.
  left.
  unfold Table.In, Table.Raw.PX.In.
  exists x.
  tauto.

  right.
  unfold Table.In, Table.Raw.PX.In.
  exists x.
  tauto.

 decompose [or] H.
  UnfoldIn H0.
  unfold Table.In, Table.Raw.PX.In.
  exists x.
  apply <- union_iff.
  tauto.

  destruct (TableWF.In_dec m1 k).
   UnfoldIn i.
   unfold Table.In, Table.Raw.PX.In.
   exists x.
   apply <- union_iff.
   tauto.

   UnfoldIn H0.
   unfold Table.In, Table.Raw.PX.In.
   exists x.
   apply <- union_iff.
   tauto.
Qed.

Lemma union_assoc: forall A (m1 m2 m3 : table A),
  union m1 (union m2 m3) = union (union m1 m2) m3.
Proof.
intros.
apply equal_ind; intros.
 apply union_iff in H.
 decompose [or and] H.
  apply <- union_iff.
  left.
  apply <- union_iff.
  tauto.

  apply union_iff in H2.
  decompose [or and] H2.
  apply <- union_iff.
  left.
  apply <- union_iff.
  tauto.

  apply <- union_iff.
  right.
  split; auto.
  intro.
  apply union_in in H0.
  decompose [or] H0; contradiction.

 apply union_iff in H.
 decompose [and or] H.
  apply union_iff in H0.
  decompose [and or] H0.
   apply <- union_iff.
   tauto.

   apply <- union_iff.
   right.
   split; auto.
   apply <- union_iff.
   tauto.

 apply <- union_iff.
 right.
 split.
  Contrapositive H1.
  apply <- union_in.
  tauto.

  apply <- union_iff.
  right.
  split; auto.
  Contrapositive H1.
  apply <- union_in.
  tauto.
Qed.

Lemma ex_ApplyTSubst : forall A X X1 X2 (tsubst tsubst1 tsubst2 : table A) x T ,
  ~ TVars.In x X1 -> ~ TVars.In x X2 -> Disjoint tsubst X ->
  TVars.Disjoint X1 X2 ->
  X = TVars.add x (TVars.union X1 X2) ->
  exists s : table A, ApplyTSubst s X X1 X2 tsubst tsubst1 tsubst2 x T.
Proof.
intros.
exists
 (union (filter (fun x => not_sumbool $ TVars.WProp.In_dec x X) tsubst) $
  union (filter (fun x => TVars.WProp.In_dec x X1) tsubst1) $
  union (filter (fun x => TVars.WProp.In_dec x X2) tsubst2) $
  Table.add x T (Table.empty A)).
unfold app,ApplyTSubst in |- *.
split; [ idtac | split; [ idtac | split ] ]; try (split; intros).
 apply <- union_iff.
 left.
 apply <- filter_iff.
 tauto.

 apply union_iff in H5.
 decompose [or] H5.
  apply filter_iff in H6.
  tauto.