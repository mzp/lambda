Require Import Classical_Prop.
Require Import List.
Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TVars.
Require Import TypeSubst.
Require Import TVarsSub.
Require Import String.

Definition merge {A P} (dec : forall x, {P x} + {~ P x}) (m1 m2 : table A) :=
  union (filter dec m1) $ filter (fun y => not_sumbool $ dec y) m2.

Lemma filter_in: forall A P (dec : forall x, {P x} + {~ P x}) (m : table A) k,
  Table.In k (filter dec m) -> P k.
Proof.
intros.
UnfoldIn H.
apply filter_iff in H0.
tauto.
Qed.

Lemma merge_iff : forall A P (dec : forall x, {P x} + {~ P x}) (m1 m2 : table A) k e,
 Table.MapsTo k e (merge dec m1 m2) <-> (P k /\ Table.MapsTo k e m1) \/ (~ P k /\ Table.MapsTo k e m2).
unfold merge, app.
split; intros.
 apply union_iff in H.
 decompose [and or] H.
  apply filter_iff in H0.
  tauto.

  apply filter_iff in H2.
  tauto.

 apply <- union_iff.
 decompose [and or] H.
  left.
  apply <- filter_iff.
  tauto.

  right.
  split.
   Contrapositive H1.
   apply filter_in in H0.
   assumption.

   apply <- filter_iff.
   tauto.
Qed.

Lemma merge_sym: forall A P (dec : forall x, {P x} + {~ P x}) (m1 m2 : table A),
  merge dec m1 m2 = merge (fun x => not_sumbool $ dec x) m2 m1.
Proof.
intros.
apply equal_ind; intros.
 apply <- merge_iff.
 apply merge_iff in H.
 tauto.

 apply <- merge_iff.
 apply merge_iff in H.
 decompose [and or] H; auto.
 apply NNPP in H1.
 tauto.
Qed.

Lemma disjoint_merge: forall A P Q
                            (dec1 : forall x, {P x} + {~ P x})
                            (dec2 : forall x, {Q x} + {~ Q x})
                            (m1 m2 m3 : table A),
  (forall x, P x -> ~ Q x) ->
  (forall x, Q x -> ~ P x) ->
  merge dec1 m1 (merge dec2 m2 m3) = merge dec2 m2 (merge dec1 m1 m3).
Proof.
intros.
apply equal_ind; intros.
 apply <- merge_iff.
 apply merge_iff in H1.
 decompose [and or] H1.
  right.
  split; (try (apply H; assumption)).
  apply <- merge_iff.
  tauto.

  apply merge_iff in H4.
  decompose [and or] H4; auto.
  right.
  split; auto.
  apply <- merge_iff.
  tauto.

 apply <- merge_iff.
 apply merge_iff in H1.
 decompose [and or] H1.
  right.
  split; (try (apply H0; assumption)).
  apply <- merge_iff.
  tauto.

  apply merge_iff in H4.
  decompose [and or] H4; auto.
  right.
  split; auto.
  apply <- merge_iff.
  right.
  tauto.
Qed.

Definition ApplyMaps {A : Type} m' X X1 X2 (m m1 m2 : table A) x T :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U m <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U m1 <-> Table.MapsTo Y U m')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U m2 <-> Table.MapsTo Y U m')) /\
  Table.MapsTo x T m'.


Lemma not_in: forall x X,
  ~ TVars.FSet.In x X ->
  (forall y : string, TVars.FSet.In x X -> x <> y).
Proof.
intros.
Contrapositive H.
tauto.
Qed.


Lemma ex_ApplyMaps : forall A X X1 X2 (m m1 m2 : table A) x T ,
 TVars.Disjoint X1 X2 ->
 (forall x0, TVars.FSet.In x0 X1 -> TVars.FSet.In x0 X) ->
 (forall x0, TVars.FSet.In x0 X2 -> TVars.FSet.In x0 X) ->
 (forall x0 : string, ~ TVars.FSet.In x0 X -> x <> x0) ->
 (forall x0 : string, x = x0 -> TVars.FSet.In x0 X) ->
 (forall x0 : string, TVars.FSet.In x0 X1 -> x <> x0) ->
 (forall x0 : string, x = x0 -> ~ TVars.FSet.In x0 X1) ->
 (forall x0 : string, TVars.FSet.In x0 X2 -> x <> x0) ->
 (forall x0 : string, x = x0 -> ~ TVars.FSet.In x0 X2) ->
 TVars.FSet.In x X -> ~ TVars.FSet.In x X1  -> ~ TVars.FSet.In x X2 ->
  exists s : table A, ApplyMaps s X X1 X2 m m1 m2 x T.
Proof.
intros.
rewrite TVars.disjoint_iff in H.
decompose [and] H.
exists
 (merge  (fun y => not_sumbool $ TVars.WProp.In_dec y X) m $
   merge (fun y => TVars.WProp.In_dec y X1) m1 $
   merge (fun y => TVars.WProp.In_dec y X2) m2 $
   merge (fun y => string_dec x y) (Table.add x T (Table.empty A)) $
         Table.empty A).

unfold ApplyMaps,app.
split; [ idtac | split; [ idtac | split ] ]; intros; (try (split; intro MH)).
 apply <- merge_iff.
 tauto.

 apply merge_iff in MH.
 decompose [or and] MH; [ assumption | contradiction ].

 rewrite disjoint_merge; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH;
  [ assumption | contradiction ].

 rewrite disjoint_merge with (m1:=m1) (m2:=m2); auto.
 rewrite disjoint_merge; auto.
 apply <- merge_iff.
 tauto.

 rewrite disjoint_merge with (m1:=m1) (m2:=m2) in MH; auto.
 rewrite disjoint_merge in MH; auto.
 apply merge_iff in MH.
 decompose [and or] MH;
  [ assumption | contradiction ].

 rewrite disjoint_merge with (m1 := m2) (m2 := Table.add x T (Table.empty A)); auto.
 rewrite disjoint_merge with (m1 := m1) (m2 := Table.add x T (Table.empty A)); auto.
 rewrite disjoint_merge; auto.
 apply <- merge_iff.
 left.
 split; auto.
 apply <- TableWF.add_mapsto_iff.
 tauto.
Qed.
