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

