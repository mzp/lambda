Require Import List.
Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TVars.
Require Import TypeSubst.
Require Import TVarsSub.
Require Import String.

Definition Maps A := list ((string -> bool) * table A).

Definition Union {A : Type} m' (ms : Maps A) := forall k e P p m,
  In (p,m) ms -> prop_bool P p -> P k ->
  (Table.MapsTo k e m' <-> Table.MapsTo k e m).

Definition Disjoint {A : Type} (ms : Maps A) := forall i j m1 m2 p1 p2 P Q,
  i <> j ->
  Some (p1,m1) = List.nth_error ms i ->
  Some (p2,m2) = List.nth_error ms j ->
  prop_bool P p1 ->
  prop_bool Q p2 ->
  (forall x, P x -> ~ Q x) /\ (forall x, Q x -> ~ P x).

Lemma cons_disjoint : forall A m (ms : Maps A),
  Disjoint (m::ms) -> Disjoint ms.
Proof.
unfold Disjoint.
intros.
apply (H (1+i)%nat (1+j)%nat m1 m2 p1 p2); auto.
Qed.

Lemma ex_union : forall A ms,
  Disjoint ms ->
  exists m' : table A, Union m' ms.
Proof.
induction ms; intros.
 exists (empty A).
 unfold Union.
 Split.
  inversion H3.

  inversion H0.

 apply cons_disjoint in H; auto.
 apply IHms in H.
 decompose [ex] H.
 destruct a.
 exists (union (filter_bool b t) x).
 unfold Union.
 Split.
  inversion H1.
   inversion H5.
   rewrite H7,H8 in H4.
   apply union_iff in H4.
   decompose [and or] H4.
    apply filter_bool_iff in H6; try tauto.
    apply H2.

    UnfoldIn H9.
    assert False.
     apply H9.

     apply <- filter_bool_iff.
     split.
      apply H10.
