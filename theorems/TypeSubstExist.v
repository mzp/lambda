Require Import Util.
Require Import Tables.
Require Import Term.
Require Import TVars.
Require Import TypeSubst.
Require Import TVarsSub.

Definition Include {A : Type} (m' m : table A) P := forall k e,
  Table.MapsTo k e m' <-> (P k /\ Table.MapsTo k e m).

Lemma ex_include : forall A P (dec : forall x, {P x} + {~ P x}) (m : table A),
  exists m', Include m' m P.
Proof.
intros.
exists (filter dec m).
unfold Include, app.
split; intros.
 apply filter_iff in H.
 tauto.

 apply <- filter_iff.
 tauto.
Qed.

Definition ApplyTSubst {A : Type} m' X X1 X2 (m m1 m2: table A) x T :=
  Include m' m  (fun y => ~ TVars.In y X) /\
  Include m' m1 (fun y => TVars.In y X1)  /\
  Include m' m2 (fun y => TVars.In y X2)  /\
  Include m' (Table.add x T (empty A)) (fun y => x = y).

Lemma ex_include_and: forall A P (Q : Prop) (m' m : table A),
  Q ->
  exists m',
    Include m' m P /\ Q.
Proof.
intros.

Lemma ex_ApplyTSubst : forall A X X1 X2 (tsubst tsubst1 tsubst2 : table A) x T ,
  Disjoint tsubst X ->
  ~ TVars.In x X1 -> ~ TVars.In x X2 ->
  TVars.Disjoint X1 X2 ->
  X = TVars.add x (TVars.union X1 X2) ->
  exists s : table A, ApplyTSubst s X X1 X2 tsubst tsubst1 tsubst2 x T.
Proof.
intros.



Definition ApplyTSubst {A : Type} m' X X1 X2 (m m1 m2: table A) x T :=
  Union m' (fun x => ~ TVars.In x X) m.

(*  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U tsubst <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U tsubst1 <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U tsubst2 <-> Table.MapsTo Y U tsubst')) /\
  Table.MapsTo x T tsubst'.

*)