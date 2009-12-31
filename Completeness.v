Require Import List.
Require Import String.
Require Import Sumbool.
Require Import Classical.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.
Require Import TypeSubstFact.

(* Lemma *)

(* for var *)
Lemma var_inv : forall s T S tenv tsubst ,
  Table.MapsTo s S tenv ->
  Solution tsubst T tenv (Var s) ->
  T = type_subst S tsubst.
Proof.
unfold Solution in |- *.
simpl in |- *.
intros.
inversion H0.
unfold tenv_subst in H2.
apply (TableWF.map_mapsto_iff tenv s T (fun T : type => type_subst T tsubst))
 in H2.
inversion H2.
inversion H5.
rewrite H6 in |- *.
assert (x = S).
 apply TableWF.MapsTo_fun with (m := tenv) (x := s); trivial.

 rewrite H8 in |- *.
 reflexivity.
Qed.

(* for lambda *)
Lemma lambda_inv : forall T tenv tsubst x T1 t,
  Solution tsubst T tenv (Lambda x T1 t) ->
  exists T2,
  Solution tsubst T2 (Table.add x T1 tenv) t /\
  T = FunT (type_subst T1 tsubst) T2.
Proof.
unfold Solution in |- *; simpl in |- *.
intros.
inversion H.
exists b.
split.
 unfold tenv_subst in |- *.
 rewrite map_add in |- *.
 trivial.

 reflexivity.
Qed.

Lemma fun_fresh_inv : forall (X : TVars.t) T1 T2,
  (forall x, TVars.In x X -> FreshT x (FunT T1 T2)) ->
  (forall x, TVars.In x X -> FreshT x T1) /\
  (forall x, TVars.In x X -> FreshT x T2).
Proof.
intros.
split; intros;
 apply H in H0;
 inversion H0;
 tauto.
Qed.

Lemma subst_eq : forall T X tsubst1 tsubst2,
  (forall x,TVars.In x X -> FreshT x T) ->
  tsubst1 = sub tsubst2 X ->
  type_subst T tsubst1 = type_subst T tsubst2.
Proof.
induction T; intros; simpl in |- *.
 destruct (TVars.WProp.In_dec s X).
  apply H in i.
  inversion i.
  tauto.

  apply sub_find with (A:=type) (tsubst:=tsubst2) in n.
  rewrite <- n in |- *.
  rewrite H0 in |- *.
  reflexivity.

 reflexivity.

 apply fun_fresh_inv in H.
 decompose [and] H.
 apply (IHT1 _ tsubst1 tsubst2) in H1.
  apply (IHT2 _ tsubst1 tsubst2) in H2.
   rewrite H1 in |- *.
   rewrite H2 in |- *.
   reflexivity.

   trivial.

  trivial.
Qed.

(* for apply *)
Lemma apply_inv: forall T tenv tsubst t1 t2,
  Solution tsubst T tenv (Apply t1 t2) ->
  exists T1,
  Solution tsubst (FunT T1 T) tenv t1 /\ Solution tsubst T1 tenv t2.
Proof.
intros.
inversion H.
exists a.
split; trivial.
Qed.

Definition ApplyTSubst {A : Type} tsubst' X X1 X2 (tsubst tsubst1 tsubst2 : table A) x T :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U tsubst <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U tsubst1 <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U tsubst2 <-> Table.MapsTo Y U tsubst')) /\
  Table.MapsTo x T tsubst'.

Lemma union_filter_intro_1 : forall A (P : string-> Prop) (dec : forall x, {P x} + {~ P x}) k e (X Y : table A),
   P k -> Table.MapsTo k e X ->
   Table.MapsTo k e (union (filter dec X) Y).
Proof.
intros.
apply <- union_iff (* Generic printer *).
left.
apply <- filter_iff (* Generic printer *).
split; trivial.
Qed.

Lemma union_filter_intro_2 : forall A (P : string-> Prop) (dec : forall x, {P x} + {~ P x}) k e (X Y : table A),
   ~ P k -> Table.MapsTo k e Y ->
   Table.MapsTo k e (union (filter dec X) Y).
Proof.
intros.
apply <- union_iff (* Generic printer *).
right.
split.
 unfold Table.In in |- *.
 unfold Table.Raw.PX.In in |- *.
 intro.
 inversion H1.
 apply filter_iff in H2.
 inversion H2.
 contradiction .

 trivial.
Qed.

Lemma x_in_X: forall x y X X1 X2,
  X = TVars.add x (TVars.union X1 X2) ->
  (y = x \/ TVars.In y X1 \/ TVars.In y X2) ->
  TVars.FSet.In y X.
Proof.
intros.
rewrite H in |- *.
decompose [or] H0.
 rewrite H1 in |- *.
 apply <- TVars.WFact.add_iff (* Generic printer *); left; reflexivity.

 apply <- TVars.WFact.add_iff (* Generic printer *); right; apply <-
  TVars.WFact.union_iff (* Generic printer *); left;
  trivial.

 apply <- TVars.WFact.add_iff (* Generic printer *); right; apply <-
  TVars.WFact.union_iff (* Generic printer *); right;
  trivial.
Qed.

Lemma union_filter_elim_2 : forall (A : Type) (P : string -> Prop) (dec : forall x,{ P x } + {~ P x }) k e (X Y : table A),
  ~ P k -> Table.MapsTo k e (union (filter dec X) Y) ->
  Table.MapsTo k e Y.
Proof.
intros.
apply union_iff in H0.
decompose [or] H0.
 apply filter_iff in H1.
 decompose [and] H1.
 contradiction .

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
unfold app in |- *.
unfold ApplyTSubst in |- *.
split; [ idtac | split; [ idtac | split ] ]; intros.
 split; intros.
  apply union_filter_intro_1; trivial.

  apply union_iff in H5.
  inversion H5.
   apply filter_iff in H6.
   tauto.

   inversion H6.
   apply union_filter_elim_2 in H8.
    apply union_filter_elim_2 in H8.
     apply TableWF.add_mapsto_iff in H8.
     inversion H8.
      inversion H9.
      assert False.
       apply H4.
       apply (x_in_X x Y X X1 X2); [ | rewrite H10 ]; tauto.

       contradiction .

      inversion H9.
      inversion H11.

     intro.
     apply H4.
     apply (x_in_X x Y X X1 X2); tauto.

    intro.
    apply H4.
    apply (x_in_X x Y X X1 X2); tauto.

 split; intros.
  apply union_filter_intro_2.
   intro.
   apply H6.
   apply (x_in_X x Y X X1 X2); tauto.

   apply union_filter_intro_1; trivial.

  apply union_filter_elim_2 in H5.
   apply union_iff in H5.
   inversion H5.
    apply filter_iff in H6; tauto.

    inversion H6.
    apply union_filter_elim_2 in H8.
     apply TableWF.add_mapsto_iff in H8.
     inversion H8.
      inversion H9.
      rewrite <- H10 in H4.
      contradiction.

      inversion H9.
      inversion H11.

     apply TVars.disjoint_left with (X := X1).
      trivial.

      trivial.

   intro.
   apply H6.
   apply (x_in_X x Y X X1 X2); tauto.

 split; intros.
  apply union_filter_intro_2.
   intro.
   apply H6.
   apply (x_in_X x Y X X1 X2); tauto.

   apply union_filter_intro_2.
    apply TVars.disjoint_left with (X := X2).
     apply TVars.disjoint_sym.
     trivial.

     trivial.

    apply union_filter_intro_1; tauto.

  apply union_filter_elim_2 in H5.
   apply union_filter_elim_2 in H5.
    apply union_iff in H5.
    inversion H5.
     apply filter_iff in H6.
     tauto.

     inversion H6.
     apply TableWF.add_mapsto_iff in H8.
     inversion H8.
      inversion H9.
      rewrite <- H10 in H4.
      contradiction.

      inversion H9.
      inversion H11.

    apply TVars.disjoint_left with (X := X2).
     apply TVars.disjoint_sym.
     trivial.

     trivial.

   intro.
   apply H6.
   apply (x_in_X x Y X X1 X2); tauto.

 apply union_filter_intro_2.
  intro.
  apply H4.
  apply (x_in_X x x X X1 X2); tauto.

  apply union_filter_intro_2.
   trivial.

   apply union_filter_intro_2.
    trivial.

    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    left.
    split; reflexivity.
Qed.

(*Lemma ApplyTSubst_sub : forall A (tsubst' tsubst tsubst1 tsubst2 : table A)X X1 X2 x T,
  ~ TVars.In x X1 -> ~ TVars.In x X2 ->   Disjoint tsubst X ->
  X = TVars.add x (TVars.union X1 X2) ->
  ApplyTSubst tsubst' X X1 X2 tsubst tsubst1 tsubst2 x T ->
  tsubst = sub tsubst' X.
Proof.
intros.
apply Extensionality_Table.
apply <- TableWF.Equal_mapsto_iff (* Generic printer *).
split; intros.
*)

(* main theorem *)
(*Theorem completeness: forall t tenv Ts S T X C tsubst1,
  TypeConstraint t tenv Ts S X C ->
  TypeSubst.Solution tsubst1 T tenv t ->
  Disjoint tsubst1 X ->
  exists tsubst2,
    tsubst1 = sub tsubst2 X /\
    Constraint.Solution tsubst2 T tenv Ts t S C.
Proof.
intros until tsubst1.
intro.
generalize T.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; unfold Constraint.Solution in |- *; simpl in |- *;
 intros.
 exists tsubst1.
 split.
  apply sub_empty.

  exists TVars.empty.
  split.
   apply CTVar.
   trivial.

   split.
    apply Unified_empty.

    apply var_inv with (S := T0) in H1.
     trivial.

     trivial.

 apply lambda_inv in H2.
 decompose [ex] H2.
 decompose [and] H4.
 apply H1 in H5.
  decompose [ex] H5.
  decompose [and] H7.
  exists x1.
  split.
   trivial.

   exists X0.
   split.
    apply CTLambda.
    trivial.

    split.
     decompose [ex] H9.
     tauto.

     assert (type_subst T1 tsubst1 = type_subst T1 x1).
      apply subst_eq with (X := X0).
       intros.
       apply tvars_free with (x := x2) in H0.
        decompose [and] H0.
        unfold FreshTs in H11.
        apply H11.
        apply in_eq.

        trivial.

       trivial.

      rewrite H6 in |- *.
      rewrite H10 in |- *.
      decompose [ex] H9.
      decompose [and] H11.
      rewrite H15 in |- *.
      trivial.

  trivial.

 exists tsubst1.
 split.
  apply sub_empty.

  exists TVars.empty.
  split.
   apply CTBool.

   split.
    apply Unified_empty.

    inversion H0.
    reflexivity.

 apply apply_inv in H11.
 decompose [ex] H11.
 decompose [and] H13.
 apply H1 in H14.
  apply H3 in H15.
   decompose [ex] H14; decompose [ex] H15.
   decompose [and] H16; decompose [and] H17.
   exists
    (ApplyTSubst (TVars.add x (TVars.union X1 X2)) X1 X2 tsubst1 x1 x2 x T0).
   split.
    apply ApplyTSubst_sub.
     unfold Fresh in H9.
     tauto.

     unfold Fresh in H9.
     tauto.

     trivial.

     reflexivity.

    exists (TVars.add x (TVars.union X1 X2)).
    split.
     apply CTApply with (T1 := T1) (T2 := T2) (C1 := C1) (C2 := C2); trivial.

     split.
*)
