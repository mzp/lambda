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

Lemma ApplyTSubst_sym : forall A X X1 X2 (s tsubst tsubst1 tsubst2 : table A) x T ,
   ApplyTSubst s X X1 X2 tsubst tsubst1 tsubst2 x T ->
   ApplyTSubst s X X2 X1 tsubst tsubst2 tsubst1 x T.
Proof.
unfold ApplyTSubst in |- *.
intros.
decompose [and] H.
split; [ idtac | split; [ idtac | split ] ]; intros.
 apply H0.
 trivial.

 apply H1.
 trivial.

 apply H2.
 trivial.

 trivial.
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

Lemma not_x_sub_eq : forall A (tsubst' tsubst : table A) X,
  Disjoint tsubst X ->
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U tsubst <-> Table.MapsTo Y U tsubst')) ->
  tsubst = sub tsubst' X.
Proof.
intros.
apply Extensionality_Table.
apply <- TableWF.Equal_mapsto_iff (* Generic printer *).
split; intros.
 destruct (TVars.WProp.In_dec k X).
  unfold Disjoint in H.
  specialize (H k).
  decompose [and] H.
  apply H3 in i.
  assert False.
   apply i.
   unfold Table.In in |- *.
   unfold Table.Raw.PX.In in |- *.
   exists e.
   trivial.

   contradiction .

  unfold sub in |- *.
  apply <- filter_iff (* Generic printer *); auto.
  split; auto.
  apply H0 with (U := e) in n.
  apply n.
  trivial.

 unfold sub in H1.
 apply filter_iff in H1.
 decompose [and] H1.
 apply H0 with (U := e) in H3.
 apply H3; trivial.
Qed.

Lemma ApplyTSubst_sub : forall A (tsubst' tsubst tsubst1 tsubst2 : table A)X X1 X2 x T,
  ~ TVars.In x X1 -> ~ TVars.In x X2 ->   Disjoint tsubst X ->
  X = TVars.add x (TVars.union X1 X2) ->
  ApplyTSubst tsubst' X X1 X2 tsubst tsubst1 tsubst2 x T ->
  tsubst = sub tsubst' X.
Proof.
unfold ApplyTSubst in |- *.
intros.
decompose [and] H3.
apply not_x_sub_eq; auto.
Qed.

Lemma ApplyTSubst_subst_eq: forall s X X1 X2 tsubst tsubst1 tsubst2 x S T,
  ApplyTSubst s X X1 X2 tsubst tsubst1 tsubst2 x S ->
  tsubst = sub tsubst1 X1 ->
  (forall x, UseT x T -> ~ TVars.In x X1 -> ~ TVars.In x X) ->
  type_subst T s = type_subst T tsubst1.
Proof.
intros.
unfold ApplyTSubst in H.
decompose [and] H.
induction T; auto.
 destruct (TVars.WProp.In_dec s0 X1).
  apply mapsto_type_subst.
  intro.
  apply iff_sym.
  apply H4.
  trivial.

  assert (type_subst (VarT s0) tsubst = type_subst (VarT s0) s).
   apply mapsto_type_subst.
   intro.
   apply H2.
   apply H1.
    apply UVarT.

    trivial.

   assert (type_subst (VarT s0) tsubst = type_subst (VarT s0) tsubst1).
    rewrite H0 in |- *.
    apply type_subst_sub.
    trivial.

    rewrite <- H5 in |- *; rewrite H7 in |- *.
    reflexivity.

 simpl in |- *.
 rewrite IHT1 in |- *.
  rewrite IHT2 in |- *.
   reflexivity.

   intros.
   apply H1; auto.
   apply UFunT.
   right; trivial.

  intros.
  apply H1; auto.
  apply UFunT.
  left.
  trivial.
Qed.

Lemma ApplyTSubst_unified: forall s X X1 X2 tsubst tsubst1 tsubst2 x S C,
  ApplyTSubst s X X1 X2 tsubst tsubst1 tsubst2 x S ->
  tsubst = sub tsubst1 X1 ->
  (forall x, UseC x C -> ~ TVars.In x X1 -> ~ TVars.In x X) ->
  Unified C tsubst1 ->
  Unified C s.
Proof.
unfold Unified in |- *; intros.
assert (type_subst S0 s = type_subst S0 tsubst1).
 apply (ApplyTSubst_subst_eq s X X1 X2 tsubst tsubst1 tsubst2 x S); auto.
 intros.
 apply H1; auto.
 unfold UseC in |- *.
 exists S0; exists T.
 split; tauto.

 assert (type_subst T s = type_subst T tsubst1).
  apply (ApplyTSubst_subst_eq s X X1 X2 tsubst tsubst1 tsubst2 x S); auto.
  intros.
  apply H1; auto.
  unfold UseC in |- *.
  exists S0; exists T.
  split; tauto.

  rewrite H4 in |- *; rewrite H5 in |- *.
  apply H2.
  trivial.
Qed.

Lemma not_in_disjoint: forall A (Y : A) (Fresh Use : string -> A -> Prop) x y X1 X2 ,
  (forall x, Use x Y -> ~ Fresh x Y) ->
  Fresh x Y -> Use y Y ->
  (forall x , TVars.In x X2 -> Fresh x Y) ->
  ~ TVars.In y X1 ->
  ~ TVars.In y (TVars.add x (TVars.union X1 X2)).
Proof.
intros.
intro.
apply H3.
apply TVars.WFact.add_iff in H4.
decompose [or] H4.
 rewrite H5 in H0.
 apply H in H1.
 contradiction .

 apply TVars.WFact.union_iff in H5.
 decompose [or] H5; auto.
 apply H2 in H6.
 apply H in H1.
 contradiction .
Qed.

Lemma not_in_disjoint_t: forall x y T X1 X2,
  FreshT x T -> UseT y T ->
  DisjointT X2 T ->
  ~ TVars.In y X1 ->
  ~ TVars.In y (TVars.add x (TVars.union X1 X2)).
Proof.
intros.
apply (not_in_disjoint _ T FreshT UseT); auto.
intros.
apply use_t_not_fresh.
trivial.
Qed.

Lemma not_in_disjoint_c: forall x y C X1 X2,
  FreshC x C -> UseC y C ->
  DisjointC X2 C ->
  ~ TVars.In y X1 ->
  ~ TVars.In y (TVars.add x (TVars.union X1 X2)).
Proof.
intros.
apply (not_in_disjoint _ C FreshC UseC); auto.
intros.
apply use_c_not_fresh.
trivial.
Qed.

Lemma disjoint_union: forall A (tsubst : table A) X1 X2,
  Disjoint tsubst (TVars.union X1 X2) ->
  Disjoint tsubst X1.
Proof.
unfold Disjoint in |- *.
intros.
specialize (H x).
decompose [and] H.
split; intros.
 apply H0 in H2.
 intro.
 apply H2.
 apply <- TVars.WFact.union_iff (* Generic printer *).
 tauto.

 apply H1.
 apply <- TVars.WFact.union_iff (* Generic printer *).
 tauto.
Qed.

Lemma disjoint_add: forall A (tsubst : table A) x X,
  Disjoint tsubst (TVars.add x X) ->
  Disjoint tsubst X.
Proof.
unfold Disjoint in |- *.
intros.
specialize (H x0).
decompose [and] H.
split; intros.
 apply H0 in H2.
 intro.
 apply H2.
 apply <- TVars.WFact.add_iff (* Generic printer *).
 tauto.

 apply H1.
 apply <- TVars.WFact.add_iff (* Generic printer *).
 tauto.
Qed.

Lemma if_inv: forall tsubst T tenv t1 t2 t3,
  Solution tsubst T tenv (If t1 t2 t3) ->
  Solution tsubst BoolT tenv t1 /\
  Solution tsubst T tenv t2 /\
  Solution tsubst T tenv t3.
Proof.
unfold Solution in |- *.
intros.
inversion H.
auto.
Qed.

Definition IfTSubst {A : Type} tsubst' X X1 X2 X3 (tsubst tsubst1 tsubst2 tsubst3: table A) :=
  (forall Y U, ~ TVars.In Y X  ->
    (Table.MapsTo Y U tsubst <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X1 ->
    (Table.MapsTo Y U tsubst1 <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X2 ->
    (Table.MapsTo Y U tsubst2 <-> Table.MapsTo Y U tsubst')) /\
  (forall Y U,   TVars.In Y X3 ->
    (Table.MapsTo Y U tsubst3 <-> Table.MapsTo Y U tsubst')).

Lemma ex_IfTSubst : forall A X X1 X2 X3 (tsubst tsubst1 tsubst2 tsubst3 : table A),
  Disjoint tsubst X ->
  TVars.Disjoint X1 X2 ->
  TVars.Disjoint X2 X3 ->
  TVars.Disjoint X3 X1 ->
  X = TVars.union X1 (TVars.union X2 X3) ->
  exists s : table A, IfTSubst s X X1 X2 X3 tsubst tsubst1 tsubst2 tsubst3.
Proof.
intros.
exists
 (union (filter (fun x => not_sumbool $ TVars.WProp.In_dec x X) tsubst) $
  union (filter (fun x => TVars.WProp.In_dec x X1) tsubst1) $
  union (filter (fun x => TVars.WProp.In_dec x X2) tsubst2) $
  filter (fun x => TVars.WProp.In_dec x X3) tsubst3).
unfold app in |- *.
unfold IfTSubst in |- *.
split; [ idtac | split; [ idtac | split ] ]; split; intros.
 apply union_filter_intro_1; trivial.

 apply union_iff in H5.
 decompose [or] H5.
  apply filter_iff in H6.
  tauto.

  decompose [and] H6.
  apply union_filter_elim_2 in H8.
   apply union_filter_elim_2 in H8.
    apply filter_iff in H8.
    decompose [and] H8.
    assert False.
     apply H4.
     rewrite H3 in |- *.
     apply <- TVars.WFact.union_iff (* Generic printer *).
     right.
     apply <- TVars.WFact.union_iff (* Generic printer *).
     tauto.

     contradiction .

    intro.
    apply H4.
    rewrite H3 in |- *.
    apply <- TVars.WFact.union_iff (* Generic printer *).
    right.
    apply <- TVars.WFact.union_iff (* Generic printer *).
    tauto.

   intro.
   apply H4.
   rewrite H3 in |- *.
   apply <- TVars.WFact.union_iff (* Generic printer *).
   tauto.

 apply union_filter_intro_2.
  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.

  apply union_filter_intro_1.
   trivial.

   trivial.

 apply union_filter_elim_2 in H5.
  apply union_iff in H5.
  decompose [or] H5.
   apply filter_iff in H6.
   tauto.

   decompose [and] H6.
   apply union_filter_elim_2 in H8.
    apply filter_iff in H8.
    decompose [and] H8.
    apply TVars.disjoint_left with (x := Y) in H2; auto.
    contradiction .

    apply TVars.disjoint_left with (X := X1); auto.

  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.

 apply union_filter_intro_2.
  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  right.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.

  apply union_filter_intro_2.
   apply TVars.disjoint_left with (X := X2).
    apply TVars.disjoint_sym.
    tauto.

    tauto.

   apply union_filter_intro_1; tauto.

 apply union_filter_elim_2 in H5.
  apply union_filter_elim_2 in H5.
   apply union_iff in H5.
   decompose [or] H5.
    apply filter_iff in H6.
    tauto.

    decompose [and] H6.
    apply filter_iff in H8.
    decompose [and] H8.
    apply TVars.disjoint_left with (x := Y) in H1; auto.
    contradiction .

   apply TVars.disjoint_left with (X := X2).
    apply TVars.disjoint_sym.
    tauto.

    tauto.

  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  right.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.

 apply union_filter_intro_2.
  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  right.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.

  apply union_filter_intro_2.
   apply TVars.disjoint_left with (X := X3); auto.

   apply union_filter_intro_2.
    apply TVars.disjoint_left with (X := X3).
     apply TVars.disjoint_sym.
     trivial.

     trivial.

    apply <- filter_iff (* Generic printer *).
    tauto.

 apply union_filter_elim_2 in H5.
  apply union_filter_elim_2 in H5.
   apply union_filter_elim_2 in H5.
    apply filter_iff in H5.
    tauto.

    apply TVars.disjoint_left with (X := X3).
     apply TVars.disjoint_sym.
     tauto.

     tauto.

   apply TVars.disjoint_left with (X := X3); auto.

  intro.
  apply H6.
  rewrite H3 in |- *.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  right.
  apply <- TVars.WFact.union_iff (* Generic printer *).
  tauto.
Qed.

Lemma IfTSubst_sub : forall A (tsubst' tsubst tsubst1 tsubst2 tsubst3: table A)X X1 X2 X3,
  Disjoint tsubst X ->
  X = TVars.union X1 (TVars.union X2 X3) ->
  IfTSubst tsubst' X X1 X2 X3 tsubst tsubst1 tsubst2 tsubst3->
  tsubst = sub tsubst' X.
Proof.
unfold IfTSubst in |- *.
intros.
decompose [and] H1.
apply not_x_sub_eq; auto.
Qed.

(* main theorem *)
Theorem completeness: forall t tenv Ts S T X C tsubst1,
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

 apply apply_inv in H13.
 decompose [ex] H13.
 decompose [and] H15.
 apply H1 in H16.
  apply H3 in H17.
   decompose [ex] H16; decompose [ex] H17.
   decompose [and] H18; decompose [and] H19.
   assert
    (exists s : _,
       ApplyTSubst s (TVars.add x (TVars.union X1 X2)) X1 X2 tsubst1 x1 x2 x
         T0).
    unfold Fresh in H11.
    decompose [and] H11.
    apply ex_ApplyTSubst; trivial.

    decompose [ex] H24.
    exists x3.
    split.
     unfold Fresh in H11.
     decompose [and] H11.
     apply
      ApplyTSubst_sub
       with
         (tsubst1 := x1)
         (tsubst2 := x2)
         (X1 := X1)
         (X2 := X2)
         (x := x)
         (T := T0); trivial.

     exists (TVars.add x (TVars.union X1 X2)).
     split.
      apply CTApply with (T1 := T1) (T2 := T2) (C1 := C1) (C2 := C2); trivial.

      split.
       rewrite H12 in |- *.
       apply Unified_Add_intro.
        apply Unified_Union_intro.
         apply
          (ApplyTSubst_unified x3 (TVars.add x (TVars.union X1 X2)) X1 X2
             tsubst1 x1 x2 x T0 _); auto.
          intros.
          apply not_in_disjoint_c with (C := C1); auto.
          unfold Fresh in H11.
          tauto.

          decompose [ex] H21.
          tauto.

         apply
          (ApplyTSubst_unified x3 (TVars.add x (TVars.union X1 X2)) X2 X1
             tsubst1 x2 x1 x T0 _); auto.
          apply ApplyTSubst_sym.
          trivial.

          intros.
          rewrite TVars.union_sym in |- *.
          apply not_in_disjoint_c with (C := C2); auto.
          unfold Fresh in H11.
          tauto.

          decompose [ex] H23.
          tauto.

        unfold Unified in |- *.
        intros.
        apply TConst.WFact.singleton_iff in H26.
        simpl in H26.
        decompose [and] H26.
        assert (type_subst T1 x3 = type_subst T1 x1).
         apply
          (ApplyTSubst_subst_eq x3 (TVars.add x (TVars.union X1 X2)) X1 X2
             tsubst1 x1 x2 x T0); auto.
         intros.
         apply not_in_disjoint_t with (T := T1); auto.
         unfold Fresh in H11.
         tauto.

         assert (type_subst T2 x3 = type_subst T2 x2).
          apply
           (ApplyTSubst_subst_eq x3 (TVars.add x (TVars.union X1 X2)) X2 X1
              tsubst1 x2 x1 x T0); auto.
           apply ApplyTSubst_sym.
           trivial.

           intros.
           rewrite TVars.union_sym in |- *.
           apply not_in_disjoint_t with (T := T2); auto.
           unfold Fresh in H11.
           tauto.

          rewrite <- H27 in |- *.
          decompose [ex] H21.
          decompose [and] H31.
          rewrite H29 in |- *.
          rewrite <- H35 in |- *.
          rewrite <- H28 in |- *.
          simpl in |- *.
          rewrite H30 in |- *.
          decompose [ex] H23.
          decompose [and] H33.
          rewrite <- H39 in |- *.
          unfold ApplyTSubst in H25.
          decompose [and] H25.
          apply TableWF.find_mapsto_iff in H43.
          rewrite H43 in |- *.
          reflexivity.

       unfold ApplyTSubst in H25.
       decompose [and] H25.
       apply TableWF.find_mapsto_iff in H30.
       rewrite H30 in |- *.
       reflexivity.

   apply disjoint_add in H14.
   rewrite TVars.union_sym in H14.
   apply disjoint_union in H14.
   trivial.

  apply disjoint_add in H14.
  apply disjoint_union in H14.
  trivial.

 apply if_inv in H16.
 decompose [and] H16.
 apply H1 in H18.
  apply H3 in H20.
   apply H5 in H21.
    decompose [ex] H18.
    decompose [ex] H20.
    decompose [ex] H21.
    assert
     (exists s : _,
        IfTSubst s (TVars.union X1 (TVars.union X2 X3)) X1 X2 X3 tsubst1 x x0
          x1).
     apply ex_IfTSubst; auto.

     decompose [ex] H24.
     exists x2.
     split.
      apply IfTSubst_sub in H25; auto.

      exists (TVars.union X1 (TVars.union X2 X3)).
      split.
       apply CTIf with (T1 := T1) (T3 := T3) (C1 := C1) (C2 := C2) (C3 := C3);
        auto.

       split.
        rewrite H15 in |- *.
        apply Unified_Add_intro.
         apply Unified_Add_intro.
          apply Unified_Union_intro.

