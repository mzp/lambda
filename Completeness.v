Require Import List.
Require Import String.
Require Import Sumbool.
Require Import Classical.

Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import Constraint.
Require Import TypeSubst.

Definition sub tsubst tvars :=
  TVars.FSet.fold (fun x (table : table type) => Table.remove x table) tvars tsubst.

Lemma sub_find : forall tsubst x X,
  ~ TVars.In x X ->
  Table.find x (sub tsubst X) = Table.find x tsubst.
Proof.
intros.
unfold sub in |- *.
pattern X,
 (TVars.FSet.fold
    (fun (x0 : TVars.FSet.elt) (table : table type) =>
     Table.remove (elt:=type) x0 table) X tsubst) in |- *.
apply TVars.WProp.fold_rec; intros.
 reflexivity.

 rewrite TableWF.remove_o in |- *.
 destruct (TVars.WProp.Dec.F.eq_dec x0 x).
  unfold Dec.StrDec.eq in e.
  rewrite e in H0.
  contradiction .

  rewrite H3 in |- *.
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

  apply (sub_find tsubst2 _ _) in n.
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

Definition Disjoint (tsubst : tsubst) tvars := forall x,
  Table.In x tsubst -> ~ TVars.In x tvars /\
  TVars.In x tvars  -> ~ Table.In x tsubst.

Lemma sub_empty : forall tsubst,
  tsubst = sub tsubst TVars.empty.
Proof.
intro tubst.
reflexivity.
Qed.

(* inversion *)
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

Definition app {A B : Type} (f : A -> B) (x : A) := f x.
Infix "$" := app (at level 51, right associativity).

Definition union {A : Type} {P : string -> Prop} (dec : forall x,{P x} + {~ P x}) (tsubst1 tsubst2 : table A) :=
  Table.fold
    (fun Y U tsubst =>
       if dec Y then Table.add Y U tsubst else tsubst)
    tsubst1 tsubst2.

Definition Not_dec {P : Prop} : {P} + {~ P} -> {~ P} + {~ ~ P}.
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

Lemma union_intro : forall (A : Type) (P : string -> Prop) x (dec : forall x,{ P x } + {~ P x }) (T : A) tsubst1 tsubst2,
  ~ P x ->
  Table.MapsTo x T tsubst2 ->
  Table.MapsTo x T (union dec tsubst1 tsubst2).
Proof.
intros.
unfold union in |- *.
pattern tsubst1,
 (Table.fold
    (fun (Y : Table.key) (U : A) (tsubst : Table.t A) =>
     if dec Y then Table.add Y U tsubst else tsubst) tsubst1 tsubst2)
 in |- *.
apply TableProp.fold_rec_bis; intros.
 trivial.

 trivial.

 destruct (dec k).
  destruct (string_dec x k).
   rewrite e0 in H.
   contradiction .

   apply <- TableWF.add_mapsto_iff (* Generic printer *).
   right.
   split.
    apply sym_not_eq.
    trivial.

    trivial.

  trivial.
Qed.

Definition new_tsubst X tsubst X1 tsubst1 X2 tsubst2 x T :=
  union (fun x => Not_dec $ TVars.WProp.In_dec x X) tsubst $
  union (fun x => TVars.WProp.In_dec x X1) tsubst1 $
  union (fun x => TVars.WProp.In_dec x X2) tsubst2 $
  Table.add x T (Table.empty type).

Lemma new_tsust : forall X tsubst tsubst' X1 tsubst1 X2 tsubst2 x T Y U,
  tsubst' = new_tsubst X tsubst X1 tsubst1 X2 tsubst2 x T ->
  ~ TVars.In Y X ->
  Table.MapsTo Y U tsubst ->
  Table.MapsTo Y U tsubst'.
Proof.
intros.
rewrite H in |- *.
unfold new_tsubst in |- *.
unfold app in |- *.
unfold union at 1 in |- *.
generalize H1.
pattern tsubst,
 (Table.fold
    (fun (Y0 : Table.key) (U0 : type) (tsubst0 : Table.t type) =>
     if Not_dec (TVars.WProp.In_dec Y0 X)
     then Table.add Y0 U0 tsubst0
     else tsubst0) tsubst
    (union (fun x0 : string => TVars.WProp.In_dec x0 X1) tsubst1
       (union (fun x0 : string => TVars.WProp.In_dec x0 X2) tsubst2
          (Table.add x T (Table.empty type))))) in |- *.
apply TableProp.fold_rec_bis; intros.
 apply H3.
 apply Extensionality_Table in H2.
 rewrite H2 in |- *.
 trivial.

 inversion H2.

 destruct (Not_dec (TVars.WProp.In_dec k X)).
  apply <- TableWF.add_mapsto_iff (* Generic printer *).
  destruct (string_dec k Y).
   left.
   split.
    trivial.

    apply TableWF.MapsTo_fun with (m := tsubst) (x := k).
     trivial.

     rewrite e0 in |- *.
     trivial.

   right.
   split.
    trivial.

    apply H4.
    apply TableWF.add_mapsto_iff in H5.
    decompose [or] H5.
     decompose [and] H6.
     contradiction .

     tauto.

  apply H4.
  apply TableWF.add_mapsto_iff in H5.
  decompose [or] H5.
   decompose [and] H6.
   rewrite H7 in n.
   contradiction .

   tauto.
Qed.

Lemma new_tsust1 : forall X tsubst tsubst' X1 tsubst1 X2 tsubst2 x T Y U,
  X = TVars.add x (TVars.union X1 X2) ->
  tsubst' = new_tsubst X tsubst X1 tsubst1 X2 tsubst2 x T ->
  TVars.In Y X1 -> Table.MapsTo Y U tsubst1 -> Table.MapsTo Y U tsubst'.
Proof.
intros.
rewrite H0 in |- *.
unfold new_tsubst in |- *.
unfold app in |- *.
apply union_intro.
 intro.
 apply H3.
 rewrite H in |- *.
 apply <- TVars.WFact.add_iff (* Generic printer *).
 right.
 apply <- TVars.WFact.union_iff (* Generic printer *).
 tauto.

 unfold union at 1 in |- *.
 generalize H2.
 pattern tsubst1,
  (Table.fold
     (fun (Y0 : Table.key) (U0 : type) (tsubst0 : Table.t type) =>
      if TVars.WProp.In_dec Y0 X1 then Table.add Y0 U0 tsubst0 else tsubst0)
     tsubst1
     (union (fun x0 : string => TVars.WProp.In_dec x0 X2) tsubst2
        (Table.add x T (Table.empty type)))) in |- *.
 apply TableProp.fold_rec_bis; intros.
  apply H4.
  apply Extensionality_Table in H3.
  rewrite H3 in |- *.
  trivial.

  inversion H3.

  destruct (TVars.WProp.In_dec k X1).
   apply TableWF.add_mapsto_iff in H6.
   decompose [or] H6.
    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    left.
    tauto.

    apply <- TableWF.add_mapsto_iff (* Generic printer *).
    right.
    split.
     tauto.

     apply H5.
     tauto.

   apply H5.
   apply TableWF.add_mapsto_iff in H6.
   decompose [or] H6.
    decompose [and] H7.
    rewrite H8 in n.
    contradiction .

    tauto.
Qed.

(* /\
  (forall Y U,
  (forall Y U, TVars.In Y X2 -> Table.MapsTo Y U tsubst -> Table.MapsTo Y U tsubst') /\
  Table.MapsTo x T tsubst'.*)

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

 apply apply_inv in H11.
 decompose [ex] H11.
 decompose [and] H13.
 apply H1 in H14.
  apply H3 in H15.
   decompose [ex] H14; decompose [ex] H15.
   decompose [and] H16; decompose [and] H17.



(*
  apply apply_inv in H11.
  decompose [ex] H11.
  decompose [and] H14.
  apply H1 in H15.
   apply H3 in H16.
    decompose [ex] H15; decompose [ex] H16.
    decompose [and] H17; decompose [and] H18.
    split.
     rewrite H10 in |- *.
     apply Unified_Add_intro.
      apply Unified_Union_intro; trivial.

      unfold Unified in |- *.
      intros.
      apply TConst.WFact.singleton_iff in H23.
*)
