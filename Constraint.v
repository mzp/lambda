Require Import List.
Require Import Ensembles.
Require Import String.

Require Import Typing.
Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import TypeSubst.
Require Import Dec.

Module TVars  := Sets.Make StrDec.
Module TypePairDec := PairDec TypeDec TypeDec.
Module TConst := Sets.Make TypePairDec.

Definition tvars  := TVars.t.
Definition tconst := TConst.t.

Definition Unified (c : tconst) (t : tsubst) := forall (S T : type),
  TConst.In (S,T) c -> type_subst S t = type_subst T t.

Inductive FreshT : string -> type -> Prop :=
  | FVarT : forall x y, x <> y -> FreshT x (VarT y)
  | FFunT : forall x T1 T2, FreshT x T1 /\ FreshT x T2 -> FreshT x (FunT T1 T2).

Inductive FreshTerm : string -> term -> Prop :=
  | FLambda : forall x y T t, FreshT x T /\ FreshTerm x t -> FreshTerm x (Lambda y T t)
  | FApply  : forall x t1 t2, FreshTerm x t1 /\ FreshTerm x t2 -> FreshTerm x (Apply t1 t2)
  | FIf     : forall x t1 t2 t3, FreshTerm x t1 /\ FreshTerm x t2 \/ FreshTerm x t3 -> FreshTerm x (If t1 t2 t3).

Definition FreshC x c := forall S T,
  TConst.In (S,T) c -> FreshT x S \/ FreshT x T.

Definition FreshE x tenv := forall y T,
  Table.MapsTo y T tenv -> FreshT x T.

Definition DisjointT xs T := forall x,
  TVars.In x xs -> FreshT x T.

Definition FreshTs x Ts := forall T,
  List.In T Ts -> FreshT x T.

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv ts t1 t2 :=
  ~ TVars.In x X1  /\ ~ TVars.In x X2 /\
  FreshT x T1 /\ FreshT x T2 /\
  FreshC x C1 /\ FreshC x C2 /\
  FreshE x tenv /\ FreshTs x ts /\
  FreshTerm x t1 /\ FreshTerm x t2.

Inductive TypeConstraint : term -> tenv -> list type -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv Ts T,
    Table.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv Ts T TVars.empty TConst.empty
| CTLambda : forall x T1 T2 t tenv Ts X C,
    TypeConstraint t (Table.add x T1 tenv) (T1::Ts) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv Ts (FunT T1 T2) X C
| CTBool : forall b tenv Ts,
    TypeConstraint (Bool b) tenv Ts BoolT TVars.empty TConst.empty
| CTApply : forall x t1 t2 T1 T2 tenv Ts X1 X2 C1 C2 C,
    TypeConstraint t1 tenv Ts T1 X1 C1 ->
    TypeConstraint t2 tenv Ts T2 X2 C2 ->
    TVars.Disjoint X1 X2 -> DisjointT X2 T1 -> DisjointT X1 T2 ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv Ts t1 t2 ->
    C = TConst.add (T1,FunT T2 (VarT x)) (TConst.union C1 C2) ->
    TypeConstraint (Apply t1 t2) tenv Ts (VarT x) (TVars.add x (TVars.union X1 X2)) C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv Ts X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv Ts T1 X1 C1 ->
    TypeConstraint t2 tenv Ts T2 X2 C2 ->
    TypeConstraint t3 tenv Ts T3 X3 C3 ->
    X = TVars.union X1 (TVars.union X2 X3) ->
    TVars.Disjoint X1 X2 -> TVars.Disjoint X2 X3 -> TVars.Disjoint X3 X1 ->
    C = TConst.add (T1,BoolT) (TConst.add (T2,T3) (TConst.union C1 (TConst.union C2 C3))) ->
    TypeConstraint (If t1 t2 t3) tenv Ts T2 X C.

Definition Solution tsubst T tenv Ts t S C := exists X,
  TypeConstraint t tenv Ts S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

Lemma Unified_Union : forall C1 C2 tsubst,
  Unified (TConst.union C1 C2) tsubst -> Unified C1 tsubst.
Proof.
unfold Unified in |- *.
intros.
apply H.
apply (TConst.WFact.union_iff C1 C2 _).
left; trivial.
Qed.

Lemma Unified_empty : forall tsubst,
  Unified TConst.empty tsubst.
Proof.
unfold Unified in |- *.
intros.
inversion H.
Qed.

Lemma Unified_Add : forall c C tsubst,
  Unified (TConst.add c C) tsubst -> Unified C tsubst.
Proof.
unfold Unified in |- *.
intros.
apply H.
apply (TConst.WFact.add_iff C c _).
right; trivial.
Qed.

Lemma var_solution_inv : forall T S tenv Ts tsubst x C,
  Solution tsubst T tenv Ts (Var x) S C ->
  Table.MapsTo x T (tenv_subst tenv tsubst).
Proof.
intros.
unfold Solution in H.
inversion H.
inversion H0.
unfold tenv_subst in |- *.
apply
 (TableWF.map_mapsto_iff tenv x T (fun T0 : type => type_subst T0 tsubst)).
inversion H1.
exists S.
inversion H2.
split; trivial.
Qed.

Lemma lambda_solution_inv : forall tsubst T T1 T2 tenv Ts x t C,
  Solution tsubst T tenv Ts (Lambda x T1 t) (FunT T1 T2) C ->
  T = FunT (type_subst T1 tsubst) (type_subst T2 tsubst) /\
  Solution tsubst (type_subst T2 tsubst) (Table.add x T1 tenv) (T1::Ts) t T2 C.
Proof.
unfold Solution in |- *.
intros.
inversion H.
inversion H0.
inversion H1; inversion H2.
split.
 simpl in H13.
 trivial.

 exists x0.
 split; [ trivial | split; [ trivial | reflexivity ] ].
Qed.

Lemma bool_solution_inv : forall tsubst T tenv Ts t C,
  Solution tsubst T tenv Ts t BoolT C ->
  T = BoolT.
Proof.
unfold Solution in |- *.
intros.
inversion H.
inversion H0.
inversion H2.
simpl in H4.
trivial.
Qed.

Lemma apply_solution_inv: forall tsubst tenv Ts t1 t2 T T1 T2 S C1 C2 X1 X2,
 TypeConstraint t1 tenv Ts T1 X1 C1 ->
 TypeConstraint t2 tenv Ts T2 X2 C2 ->
 Solution tsubst S tenv Ts (Apply t1 t2) T (TConst.add (T1,FunT T2 T) (TConst.union C1 C2)) ->
   type_subst T1 tsubst = type_subst (FunT T2 T) tsubst /\
   Solution tsubst (type_subst T1 tsubst) tenv Ts t1 T1 C1 /\
   Solution tsubst (type_subst T2 tsubst) tenv Ts t2 T2 C2.
Proof.
unfold Solution in |- *.
intros.
inversion H1.
inversion H2.
inversion H4.
split.
 unfold Unified in H5.
 apply H5.
 apply (TConst.WFact.add_iff (TConst.union C1 C2) _ _).
 left.
 simpl in |- *.
 split; reflexivity.

 split.
  exists X1.
  split.
   trivial.

   split.
    apply (Unified_Union C1 C2 tsubst).
    apply Unified_Add with (c := (T1, FunT T2 T)).
    trivial.

    reflexivity.

  exists X2.
  split.
   trivial.

   split.
    apply (Unified_Union C2 C1 tsubst).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T1, FunT T2 T)).
    trivial.

    reflexivity.
Qed.

Lemma if_solution_inv : forall t1 t2 t3 S T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv Ts tsubst,
  TypeConstraint t1 tenv Ts T1 X1 C1 ->
  TypeConstraint t2 tenv Ts T2 X2 C2 ->
  TypeConstraint t3 tenv Ts T3 X3 C3 ->
  Solution tsubst S tenv Ts (If t1 t2 t3) T2
                  (TConst.add (T1, BoolT)
                            (TConst.add (T2, T3)
                                      (TConst.union C1 (TConst.union C2 C3)))) ->
  Solution tsubst BoolT tenv Ts t1 T1 C1 /\
  Solution tsubst S tenv Ts t2 T2 C2 /\
  Solution tsubst S tenv Ts t3 T3 C3.
Proof.
unfold Solution in |- *.
intros.
inversion H2.
inversion H3.
inversion H5.
split.
 exists X1.
 split.
  trivial.

  split.
   apply (Unified_Union C1 (TConst.union C2 C3) tsubst).
   apply Unified_Add with (c := (T2, T3)).
   apply Unified_Add with (c := (T1, BoolT)).
   trivial.

   unfold Unified in H6.
   change BoolT with (type_subst BoolT tsubst) in |- *.
   apply sym_eq.
   apply H6.
   apply
    (TConst.WFact.add_iff
       (TConst.add (T2, T3) (TConst.union C1 (TConst.union C2 C3))) _ _).
   left.
   split; reflexivity.

 split.
  exists X2.
  split.
   trivial.

   split.
    apply (Unified_Union C2 C3 tsubst).
    apply (Unified_Union (TConst.union C2 C3) C1 tsubst).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    trivial.

  exists X3.
  split.
   trivial.

   split.
    apply (Unified_Union C3 C2).
    rewrite TConst.union_sym in |- *.
    apply (Unified_Union _ C1).
    rewrite TConst.union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    rewrite H7 in |- *.
    unfold Unified in H6.
    apply H6.
    apply
     (TConst.WFact.add_iff
        (TConst.add (T2, T3) (TConst.union C1 (TConst.union C2 C3))) _ _).
    right.
    apply (TConst.WFact.add_iff (TConst.union C1 (TConst.union C2 C3)) _ _).
    left; split; reflexivity.
Qed.

Lemma empty_add : forall x s,
  TVars.FSet.Raw.empty <> TVars.FSet.Raw.add x s.
Proof.
intros.
unfold TVars.FSet.Raw.empty in |- *.
destruct s; intros; simpl.
 intro.
 inversion H.

 destruct (TVars.WProp.Dec.F.eq_dec x e); intro; inversion H.
Qed.

Lemma tvars_free : forall t X x tenv Ts S C,
  TypeConstraint t tenv Ts S X C ->
  TVars.In x X ->
  FreshTs x Ts /\ FreshTerm x t.
Proof.
intros until C.
intro.
pattern t, tenv, Ts, S, X, C in |- *.
apply TypeConstraint_ind; intros.
 inversion H1.

 apply H1 in H2.
 decompose [and] H2.
 split.
  unfold FreshTs in H3; unfold FreshTs in |- *.
  intros.
  apply H3.
  apply in_cons.
  trivial.

  apply FLambda.
  split.
   unfold FreshTs in H3.
   apply H3.
   apply in_eq.

   trivial.

 inversion H0.


(*
 inversion H1.
 split; intro.
  apply H2.
  apply fv_types_intro.
  trivial.

  inversion H4.
  decompose [or] H7.
   apply fv_types_cons with (Ts := Ts0) in H10.
   apply H2 in H10.
   trivial.

   apply H3.
   trivial.

 split; intros; intro; inversion H1.

 split; intros.
  intro.
  apply TVars.WFact.add_iff in H10.
  inversion H10.
*)
