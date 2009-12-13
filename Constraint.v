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

Definition FvTConst x c := forall S T,
  TConst.In (S,T) c -> FvT x S \/ FvT x T.

Definition FvTable x tenv := forall y T,
  Table.MapsTo y T tenv -> FvT x T.

Definition DisjointFV xs T := forall x,
  (FvT x T -> ~ TVars.In x xs) /\ (TVars.In x xs -> ~ FvT x T).

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 :=
  ~ TVars.In x X1  /\ ~ TVars.In x X2 /\
  ~ FvT x T1 /\ ~ FvT x T2 /\
  ~ FvTConst x C1 /\ ~ FvTConst x C2 /\
  ~ FvTable x tenv /\
  ~ FvTt x t1 /\ ~ FvTt x t2.

Inductive TypeConstraint : term -> tenv -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv T,
    Table.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv T TVars.empty TConst.empty
| CTLambda : forall x T1 T2 t tenv X C,
    TypeConstraint t (Table.add x T1 tenv) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv (FunT T1 T2) X C
| CTBool : forall b tenv,
    TypeConstraint (Bool b) tenv BoolT  TVars.empty TConst.empty
| CTApply : forall x t1 t2 T1 T2 tenv X1 X2 C1 C2 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    TVars.Disjoint X1 X2 -> DisjointFV X2 T1 -> DisjointFV X1 T2 ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 ->
    C = TConst.add (T1,FunT T2 (VarT x)) (TConst.union C1 C2) ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) (TVars.add x (TVars.union X1 X2)) C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = TVars.union X1 (TVars.union X2 X3) ->
    TVars.Disjoint X1 X2 -> TVars.Disjoint X2 X3 -> TVars.Disjoint X3 X1 ->
    C = TConst.add (T1,BoolT) (TConst.add (T2,T3) (TConst.union C1 (TConst.union C2 C3))) ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

Definition Solution tsubst T tenv t S C := exists X,
  TypeConstraint t tenv S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

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

Lemma var_solution_inv : forall T S tenv tsubst x C,
  Solution tsubst T tenv (Var x) S C ->
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

Lemma lambda_solution_inv : forall tsubst T T1 T2 tenv x t C,
  Solution tsubst T tenv (Lambda x T1 t) (FunT T1 T2) C ->
  T = FunT (type_subst T1 tsubst) (type_subst T2 tsubst) /\
  Solution tsubst (type_subst T2 tsubst) (Table.add x T1 tenv) t T2 C.
Proof.
unfold Solution in |- *.
intros.
inversion H.
inversion H0.
inversion H1; inversion H2.
split.
 simpl in H12.
 trivial.

 exists x0.
 split; [ trivial | split; [ trivial | reflexivity ] ].
Qed.

Lemma bool_solution_inv : forall tsubst T tenv t C,
  Solution tsubst T tenv t BoolT C ->
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

Lemma apply_solution_inv: forall tsubst tenv t1 t2 T T1 T2 S C1 C2 X1 X2,
 TypeConstraint t1 tenv T1 X1 C1 ->
 TypeConstraint t2 tenv T2 X2 C2 ->
 Solution tsubst S tenv (Apply t1 t2) T (TConst.add (T1,FunT T2 T) (TConst.union C1 C2)) ->
   type_subst T1 tsubst = type_subst (FunT T2 T) tsubst /\
   Solution tsubst (type_subst T1 tsubst) tenv t1 T1 C1 /\
   Solution tsubst (type_subst T2 tsubst) tenv t2 T2 C2.
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

Lemma if_solution_inv : forall t1 t2 t3 S T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv tsubst,
  TypeConstraint t1 tenv T1 X1 C1 ->
  TypeConstraint t2 tenv T2 X2 C2 ->
  TypeConstraint t3 tenv T3 X3 C3 ->
  Solution tsubst S tenv (If t1 t2 t3) T2
                  (TConst.add (T1, BoolT)
                            (TConst.add (T2, T3)
                                      (TConst.union C1 (TConst.union C2 C3)))) ->
  Solution tsubst BoolT tenv t1 T1 C1 /\
  Solution tsubst S tenv t2 T2 C2 /\
  Solution tsubst S tenv t3 T3 C3.
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

Lemma tvars_free : forall X x t tenv S C,
  TypeConstraint t tenv S X C ->
  FvTable x tenv -> ~ TVars.In x X.
Proof.
intro.
pattern X in |- *.
apply TVars.WProp.set_induction_bis; intros.
 apply TVars.Extensionality_Set in H.
 rewrite <- H in |- *.
 rewrite <- H in H1.
 apply (H0 x t tenv S C); trivial.

 intro.
 inversion H1.

 induction t.
  inversion H1.
