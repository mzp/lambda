Require Import List.
Require Import Ensembles.
Require Import String.

Require Import Typing.
Require Import Tables.
Require Import Sets.
Require Import Term.
Require Import TypeSubst.

Definition tconst := set (type * type).
Definition tvars := set string.

Definition Unified (c : tconst) (t : tsubst) := forall S T,
  In (S,T) c -> type_subst S t = type_subst T t.

Definition FvTConst x c := forall S T,
  In (S,T) c -> FvT x S \/ FvT x T.

Definition FvTable x tenv := forall y T,
  Table.MapsTo y T tenv -> FvT x T.

Definition DisjointFV xs T := forall x,
  (FvT x T -> ~ In x xs) /\ (In x xs -> ~ FvT x T).

Definition Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 :=
  ~ In x X1  /\ ~ In x X2 /\
  ~ FvT x T1 /\ ~ FvT x T2 /\
  ~ FvTConst x C1 /\ ~ FvTConst x C2 /\
  ~ FvTable x tenv /\
  ~ FvTt x t1 /\ ~ FvTt x t2.

Inductive TypeConstraint : term -> tenv -> type -> tvars -> tconst -> Prop :=
  CTVar : forall s tenv T X C,
    Table.MapsTo s T tenv ->
    TypeConstraint (Var s) tenv T X C
| CTLambda : forall x T1 T2 t tenv X C,
    TypeConstraint t (Table.add x T1 tenv) T2 X C ->
    TypeConstraint (Lambda x T1 t) tenv (FunT T1 T2) X C
| CTBool : forall b tenv X C,
    TypeConstraint (Bool b) tenv BoolT X C
| CTApply : forall x t1 t2 T1 T2 tenv X1 X2 X C1 C2 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    Disjoint X1 X2 -> DisjointFV X2 T1 -> DisjointFV X1 T2 ->
    X = Add x (Union X1 X2) ->
    Fresh x X1 X2 T1 T2 C1 C2 tenv t1 t2 ->
    C = Add (T1,FunT T2 (VarT x)) (Union C1 C2) ->
    TypeConstraint (Apply t1 t2) tenv (VarT x) X C
| CTIf : forall t1 t2 t3 T1 T2 T3 tenv X1 X2 X3 X C1 C2 C3 C,
    TypeConstraint t1 tenv T1 X1 C1 ->
    TypeConstraint t2 tenv T2 X2 C2 ->
    TypeConstraint t3 tenv T3 X3 C3 ->
    X = Union X1 (Union X2 X3) ->
    Disjoint X1 X2 -> Disjoint X2 X3 -> Disjoint X3 X1 ->
    C = Add (T1,BoolT) (Add (T2,T3) (Union C1 (Union C2 C3))) ->
    TypeConstraint (If t1 t2 t3) tenv T2 X C.

Definition Solution tsubst T tenv t S C := exists X,
  TypeConstraint t tenv S X C /\ Unified C tsubst /\ T = type_subst S tsubst.

Lemma Unified_Union : forall C1 C2 tsubst,
  Unified (Union C1 C2) tsubst -> Unified C1 tsubst.
Proof.
unfold Unified in |- *.
unfold In in |- *.
intros.
apply H.
unfold Union in |- *.
apply Union_introl.
trivial.
Qed.

Lemma Unified_Add : forall c C tsubst,
  Unified (Add c C) tsubst -> Unified C tsubst.
Proof.
unfold Add in |- *.
intros.
apply Unified_Union with (C2 := Singleton (type * type) c).
trivial.
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
 Solution tsubst S tenv (Apply t1 t2) T (Add (T1,FunT T2 T) (Union C1 C2)) ->
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
 unfold In in |- *; unfold Add in |- *.
 unfold Ensembles.Add in |- *.
 apply Union_intror.
 apply In_singleton.

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
    rewrite union_sym in |- *.
    apply Unified_Add with (c := (T1, FunT T2 T)).
    trivial.

    reflexivity.
Qed.

Lemma if_solution_inv : forall t1 t2 t3 S T1 T2 T3 X1 X2 X3 C1 C2 C3 tenv tsubst,
  TypeConstraint t1 tenv T1 X1 C1 ->
  TypeConstraint t2 tenv T2 X2 C2 ->
  TypeConstraint t3 tenv T3 X3 C3 ->
  Solution tsubst S tenv (If t1 t2 t3) T2
                  (Sets.Add (T1, BoolT)
                            (Sets.Add (T2, T3)
                                      (Sets.Union C1 (Sets.Union C2 C3)))) ->
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
   apply (Unified_Union C1 (Union C2 C3) tsubst).
   apply Unified_Add with (c := (T2, T3)).
   apply Unified_Add with (c := (T1, BoolT)).
   trivial.

   unfold Unified in H6.
   change BoolT with (type_subst BoolT tsubst) in |- *.
   apply sym_eq.
   apply H6.
   unfold In in |- *; unfold Add in |- *; unfold Union in |- *.
   unfold Ensembles.Add in |- *.
   apply Union_intror.
   apply In_singleton.

 split.
  exists X2.
  split.
   trivial.

   split.
    apply (Unified_Union C2 C3 tsubst).
    apply (Unified_Union (Union C2 C3) C1 tsubst).
    rewrite union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    trivial.

  exists X3.
  split.
   trivial.

   split.
    apply (Unified_Union C3 C2).
    rewrite union_sym in |- *.
    apply (Unified_Union _ C1).
    rewrite union_sym in |- *.
    apply Unified_Add with (c := (T2, T3));
     apply Unified_Add with (c := (T1, BoolT)).
    trivial.

    rewrite H7 in |- *.
    unfold Unified in H6.
    apply H6.
    unfold In in |- *; unfold Add in |- *; unfold Union in |- *.
    unfold Ensembles.Add in |- *.
    apply Union_introl.
    apply Union_intror.
    apply In_singleton.
Qed.
