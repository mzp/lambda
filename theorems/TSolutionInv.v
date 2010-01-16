Require Import Tables.
Require Import Term.
Require Import TypeSubst.
Require Import Solution.

Ltac Prepare H :=
  unfold TSolution, tenv_subst in |- *;
  simpl;
  intros;
  inversion H.

Lemma var_inv : forall tsubst T tenv s S,
  TSolution tsubst T tenv (Var s) ->
  Table.MapsTo s S tenv ->
  T = type_subst S tsubst.
Proof.
Prepare H.
apply TableWF.map_mapsto_iff in H2.
decompose [ex and] H2.
assert (x = S).
 apply TableWF.MapsTo_fun with (m := tenv) (x := s);
 tauto.

 rewrite <- H5.
 assumption.
Qed.

Lemma lambda_inv : forall tsubst T tenv x T1 t,
  TSolution tsubst T tenv (Lambda x T1 t) ->
  exists T2,
    TSolution tsubst T2 (Table.add x T1 tenv) t /\
    T = FunT (type_subst T1 tsubst) T2.
Proof.
Prepare H.
exists S.
split;
 [ rewrite map_add | ];
 tauto.
Qed.

Lemma apply_inv: forall tsubst T tenv t1 t2,
  TSolution tsubst T tenv (Apply t1 t2) ->
  exists T1,
    TSolution tsubst (FunT T1 T) tenv t1 /\
    TSolution tsubst T1 tenv t2.
Proof.
Prepare H.
exists S.
tauto.
Qed.

Lemma if_inv: forall tsubst T tenv t1 t2 t3,
  TSolution tsubst T tenv (If t1 t2 t3) ->
   TSolution tsubst BoolT tenv t1 /\
   TSolution tsubst T tenv t2 /\
   TSolution tsubst T tenv t3.
Proof.
Prepare H.
tauto.
Qed.
