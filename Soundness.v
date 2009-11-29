Require Import List.
Require Import String.

Require Import Term.
Require Import Typing.
Require Import Constraint.
Require Import TypeSubst.

Definition Subset {A : Type} (xs ys : list A) := forall e,
   In e ys -> In e xs.

Lemma tvars_intro: forall t tenv T X1 X C,
   TypeConstraint t tenv T X1 C -> Subset X1 X ->
   TypeConstraint t tenv T X C.
Proof.
induction t.
 intros.
 inversion H.
 apply CTVar.
 trivial.

 intros.
 inversion H.
 apply CTBool.

 intros.
 inversion H.
 apply CTLambda.
 apply IHt with (X1 := X1).
  trivial.

  trivial.


(*Lemma apply_solution: forall tsubst tenv x T T1 T2 S1 S2 t1 t2 C,
  Constraint.Solution tsubst T tenv (Apply t1 t2) (VarT x) C ->
  TypeSubst T1 S1 tsubst ->
  TypeSubst T2 S2 tsubst ->
  (exists C1, Constraint.Solution tsubst S1 tenv t1 T1 C1) /\
  (exists C2, Constraint.Solution tsubst S2 tenv t2 T2 C2).*)

Lemma lambda_solution: forall tsubst T S T1 T2 tenv x t C,
  Constraint.Solution tsubst T tenv (Lambda x T1 t) (FunT T1 T2) C ->
  TypeSubst T2 S tsubst ->
  Constraint.Solution tsubst S (TEnv.add x T1 tenv) t T2 C.
Proof.
unfold Constraint.Solution in |- *.
intros.
specialize (H X).
inversion H.
split.
 inversion H1.
 exact H10.

 inversion H2.
 split.
  exact H3.

  exact H0.
Qed.

Lemma lambda_intro : forall T1 T2 S1 tsubst tenv x t,
  TypeSubst T1 S1 tsubst ->
  Solution tsubst T2 (TEnv.add x T1 tenv) t ->
  Solution tsubst (FunT S1 T2) tenv (Lambda x T1 t).
Proof.
unfold Solution in |- *.
intros.
inversion H2.
assert (S = S1).
 apply subst_uniq with (T := T1) (tsubst := tsubst).
  exact H8.

  exact H.

 rewrite H10 in |- *.
 apply TLambda.
 apply H0.
  apply subst_add.
   exact H1.

   exact H.

  exact H9.
Qed.

(*
Theorem soundness : forall tenv t T S C tsubst,
  TypeConstraint t tenv S nil C ->
  Constraint.Solution tsubst T tenv t S C ->
  TypeSubst.Solution tsubst T tenv t.
Proof.
intros until tsubst.
intro.
generalize T.
pattern t, tenv, S, (nil:tvars), C in |- *.
apply TypeConstraint_ind.
 (* var *)
 unfold Solution in |- *.
 intros.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Var s) (tenv1 := tenv0) (T := T0).
  apply TVar.
  trivial.

  trivial.

  trivial.

  unfold Constraint.Solution in H1.
  specialize (H1 nil).
  inversion H1.
  inversion H5.
  trivial.

 (* lambda *)
 intros.
 generalize H2; intro.
 unfold Constraint.Solution in H3.
 specialize (H3 X).
 inversion H3.
 inversion H5.
 inversion H7.
 apply lambda_solution with (S := S2) in H2.
  trivial.
  apply H1 in H2.
  apply lambda_intro.
   trivial.

   trivial.

  trivial.

  (* bool *)
 unfold Solution in |- *.
 unfold Constraint.Solution in |- *.
 intros.
 specialize (H0 nil).
 inversion H0.
 inversion H4.
 inversion H6.
 apply
  subst_preserve
   with (tsubst := tsubst) (t := Bool b) (tenv1 := tenv0) (T := BoolT).
  apply TBool.

  trivial.

  trivial.

  apply SBoolT.
*)
