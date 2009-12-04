Require Import List.
Require Import String.

Require Import Tables.
Require Import Term.

Definition tenv := table type.
Definition empty := Table.empty type.

Inductive Typed : term -> tenv -> type -> Prop :=
  | TVar    : forall (tenv : tenv) (s : string) (ty : type),
                Table.MapsTo s ty tenv -> Typed (Var s) tenv ty
  | TBool   : forall (tenv : tenv) (b : bool) ,
                Typed (Bool b) tenv BoolT
  | TLambda : forall (tenv : tenv) (x : string) (a b : type) (body : term),
                Typed body (Table.add x a tenv) b -> Typed (Lambda x a body) tenv (FunT a b)
  | TApply  : forall (tenv : tenv) (t1 t2 : term) (a b : type),
                Typed t1 tenv (FunT a b) -> Typed t2 tenv a -> Typed (Apply t1 t2) tenv b
  | TIf     : forall (tenv : tenv) (t1 t2 t3 : term) (ty : type),
                Typed t1 tenv BoolT -> Typed t2 tenv ty -> Typed t3 tenv ty ->
                   Typed (If t1 t2 t3) tenv ty.

Lemma add_elim: forall t S T tenv s,
    ~ FV s t -> Typed t (Table.add s S tenv) T -> Typed t tenv T.
Proof.
intro.
induction t.
 intros.
 inversion H0.
 apply TVar.
 apply TableWF.add_mapsto_iff in H2.
 inversion H2; inversion H5.
  assert (FV s0 (Var s)).
   rewrite H6 in |- *.
   apply FVVar.

   contradiction.

  inversion H5.
  exact H7.

 intros.
 inversion H0.
 apply TBool.

 intros.
 inversion H0.
 apply TLambda.
 destruct (string_dec s s0).
  rewrite <- (add_1 _ tenv0 s t S) in |- *.
  rewrite <- e in H6.
  trivial.

  apply IHt with (S := S) (s := s0).
   apply FV_Lambda_inv with (y := s) (T := t).
    apply sym_not_eq.
    trivial.

    trivial.

   apply (add_2 _ tenv0 s s0 t S) in n.
   rewrite <- n in |- *.
   trivial.

 intros.
 inversion H0.
 apply TApply with (a := a).
  apply IHt1 with (S := S) (s := s).
   apply FV_Apply_inv_1 with (t2 := t2).
   trivial.

   trivial.

  apply IHt2 with (S := S) (s := s).
   apply FV_Apply_inv_2 with (t1 := t1).
    trivial.

    trivial.

 intros.
 inversion H0.
 apply TIf.
  apply IHt1 with (S := S) (s := s).
   apply FV_If_inv_1 with (t2 := t2) (t3 := t3).
   trivial.

   trivial.

  apply IHt2 with (S := S) (s := s).
   apply FV_If_inv_2 with (t1 := t1) (t3 := t3).
   trivial.

   trivial.


  apply IHt3 with (S := S) (s := s).
   apply FV_If_inv_3 with (t1 := t1) (t2 := t2).
   trivial.

   trivial.

Qed.

Lemma add_intro: forall t S T tenv s,
    ~ FV s t -> ~ BV s t -> Typed t tenv T -> Typed t (Table.add s S tenv) T.
Proof.
induction t.
 intros.
 apply TVar.
 apply Table.add_2.
  intro; apply H.
  rewrite H2 in |- *.
  apply FVVar.

  inversion H1.
  trivial.

 intros.
 inversion H1.
 apply TBool.

 intros.
 inversion H1.
 apply TLambda.
 assert (s <> s0).
  intro.
  apply H0.
  rewrite H8 in |- *.
  apply BVLambda1.

  generalize H8.
  intro.
  apply (add_2 _ tenv0 s s0 t S) in H8.
  rewrite H8 in |- *.
  apply IHt.
   intro.
   apply H.
   apply FVLambda.
    apply sym_not_eq.
    trivial.

    trivial.

   intro.
   apply H0.
   apply BVLambda2.
   trivial.

   trivial.

 intros.
 inversion H1.
 apply TApply with (a := a).
  apply IHt1.
   intro; apply H.
   apply FVApply.
   left; trivial.

   intro; apply H0.
   apply BVApply.
   left; trivial.

   exact H4.

  apply IHt2.
   intro; apply H.
   apply FVApply.
   right; trivial.

   intro; apply H0.
   apply BVApply.
   right; trivial.

   exact H7.

 intros.
 inversion H1.
 apply TIf.
  apply IHt1.
   intro; apply H.
   apply FVIf.
   left; trivial.

   intro; apply H0.
   apply BVIf.
   left; trivial.

   exact H5.

  apply IHt2.
   intro; apply H.
   apply FVIf.
   right; left; trivial.

   intro; apply H0.
   apply BVIf.
   right; left; trivial.

   trivial.

  apply IHt3.
   intro; apply H.
   apply FVIf.
   right; right; trivial.

   intro; apply H0.
   apply BVIf.
   right; right; trivial.

   trivial.
Qed.
