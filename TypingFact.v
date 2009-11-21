Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import Typing.

Lemma swap: forall tenv1 tenv2 x (r : type),
  TEnv.Equal tenv1 tenv2 ->
     TEnv.Equal (TEnv.add x r tenv1) (TEnv.add x r tenv2).
Proof.
intros.
eapply TEnvWF.Equal_mapsto_iff.

split.
  (* TEnv.MapsTo k e (TEnv.add x r tenv1) -> TEnv.MapsTo k e (TEnv.add x r tenv2) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = x *)
  inversion H1.
  rewrite H2 in |- *; rewrite H3 in |- *.
  apply TEnv.add_1.
  reflexivity.

  (* k <> x *)
  inversion H1.
  apply TEnv.add_2.
   exact H2.

   eapply TEnvWF.Equal_mapsto_iff in H.
   apply H.
   exact H3.

 (* TEnv.MapsTo k e (TEnv.add x r tenv2) -> TEnv.MapsTo k e (TEnv.add x r tenv1) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = x *)
  inversion H1.
  rewrite H3 in |- *; rewrite H2 in |- *.
  apply TEnv.add_1.
  reflexivity.

  (* k <> x *)
  inversion H1.
  apply TEnv.add_2.
   exact H2.

   eapply TEnvWF.Equal_mapsto_iff.
    apply H.

    exact H3.
Qed.

Lemma string_mid:
  forall (x y : string), x = y \/ x <> y.
Proof.
  intros.
  generalize (string_dec x y).
  tauto.
Qed.

Lemma permutation: forall t tenv1 tenv2 r,
    TEnv.Equal tenv1 tenv2 ->
      Typed t tenv1 r -> Typed t tenv2 r.
Proof.
intro.
induction t.
 (* Var *)
 intros.
 inversion H0.
 apply TVar.
 eapply TEnvWF.Equal_mapsto_iff in H.
 apply H.
 exact H2.

 (* Bool *)
 intros.
 inversion H0.
 apply TBool.

 (* Lambda *)
 intros.
 inversion H0.
 apply TLambda.
 apply swap with (x := s) (r := t) in H.
 apply IHt with (r := b) in H.
  exact H.

  exact H6.

 (* Apply *)
 intros.
 inversion H0.
 apply TApply with (a := a).
  eapply IHt1 in H3.
   apply H3.

   exact H.

  eapply IHt2 in H6.
   apply H6.

   exact H.

 (* If *)
 intros.
 inversion H0.
 apply TIf.
  eapply IHt1.
   apply H.

   exact H4.

  eapply IHt2.
   apply H.

   exact H7.

  eapply IHt3.
   apply H.

   exact H8.
Qed.

Lemma Equal_add_1 : forall tenv x y (r1 r2 : type),
    x = y -> TEnv.Equal (TEnv.add x r1 (TEnv.add y r2 tenv)) (TEnv.add x r1 tenv).
Proof.
intros.
rewrite H in |- *.
eapply TEnvWF.Equal_mapsto_iff.
split.
 (* TEnv.MapsTo k e (TEnv.add y r1 (TEnv.add y r2 tenv)) ->
    TEnv.MapsTo k e (TEnv.add y r1 tenv) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = y *)
  decompose [and] H1.
  rewrite H3 in |- *.
  rewrite H2 in |- *.
  apply TEnv.add_1.
  reflexivity.

  (* k <> y *)
  decompose [and] H1.
  apply TEnv.add_2.
   exact H2.

   apply TEnv.add_3 in H3.
    exact H3.

    exact H2.

 (* TEnv.MapsTo k e (TEnv.add y r1 tenv) ->
    TEnv.MapsTo k e (TEnv.add y r1 (TEnv.add y r2 tenv)) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = y *)
  inversion H1.
  rewrite H2 in |- *.
  rewrite H3 in |- *.
  apply TEnv.add_1.
  reflexivity.

  (* k <> y *)
  decompose [and] H1.
  apply TEnv.add_2.
   exact H2.

   apply TEnv.add_2.
    exact H2.

    exact H3.
Qed.

Lemma Equal_add_2 : forall tenv x y (r1 r2 : type),
    x <> y -> TEnv.Equal (TEnv.add x r1 (TEnv.add y r2 tenv))
                         (TEnv.add y r2 (TEnv.add x r1 tenv)).
Proof.
intros.
eapply TEnvWF.Equal_mapsto_iff.
split.
 (* TEnv.MapsTo k e (TEnv.add x r1 (TEnv.add y r2 tenv)) ->
      TEnv.MapsTo k e (TEnv.add y r2 (TEnv.add x r1 tenv)) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = x *)
  inversion H1.
  rewrite H2 in |- *.
  rewrite H3 in |- *.
  rewrite H2 in H.
  apply TEnv.add_2.
   auto.

   apply TEnv.add_1.
   reflexivity.

  (* k <> x*)
  decompose [and] H1.
  apply TEnvWF.add_mapsto_iff in H3.
  decompose [or] H3.
   (* y = k*)
   inversion H4.
   rewrite H5 in |- *; rewrite H6 in |- *.
   apply TEnv.add_1.
   reflexivity.

   (* y <> k*)
   decompose [and] H4.
   apply TEnv.add_2.
    exact H5.

    apply TEnv.add_2.
     exact H2.

     exact H6.

 (* TEnv.MapsTo k e (TEnv.add y r2 (TEnv.add x r1 tenv)) ->
    TEnv.MapsTo k e (TEnv.add x r1 (TEnv.add y r2 tenv)) *)
 intros.
 apply TEnvWF.add_mapsto_iff in H0.
 decompose [or] H0.
  (* k = y *)
  inversion H1.
  rewrite H2 in |- *; rewrite H3 in |- *.
  rewrite H2 in H.
  apply TEnv.add_2.
   exact H.

   apply TEnv.add_1.
   reflexivity.

  (* k <> y *)
  inversion H1.
  apply TEnvWF.add_mapsto_iff in H3.
  decompose [or] H3.
   (* k = x *)
   inversion H4.
   rewrite H6 in |- *.
   rewrite H5 in |- *.
   apply TEnv.add_1.
   reflexivity.

   (* k <> x *)
   decompose [and] H4.
   apply TEnv.add_2.
    exact H5.

    apply TEnv.add_2.
     exact H2.

     exact H6.
Qed.


Definition NotIn (x : string) (tenv : tenv) : Prop :=
  forall (y : string) (T : type), TEnv.MapsTo y T tenv -> x <> y.

Lemma weaking:
  forall (t : term) (tenv : tenv) (T S : type) (x : string),
  Typed t tenv T -> NotIn x tenv -> Typed t (TEnv.add x S tenv) T.
Proof.
induction t.
 (* Var *)
 intros.
 inversion H.
 apply TVar.
 unfold NotIn in H0.
 apply TEnv.add_2.
  generalize (H0 s T).
  intros.
  apply H5 in H2.
  exact H2.

  exact H2.

 (* Bool *)
 intros.
 inversion H.
 apply TBool.

 (* Lambda *)
 intros.
 inversion H.
 apply TLambda.
 generalize (string_mid s x).
 intros.

 decompose [or] H7.
  (* s = x *)
  eapply Equal_add_1 in H8.
  eapply permutation.
   apply TEnvWF.Equal_sym.
   apply H8.

   exact H6.

  (* s <> x *)
  generalize H8; intro.
  eapply Equal_add_2 in H8.
  eapply permutation.
   apply TEnvWF.Equal_sym.
   apply H8.

   apply IHt.
    exact H6.

    unfold NotIn in |- *.
    intros.
    apply TEnvWF.add_mapsto_iff in H10.
    decompose [or] H10.
     inversion H11.
     rewrite <- H12 in |- *.
     auto.

     unfold NotIn in H0.
     eapply H0.
     inversion H11.
     apply H13.

 (* Apply *)
 intros.
 inversion H.
 eapply TApply.
  apply IHt1.
   apply H3.

   exact H0.

  apply IHt2.
   exact H6.

   exact H0.

 (* If *)
 intros.
 inversion H.
 apply TIf.
  apply IHt1.
   exact H4.

   exact H0.

  apply IHt2.
   exact H7.

   exact H0.

  apply IHt3.
   exact H8.

   exact H0.
Qed.

Lemma Typed_add_elim: forall t S T tenv s,
    ~ FV s t -> Typed t (TEnv.add s S tenv) T -> Typed t tenv T.
Proof.
intro.
induction t.
 intros.
 inversion H0.
 apply TVar.
 apply TEnvWF.add_mapsto_iff in H2.
 inversion H2.
  inversion H5.
  assert (FV s0 (Var s)).
   rewrite H6 in |- *.
   apply FVVar.

   contradiction .

  inversion H5.
  exact H7.

 intros.
 inversion H0.
 apply TBool.

 intros.
 inversion H0.
 apply TLambda.
 destruct (string_dec s s0).
  apply permutation with (tenv2 := TEnv.add s t tenv) in H6.
   exact H6.

   apply Equal_add_1.
   exact e.

  apply IHt with (S := S) (s := s0).
   apply FV_Lambda_inv with (y := s) (T := t).
    apply sym_not_eq.
    exact n.

    exact H.

   apply permutation with (tenv1 := TEnv.add s t (TEnv.add s0 S tenv)).
    apply Equal_add_2.
    exact n.

    exact H6.

 intros.
 inversion H0.
 apply TApply with (a := a).
  apply IHt1 with (S := S) (s := s).
   apply FV_Apply_inv_1 with (t2 := t2).
   exact H.

   exact H3.

  apply IHt2 with (S := S) (s := s).
   apply FV_Apply_inv_2 with (t1 := t1).
   exact H.

   exact H6.

 intros.
 inversion H0.
 apply TIf.
  apply IHt1 with (S := S) (s := s).
   apply FV_If_inv_1 with (t2 := t2) (t3 := t3).
   exact H.

   exact H4.

  apply IHt2 with (S := S) (s := s).
   apply FV_If_inv_2 with (t1 := t1) (t3 := t3).
   exact H.

   exact H7.

  apply IHt3 with (S := S) (s := s).
   apply FV_If_inv_3 with (t1 := t1) (t2 := t2).
   exact H.

   exact H8.
Qed.


Lemma Typed_add_intro: forall t S T tenv s,
    ~ FV s t -> ~ BV s t -> Typed t tenv T -> Typed t (TEnv.add s S tenv) T.
Proof.
induction t
 (* Var *).
 intros.
 apply TVar.
 apply TEnv.add_2.
  intro; apply H.
  rewrite H2 in |- *.
  apply FVVar.

  inversion H1.
  exact H3.

 (* Bool *)
 intros.
 inversion H1.
 apply TBool.

 (* Lambda *)
 intros.
 inversion H1.
 apply TLambda.
 apply permutation with (tenv1 := TEnv.add s0 S (TEnv.add s t tenv)).
  apply Equal_add_2.
  intro; apply H0.
  rewrite H8 in |- *.
  apply BVLambda1.

  apply IHt.
   intro; apply H.
   apply FVLambda.
    intro; apply H0.
    rewrite H9 in |- *.
    apply BVLambda1.

    exact H8.

   intro; apply H0.
   apply BVLambda2.
   exact H8.

   exact H7.

 (* Apply *)
 intros.
 inversion H1.
 apply TApply with (a := a).
  apply IHt1.
   intro; apply H.
   apply FVApply.
   left; exact H8.

   intro; apply H0.
   apply BVApply.
   left; exact H8.

   exact H4.

  apply IHt2.
   intro; apply H.
   apply FVApply.
   right; exact H8.

   intro; apply H0.
   apply BVApply.
   right; exact H8.

   exact H7.

 (* If *)
 intros.
 inversion H1.
 apply TIf.
  apply IHt1.
   intro; apply H.
   apply FVIf.
   left; exact H10.

   intro; apply H0.
   apply BVIf.
   left; exact H10.

   exact H5.

  apply IHt2.
   intro; apply H.
   apply FVIf.
   right; left; exact H10.

   intro; apply H0.
   apply BVIf.
   right; left; exact H10.

   exact H8.

  apply IHt3.
   intro; apply H.
   apply FVIf.
   right; right; exact H10.

   intro; apply H0.
   apply BVIf.
   right; right; exact H10.

   exact H9.
Qed.
