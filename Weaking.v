Require Import List.
Require Import String.

Require Import Term.
Require Import Eval.
Require Import Typing.

Lemma swap:
  forall (tenv1 tenv2 : tenv) (x : string) (r : type),
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

Theorem permutation:
  forall (t : term) (tenv1 tenv2 : tenv) (r : type),
    TEnv.Equal tenv1 tenv2 ->
      Typed t tenv1 r -> Typed t tenv2 r.
Proof.
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

Lemma Equal_add_1 :
  forall (tenv : tenv) (x y : string) (r1 r2 : type),
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

Lemma Equal_add_2 :
  forall (tenv : tenv) (x y : string) (r1 r2 : type),
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

Theorem weaking:
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

(*Lemma subst_presarve:
  forall (t : term) (s: term) (x : string) (T S : type) (tenv : tenv),
    Typed t (TEnv.add x S tenv) T -> Typed s tenv S -> Typed (subst t x s) tenv T.
Proof.
intros t s x.
pattern t, x, s, (subst t x s) in |- *.
apply subst_ind.
 (* Var *)
 intros.
 rewrite _x in H.
 inversion H.
 apply TEnvWF.add_mapsto_iff in H2.
 decompose [or] H2.
  inversion H5.
  rewrite <- H7 in |- *.
  exact H0.

  inversion H5.
  tauto.

 intros.
 inversion H.
 apply TEnvWF.add_mapsto_iff in H2.
 decompose [or] H2.
  inversion H5.
  apply sym_eq in H6.
  contradiction.

  inversion H5.
  rewrite e in |- *.
  apply TVar.
  exact H7.

 (* Bool *)
 intros.
 rewrite e in |- *.
 inversion H.
 apply TBool.

 (* Lambda-1 *)
 intros.
 generalize _x.
 intro.
 inversion H.
 apply TLambda.
 apply Equal_add_1 with (tenv := tenv) (r1 := T) (r2 := S) in _x0.
 apply permutation with (t := body) (r := b) in _x0.
  exact _x0.

  exact H6.

 (* Lambda-2 *)
 intros.
 inversion H0.
 apply TLambda.
 inversion H0.
 apply H with (S := S).
*)
(*
Proof.
induction t.
 (* Var z *)
 intros.
 inversion H1.
  (* x = z *)
  rewrite H3 in H.
  inversion H.
  apply TEnvWF.add_mapsto_iff in H8.
  decompose [or] H8.
   inversion H11.
   rewrite <- H13 in |- *.
   exact H0.

   tauto.

  (* x <> z *)
  inversion H.
  apply TEnvWF.add_mapsto_iff in H8.
  decompose [or] H8.
   inversion H11.
   rewrite H12 in H3.
   tauto.

   inversion H11.
   apply TVar.
   exact H13.

 (* Bool *)
 intros.
 inversion H; inversion H1.
 apply TBool.

 (* Lambda *)
 intros.
 inversion H.
 inversion H1.
  apply (Equal_add_2 tenv s x t S) in H14.
*)

Lemma Var_add_eq:
  forall (x : string) (S T : type) (tenv : tenv),
     Typed (Var x) (TEnv.add x S tenv) T -> S = T.
Proof.
intros.
inversion H.
apply TEnvWF.add_mapsto_iff in H1.
inversion H1.
 inversion H4.
 exact H6.

 inversion H4.
 tauto.
Qed.

Lemma Var_add_elim:
  forall (x y : string) (S T : type) (tenv : tenv),
     x <> y -> Typed (Var x) (TEnv.add y S tenv) T -> Typed (Var x) tenv T.
Proof.
intros.
inversion H0.
apply TEnvWF.add_mapsto_iff in H2.
inversion H2.
 inversion H5.
 rewrite H6 in H.
 tauto.

 inversion H5.
 apply TVar.
 exact H7.
Qed.

Lemma Var_add_intro:
  forall (x y : string) (S T : type) (tenv : tenv),
     x <> y -> Typed (Var x) tenv T -> Typed (Var x) (TEnv.add y S tenv) T.
Proof.
intros.
apply TVar.
apply TEnv.add_2.
 apply sym_not_equal.
 exact H.

 inversion H0.
 exact H2.
Qed.

Lemma Typed_add_elim:
  forall (t : term) (S T U : type) (s : string) (tenv : tenv),
      Typed t (TEnv.add s T (TEnv.add s S tenv)) U -> Typed t (TEnv.add s T tenv) U.
Proof.
intros.
apply permutation with (tenv1 := TEnv.add s T (TEnv.add s S tenv)).
 apply Equal_add_1.
 reflexivity.

 exact H.
Qed.

Lemma Typed_add_intro:
  forall (t : term) (S T U : type) (s : string) (tenv : tenv),
      Typed t (TEnv.add s T tenv) U -> Typed t (TEnv.add s T (TEnv.add s S tenv)) U.
Proof.
intros.
apply permutation with (tenv1 := TEnv.add s T tenv).
 apply TEnvWF.Equal_sym.
 apply Equal_add_1.
 reflexivity.

 exact H.
Qed.
