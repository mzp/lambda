Require Import List.
Require Import String.
Require Import Lambda.

(* function *)
Fixpoint subst (t : term) (old : string) (new : term) :=
  match t with
    | Bool _ =>
      t
    | Var x =>
      if string_dec x old then
        new
      else
      	t
    | Lambda x type body =>
      if string_dec x old then
      	t
      else
        Lambda x type (subst body old new)
    | Apply t1 t2 =>
      Apply (subst t1 old new) (subst t2 old new)
    | If t1 t2 t3 =>
      If (subst t1 old new) (subst t2 old new) (subst t3 old new)
  end.

Definition is_value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      true
  | Apply _ _  | If _ _ _ =>
      false
  end.

Fixpoint reduce (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      None
  | Apply t1 t2 =>
      match reduce t1 with
        Some t => Some (Apply t t2)
      | None =>
      	 match reduce t2 with
	  Some t => Some (Apply t1 t)
       	| None   =>
      	   match t1 with
	   Lambda x _ body => Some (subst body x t2)
      	 | _ => None
      	   end
         end
      end
  | If (Bool true) t2 t3 =>
      Some t2
  | If (Bool false) t2 t3 =>
      Some t3
  | If t1 t2 t3 =>
      match reduce t1 with
      	None   => None
      | Some t => Some (If t t2 t3)
      end
  end.

(* typing *)
Fixpoint typing (t : term) (tenv : tenv) :=
  match t with
    Bool _ =>
      Some BoolT
  | Var x =>
      TEnv.find x tenv
  | Lambda x ty1 body =>
    match typing body (TEnv.add x ty1 tenv) with
      None => None
    | Some ty2 => Some (FunT ty1 ty2)
   end
  | Apply t1 t2 =>
    match (typing t1 tenv, typing t2 tenv) with
       (Some (FunT ty11 ty12),Some ty13) =>
        if type_dec ty11 ty13 then
          Some ty12
      	else
	  None
      | _ => None
    end
  | If t1 t2 t3 =>
    match typing t1 tenv with
      Some BoolT =>
      	match (typing t2 tenv, typing t3 tenv) with
      	(Some ty1, Some ty2) =>
          if type_dec ty1 ty2 then
      	    Some ty1
      	  else
	    None
      	| _ =>
      	  None
      	end
    | _ =>
        None
    end
  end.

(* prop theorem *)
Theorem value_prop :
  forall t : term, is_value t = true <-> Value t.
Proof.
split.
 destruct t.
  intro; apply ValVar.

  intro; apply ValBool.

  intro; apply ValLambda.

  simpl in |- *; intro; discriminate.

  simpl in |- *; intro; discriminate.

 generalize t.
 apply Value_ind.
  intro; reflexivity.

  intro; reflexivity.

  intro; reflexivity.
Qed.

Theorem reduce_prop1 :
  forall (t r : term), Some r = reduce t -> Reducible t.
Proof.
intro t.
induction t.
 simpl in |- *; intros; discriminate.

 simpl in |- *; intros; discriminate.

 simpl in |- *; intros; discriminate.

 intro.
 simpl in |- *.
 destruct (reduce t1).
  intros.
  apply RAppLeft.
  eapply IHt1.
  reflexivity.

  destruct (reduce t2).
   intros.
   apply RAppRight.
   eapply IHt2.
   reflexivity.

   destruct t1.
    intro; discriminate.

    intro; discriminate.

    intros; apply RLambda.

    intro; discriminate.

    intro; discriminate.

 simpl in |- *.
 destruct t1.
  simpl in |- *.
  intros; discriminate.

  simpl in |- *.
  intros; apply RIf.

  simpl in |- *.
  intros.
  discriminate.

  destruct (reduce (Apply t1_1 t1_2)).
   intros.
   apply RIfCond.
   eapply IHt1.
   reflexivity.

   intros; discriminate.

  destruct (reduce (If t1_1 t1_2 t1_3)).
   intros.
   apply RIfCond.
   eapply IHt1.
   reflexivity.

   intros; discriminate.
Qed.

Theorem reduce_prop2 :
  forall (t : term), Reducible t -> exists r : term,Some r = reduce t.
Proof.
apply Reducible_ind.
 intros.
 simpl in |- *.
 destruct (reduce t1).
  exists (Apply t t2); reflexivity.

  destruct (reduce t2).
   exists (Apply t1 t).
   reflexivity.

   inversion H0; discriminate.

 intros.
 simpl in |- *.
 destruct (reduce t1).
  exists (Apply t t2).
  reflexivity.

  destruct (reduce t2).
   exists (Apply t1 t); reflexivity.

   inversion H0.
   discriminate.

 intros.
 simpl in |- *.
 destruct (reduce arg).
  exists (Apply (Lambda x ty body) t); reflexivity.

  exists (subst body x arg); reflexivity.

 intros.
 generalize H.
 simpl in |- *.
 destruct t1.
  inversion H.

  inversion H.

  inversion H.

  intros.
  inversion H0.
  rewrite <- H2 in |- *.
  exists (If x t2 t3).
  reflexivity.

  intro.
  inversion H0.
  rewrite <- H2 in |- *.
  exists (If x t2 t3).
  reflexivity.

 intros.
 simpl in |- *.
 case b.
  exists t1; reflexivity.

  exists t2; reflexivity.
Qed.

Theorem subst_1 :
  forall (t1 t2 : term) (x :string) (s : term),
    Subst t1 t2 x s -> t2 = subst t1 x s.
Proof.
apply Subst_ind.
 intros.
 simpl in |- *.
 destruct (string_dec x s).
  reflexivity.

  contradiction .

 intros.
 simpl in |- *.
 destruct (string_dec x s).
  contradiction .

  reflexivity.

 intros.
 simpl in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 destruct (string_dec x s).
  contradiction .

  rewrite <- H1 in |- *.
  reflexivity.

 intros.
 simpl in |- *.
 destruct (string_dec x s).
  reflexivity.

  contradiction .

 intros.
 simpl in |- *.
 rewrite <- H0 in |- *; rewrite <- H2 in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 rewrite H0 in |- *; rewrite H2 in |- *; rewrite H4 in |- *.
 reflexivity.
Qed.


Theorem subst_2 :
  forall (t1 t2 s : term) (x :string),
    t2 = subst t1 x s -> Subst t1 t2 x s.
Proof.
induction t1.
 simpl in |- *; intros.
 destruct (string_dec s x).
  rewrite H in |- *.
  apply SVar1.
  exact e.

  rewrite H in |- *.
  apply SVar2.
  exact n.

 simpl in |- *; intros.
 rewrite H in |- *.
 apply SBool.

 simpl in |- *.
 intros.
 destruct (string_dec s x).
  rewrite H in |- *; rewrite e in |- *.
  apply SLambda2.
  reflexivity.

  rewrite H in |- *.
  apply SLambda1.
   exact n.

   apply IHt1.
   reflexivity.

 simpl in |- *.
 intros.
 rewrite H in |- *.
 apply SApply.
  apply IHt1_1.
  reflexivity.

  apply IHt1_2.
  reflexivity.

 intros.
 rewrite H in |- *.
 simpl in |- *.
 apply SIf.
  apply IHt1_1.
  reflexivity.

  apply IHt1_2; reflexivity.

  apply IHt1_3; reflexivity.
Qed.

Theorem typed_prop1 :
  forall (t : term) (tenv : tenv) (ty : type),
    Typed t tenv ty -> typing t tenv = Some ty.
Proof.
apply Typed_ind.
 intros.
 apply TEnv.find_1.
 exact H.

 intros.
 simpl in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 rewrite H0 in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 rewrite H0 in |- *.
 rewrite H2 in |- *.
 destruct (type_dec a a).
  reflexivity.

  tauto.

 intros.
 simpl in |- *.
 rewrite H0 in |- *.
 rewrite H2 in |- *.
 rewrite H4 in |- *.
 destruct (type_dec ty ty).
  reflexivity.

  tauto.
Qed.

Theorem typed_prop2 :
  forall (t : term)  (tenv : tenv) (ty : type),
     typing t tenv = Some ty -> Typed t tenv ty.
Proof.
induction t.
 simpl in |- *.
 intros.
 apply TVar.
 apply TEnv.find_2.
 exact H.

 simpl in |- *.
 intros.
 inversion H.
 apply TBool.

 simpl in |- *.
 intro.
 intro.
 specialize (IHt (TEnv.add s t tenv)).
 destruct (typing t0 (TEnv.add s t tenv)).
  intros.
  inversion H.
  apply TLambda.
  specialize (IHt t1).
  tauto.

  intro; discriminate.

 intro.
 specialize (IHt1 tenv).
 specialize (IHt2 tenv).
 simpl in |- *.
 destruct (typing t1 tenv).
  destruct t.
   intros; discriminate.

   destruct (typing t2 tenv).
    destruct (type_dec t3 t).
     rewrite <- e in IHt2.
     specialize (IHt1 (FunT t3 t4)).
     intros.
     specialize (IHt2 t3).
     assert (Typed t1 tenv (FunT t3 t4)).
      apply IHt1.
      reflexivity.

      assert (Typed t2 tenv t3).
       apply IHt2.
       reflexivity.

       generalize H1.
       generalize H0.
       inversion H.
       apply TApply.

     intros; discriminate.

    intros; discriminate.

  intros; discriminate.

 intros tenv ty.
 simpl in |- *.
 specialize (IHt1 tenv).
 specialize (IHt2 tenv).
 specialize (IHt3 tenv).
 destruct (typing t1 tenv).
  destruct t.
   destruct (typing t2 tenv).
    destruct (typing t3 tenv).
     destruct (type_dec t t0).
      intro.
      specialize (IHt1 BoolT).
      specialize (IHt2 t0).
      specialize (IHt3 t0).
      inversion H.
      assert (Typed t1 tenv BoolT).
       apply IHt1.
       reflexivity.

       assert (Typed t2 tenv t0).
        apply IHt2.
        rewrite e in |- *.
        reflexivity.

        assert (Typed t3 tenv t0).
         apply IHt3.
         reflexivity.

         generalize H0, H2, H3.
      	 rewrite <- e in |- *.
      	 rewrite H1 in |- *.
         apply TIf.

      intros; discriminate.

     intros; discriminate.

    intros; discriminate.

   intros; discriminate.

  intros; discriminate.
Qed.

