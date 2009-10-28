(* simple typed lambda calculus *)
Require Import Arith.EqNat.
Require Import Arith.
Require Import Recdef.
Require Import List.
Require Import String.
Require Import Bool.DecBool.

(* simple type *)
Inductive type : Set :=
    BoolT : type
  | FunT  : type -> type -> type.

Inductive term : Set :=
    Var     : string -> term
  | Bool    : bool   -> term
  | Lambda  : string -> type -> term -> term
  | Apply   : term  -> term -> term
  | If      : term -> term -> term -> term.

(* equality *)
Definition type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(* Prop *)
Inductive Value  : term -> Prop :=
  | ValVar    : forall s : string, Value (Var s)
  | ValBool   : forall b : bool,   Value (Bool b)
  | ValLambda : forall (x : string) (ty : type) (body : term), Value (Lambda x ty body).

Inductive Reducible : term -> Prop :=
  | RAppLeft  : forall t1 t2 : term, Reducible t1 -> Reducible (Apply t1 t2)
  | RAppRight : forall t1 t2 : term, Reducible t2 -> Reducible (Apply t1 t2)
  | RLambda   : forall (x : string) (ty : type) (body arg : term), Reducible (Apply (Lambda x ty body) arg)
  | RIfCond   : forall (t1 t2 t3 : term), Reducible t1 -> Reducible (If t1 t2 t3)
  | RIf       : forall (b : bool) (t1 t2 : term), Reducible (If (Bool b) t1 t2).

Definition tenv := list (string * type).

Fixpoint assoc {A : Type} (x : string) (xs : list (string * A)) :=
  match xs with
  | nil =>
      None
  | (key, v) :: ys =>
      if string_dec x key then
        Some v
       else
      	assoc x ys
  end.

Inductive Typed : term -> tenv -> type -> Prop :=
  | TVar    : forall (tenv : tenv) (s : string) (ty : type), Some ty = assoc s tenv -> Typed (Var s) tenv ty
  | TBool   : forall (tenv : tenv) (b : bool) , Typed (Bool b) tenv BoolT
  | TLambda : forall (tenv : tenv) (x : string)      (a b : type) (body : term), Typed body ((x,a)::tenv) b -> Typed (Lambda x a body) tenv (FunT a b)
  | TApply  : forall (tenv : tenv) (t1 t2 : term)    (a b : type), Typed t1 tenv (FunT a b) -> Typed t2 tenv a -> Typed (Apply t1 t2) tenv b
  | TIf     : forall (tenv : tenv) (t1 t2 t3 : term) (ty : type), Typed t1 tenv BoolT -> Typed t2 tenv ty -> Typed t3 tenv ty -> Typed (If t1 t2 t3) tenv ty.

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
      assoc x tenv
  | Lambda x ty1 body =>
    match typing body ((x,ty1)::tenv) with
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

Theorem typed_prop1 :
  forall (t : term) (tenv : tenv) (ty : type),
    Typed t tenv ty -> Some ty = typing t tenv.
Proof.
apply Typed_ind.
 intros.
 simpl in |- *.
 exact H.

 intros.
 simpl in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 rewrite <- H0 in |- *.
 reflexivity.

 intros.
 simpl in |- *.
 rewrite <- H0 in |- *.
 rewrite <- H2 in |- *.
 destruct (type_dec a a).
  reflexivity.

  tauto.

 intros.
 simpl in |- *.
 rewrite <- H0 in |- *.
 rewrite <- H2 in |- *.
 rewrite <- H4 in |- *.
 destruct (type_dec ty ty).
  reflexivity.

  tauto.
Qed.

Theorem typed_prop2 :
  forall (t : term)  (tenv : tenv) (ty : type),
    Some ty = typing t tenv -> Typed t tenv ty.
Proof.
induction t.
 simpl in |- *.
 intros.
 apply TVar.
 exact H.

 simpl in |- *.
 intros.
 inversion H.
 apply TBool.

 simpl in |- *.
 intro.
 intro.
 specialize (IHt ((s, t) :: tenv0)).
 destruct (typing t0 ((s, t) :: tenv0)).
  intros.
  inversion H.
  apply TLambda.
  specialize (IHt t1).
  tauto.

  intro; discriminate.

 intro.
 specialize (IHt1 tenv0).
 specialize (IHt2 tenv0).
 simpl in |- *.
 destruct (typing t1 tenv0).
  destruct t.
   intros; discriminate.

   destruct (typing t2 tenv0).
    destruct (type_dec t3 t).
     rewrite <- e in IHt2.
     specialize (IHt1 (FunT t3 t4)).
     intros.
     specialize (IHt2 t3).
     assert (Typed t1 tenv0 (FunT t3 t4)).
      apply IHt1.
      reflexivity.

      assert (Typed t2 tenv0 t3).
       apply IHt2.
       reflexivity.

       generalize H1.
       generalize H0.
       inversion H.
       apply TApply.

     intros; discriminate.

    intros; discriminate.

  intros; discriminate.

 intros tenv0 ty.
 simpl in |- *.
 specialize (IHt1 tenv0).
 specialize (IHt2 tenv0).
 specialize (IHt3 tenv0).
 destruct (typing t1 tenv0).
  destruct t.
   destruct (typing t2 tenv0).
    destruct (typing t3 tenv0).
     destruct (type_dec t t0).
      intro.
      specialize (IHt1 BoolT).
      specialize (IHt2 t0).
      specialize (IHt3 t0).
      inversion H.
      rewrite e in |- *.
      assert (Typed t1 tenv0 BoolT).
       apply IHt1.
       reflexivity.

       assert (Typed t2 tenv0 t0).
        apply IHt2.
        rewrite e in |- *.
        reflexivity.

        assert (Typed t3 tenv0 t0).
         apply IHt3.
         reflexivity.

         generalize H0, H2, H3.
         apply TIf.

      intros; discriminate.

     intros; discriminate.

    intros; discriminate.

   intros; discriminate.

  intros; discriminate.
Qed.

(* obsolute *)
Definition value (t : term) :=
  match t with
    Var _   | Bool _  | Lambda _ _ _ =>
      True
  | Apply _ _  | If _ _ _ =>
      False
  end.
