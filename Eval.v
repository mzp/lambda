Require Import List.
Require Import ListSet.
Require Import String.
Require Import Recdef.

Require Import Term.

(** * Propotion *)
Inductive Value  : term -> Prop :=
  | VBool   : forall b : bool,   Value (Bool b)
  | VLambda : forall (x : string) (ty : type) (body : term), Value (Lambda x ty body).

Inductive Reducible : term -> Prop :=
  | RAppLeft  : forall t1 t2 : term, Reducible t1 -> Reducible (Apply t1 t2)
  | RAppRight : forall t1 t2 : term, Reducible t2 -> Reducible (Apply t1 t2)
  | RLambda   : forall (x : string) (ty : type) (body arg : term), Reducible (Apply (Lambda x ty body) arg)
  | RIfCond   : forall (t1 t2 t3 : term), Reducible t1 -> Reducible (If t1 t2 t3)
  | RIf       : forall (b : bool) (t1 t2 : term), Reducible (If (Bool b) t1 t2).

(** * function *)
(** ** free variable *)
Definition empty :=
  ListSet.empty_set string.
Definition add (x : string) (xs : set string) :=
  ListSet.set_add string_dec x xs.
Definition remove (x : string) (xs : set string) :=
  ListSet.set_diff string_dec xs (add x empty).
Definition union (xs ys : set string) :=
  ListSet.set_union string_dec xs ys.
Definition in_dec (x : string) (xs : set string) :=
  set_In_dec string_dec x xs.

Fixpoint FV (t : term) : set string :=
  match t with
  | Var x =>
    add x empty
  | Bool _ =>
    empty
  | Lambda x _ body =>
    remove x (FV body)
  | Apply t1 t2 =>
    union (FV t1) (FV t2)
  | If t1 t2 t3 =>
    union (union (FV t1) (FV t2)) (FV t3)
  end.

(** ** Substitution *)
Variable Gensym : set string -> string.
Hypothesis Gensym_uniq : forall (xs : set string) (x : string),
  x = Gensym xs -> ~ set_In x xs.

Fixpoint assoc {A B : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (xs : list (A * B)) :=
  match xs with
  | nil => None
  | (key,val)::xs =>
    if dec key x then
      Some val
    else
      assoc dec x xs
  end.

Fixpoint rename_var (t : term) (old new : string) :=
  match t with
  |  Var s =>
    if string_dec s old then
      Var new
    else
      t
  | Bool _  =>
      t
  | Lambda x T body =>
      if string_dec x old then
      	Lambda x T body
      else
        Lambda x T (rename_var body old new)
  | Apply t1 t2 =>
      Apply (rename_var t1 old new) (rename_var t2 old new)
  | If t1 t2 t3 =>
      If (rename_var t1 old new) (rename_var t2 old new) (rename_var t3 old new)
  end.

Fixpoint term_length (t : term) :=
  match t with
  |  Var _ | Bool _ =>
    1
  | Lambda _ _ body =>
    1 + term_length body
  | Apply t1 t2 =>
    1 + term_length t1 + term_length t2
  | If t1 t2 t3 =>
    1 + term_length t1 + term_length t2 + term_length t3
  end.

Lemma rename_var_length :
  forall (t : term) (x y : string),
  term_length t = term_length (rename_var t x y).
Proof.
induction t.
 simpl in |- *.
 intros.
 destruct string_dec; simpl in |- *; reflexivity.

 simpl in |- *.
 intros; reflexivity.

 simpl in |- *.
 intros.
 destruct (string_dec s x); simpl in |- *.
  reflexivity.

  rewrite (IHt x y) in |- *.
  reflexivity.

 simpl in |- *.
 intros.
 rewrite (IHt1 x y) in |- *.
 rewrite (IHt2 x y) in |- *.
 reflexivity.

 simpl in |- *.
 intros.
 rewrite (IHt1 x y) in |- *; rewrite (IHt2 x y) in |- *;
  rewrite (IHt3 x y) in |- *.
 reflexivity.
Qed.

Function subst (t : term) (old : string) (new : term) {measure term_length t}: term :=
  match t with
  |  Var s =>
    if string_dec s old then
      new
    else
      t
  | Bool _  =>
      t
  | Lambda x T body =>
      if string_dec x old then
      	Lambda x T body
      else if in_dec x (FV new) then
      	let y := Gensym (union (FV new) (FV body)) in
          Lambda y T (subst (rename_var body x y) old new)
      else
        Lambda x T (subst body old new)
  | Apply t1 t2 =>
      Apply (subst t1 old new) (subst t2 old new)
  | If t1 t2 t3 =>
      If (subst t1 old new) (subst t2 old new) (subst t3 old new)
  end.
Proof.
 intros.
 rewrite <- (rename_var_length body x (Gensym (union (FV new) (FV body)))) in |- *.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply le_n.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply le_n.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_l.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_trans.
 apply Plus.le_plus_r.

 intros.
 simpl in |- *.
 apply Lt.le_lt_n_Sm.
 apply Plus.le_plus_trans.
 apply Plus.le_plus_l.
Qed.

Definition mbind {A : Type} (x : option A) (f : A -> option A) : option A :=
  match x with
  | None => None
  | Some y => f y
  end.

Infix ">>=" := mbind (at level 50).

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
      reduce t1 >>= (fun x => Some (If x t2 t3))
  end.

(** * Theorem *)
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

