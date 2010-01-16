Require Import String.

Require Import Dec.
Require Import Sets.

Module TVars  := Sets.Make StrDec.
Definition tvars  := TVars.t.

Definition DisjointBy {A : Type} (Free : string -> A -> Prop) xs (T : A) := forall x,
  TVars.In x xs -> ~ Free x T /\ Free x T -> ~ TVars.In x xs.

