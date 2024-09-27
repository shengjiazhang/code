From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Check nat_ind.
(* nat_ind
     : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  -
    reflexivity.
  -
    simpl.
    intros.
    apply H.
Qed.

Theorem plus_one_r : forall n:nat,
  n + 1 = S n.
Proof.
  intros.
  induction n.
  -
    reflexivity.
  -
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Check list_ind.
(* list_ind
     : forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (a :: l)%list) -> forall l : list A, P l *)

Inductive mytype (X : Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constrs3 (m : mytype X) (n : nat).

Check mytype_ind.

Inductive foo (X:Type) : Type :=
  | C1 (l : list X) (f : foo X)
  | C2.

Check foo_ind.
(* foo_ind
     : forall (X : Type) (P : foo X -> Prop),
       (forall (l : list X) (f : foo X), P f -> P (C1 X l f)) ->
       P (C2 X) -> forall f1 : foo X, P f1 *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  -
    reflexivity.
  -
    intros.
    unfold P_m0r in H.
    unfold P_m0r.
    simpl.
    apply H.
Qed.

Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n : nat, even n -> even (S (S n)).

Check even_ind.
(* even_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, even n -> P n -> P (S (S n))) -> forall n : nat, even n -> P n *)

Inductive le1 : nat -> nat -> Prop :=
   | le1_n : forall n, le1 n n
   | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).
Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n : nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).
Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind.
(* le1_ind
     : forall P : nat -> nat -> Prop,
       (forall n : nat, P n n) ->
       (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
       forall n n0 : nat, n <=1 n0 -> P n n0 *)

Check le2_ind.
(* le2_ind
     : forall (n : nat) (P : nat -> Prop),
       P n ->
       (forall m : nat, n <=2 m -> P m -> P (S m)) -> forall n0 : nat, n <=2 n0 -> P n0 *)

Theorem t1 : forall n m o, (n <=1 m /\ m <=1 o) -> (n <=1 o).
Proof.
  intros.
  destruct H as [H1 H2].
  induction H2.
  - (* 假设被用于证明 m ≤ o 的最终规则是 le_n *)
    apply H1.
  - (* 假设被用于证明 m ≤ o 的最终规则是 le_S。 *)
    apply le1_S.
    apply IHle1.
    apply H1.
Qed.











