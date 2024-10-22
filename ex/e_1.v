Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Import ListNotations.
Require Import Lia.
Require Import Coq.Reals.Reals.
Require Export PropExtensionality.
Require Import Extraction.
Theorem e1:forall P Q R:Prop,
  ((P -> R) /\ (Q -> R)) -> (P /\ Q -> R).
Proof.
  intros.
  inversion H0.
  inversion H.
  apply H3 in H1.
  apply H1.
Qed.

Print Nat.eq_dec.
Print lt_dec.
Print gt_dec.
Print le_gt_dec.

Theorem lt_ge_dec : forall n m, {n < m} + {n >= m}.
Proof.
  intros. destruct (le_gt_dec m n); auto.
Qed.

Print lt_ge_dec.

Print e2.