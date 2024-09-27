Require Import e_2.
Theorem e1:forall P Q R:Prop,
  ((P -> R) /\ (Q -> R)) -> (P /\ Q -> R).
Proof.
  intros.
  inversion H0.
  inversion H.
  apply H3 in H1.
  apply H1.
Qed.

Print e2.