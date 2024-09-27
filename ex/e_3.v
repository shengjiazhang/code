Theorem e3:forall P Q R S T:Prop,
  (((P /\ Q) /\ R) /\ (S /\ T)) -> (Q /\ S).
Proof.
  intros.
  inversion H.
  split.
  inversion H0.
  inversion H2.
  apply H5.
  inversion H1.
  apply H2.
Qed.