Theorem e4:forall P Q:Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  apply H1.
Qed.
