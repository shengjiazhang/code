Theorem e12:forall P Q:Prop,
  P->~P->Q.
Proof.
  unfold not.
  intros.
  elim H0.
  apply H.
Qed.