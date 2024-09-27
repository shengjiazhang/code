Theorem example6 : forall A B C : Prop,
  A -> (A -> B) -> (A -> B -> C) -> C.
Proof.
  intros.
  apply H1 in H0.
  apply H0.
  apply H.
  apply H.
Qed.
