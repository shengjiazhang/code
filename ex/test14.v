Definition relation (X: Type) := X -> X -> Prop.

Print le.
(* Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition reflexive {X: Type} (R: relation X) :=
  forall x : X, R x x.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros.
  apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros.
  induction H0.
  -
    apply H.
  -
    apply le_S.
    apply IHle.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~(symmetric le).
Proof.
  unfold not, symmetric.
  intros Hsym.
  assert (1 <= 0) as H.
  { apply Hsym. apply le_S. apply le_n. }
  inversion H.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b H1 H2.
  generalize dependent a. (* 将 a 泛化 *)
  induction b as [| b' IHb'].
  - intros a H1.
    inversion H1.
    reflexivity.
  - intros a H1 H2.
    destruct a as [| a'] eqn:Ha.
    + inversion H2.
    + apply f_equal. (* 将证明转化为证明 a' = b' *)
      apply IHb'.
      * apply le_S_n. (* 由于 b' <= a'，则 b' <= a' - 1，即 le_S_n *)
        apply H1.
      * apply le_S_n. (* 由于 a' <= b'，则 a' <= b' - 1，即 le_S_n *)
        apply H2.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).











