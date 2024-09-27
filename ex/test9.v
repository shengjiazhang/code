Require Import Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Arith.Arith.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Check 3 = 3.
(* 3 = 3
     : Prop *)
Check forall n m : nat, n + m = m + n.
(* forall n m : nat, n + m = m + n
     : Prop *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim.
(* plus_claim
     : Prop *)

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* is_three
     : nat -> Prop *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.
Check injective.

Lemma succ_inj : injective S.
Proof.
  unfold injective.
  intros.
  injection H.
  intros.
  apply H0.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP[HQ HR]].
  (* 将 H : P ∧ (Q ∧ R) 拆分为 HP : P、HQ : Q 和 HR : R  *)
  split.
  -
    split.
    +
      apply HP.
    +
      apply HQ.
  -
    apply HR.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  apply H in H0.
  destruct H0.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HP HQ].
  split.
  -
    apply HQ.
  -
    apply HP.
Qed.

Fixpoint double n : nat :=
  match n with 
  |O=>O
  |S n'=>S (S (double n'))
  end.

Definition even x := exists n : nat, x = double n.

Lemma four_is_even : even 4.
Proof.
  unfold even.
  exists 2.
  reflexivity.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - (* -> direction *)
    intros H.
    destruct H as [x HPQ].
    destruct HPQ as [HP|HQ].
    +
      left.
      exists x.
      apply HP.
    +
      right.
      exists x.
      apply HQ.
  -
    intros H.
    destruct H as [HP|HQ].
    +
      destruct HP as [x HPP].
      exists x.
      left.
      apply HPP.
    +
      destruct HQ as [x HQQ].
      exists x.
      right.
      apply HQQ.
Qed.

Fixpoint In {X : Type} (n : X) (l : list X) : Prop:=
  match l with
  |nil => False
  |x::l'=> (n = x) \/(In n l')
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l.
  -
    simpl.
    intros.
    apply H.
  -
    simpl.
    intros.
    destruct H.
    +
      rewrite H.
      left.
      reflexivity.
    +
      apply IHl in H.
      right.
      apply H.
Qed.

Definition in_not_nil :
  forall {A:Type} (x : A) (l : list A), In x l -> (l <> []).
Proof.
  intros.
  unfold not.
  intros Hn.
  destruct l.
  -
    simpl in H.
    apply H.
  -
    discriminate Hn.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros.
  apply (in_not_nil _ _ H).
Qed.

(* Inductive ev : nat->Prop :=
|evO : ev O
|evSS (n : nat) (H : ev n) : ev (S (S n)). *)

Inductive ev : nat->Prop :=
|evO : ev O
|evSS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n.
  unfold double.
  induction n.
  -
    apply evO.
  -
    apply evSS.
    apply IHn.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H'].
  inversion H' as [|n'' H''].
  apply H''.
Qed.

Lemma ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       同时 IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  -
    apply ev_even.
  -
    intros [k IHk].
    rewrite IHk.
    apply ev_double.
Qed.

Inductive le : nat->nat->Prop :=
  |le_n (n : nat) : le n n
  |le_S (n m : nat) (H : le n m) : le n (S m).
Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2.
  -
    apply H1.
  -
    apply le_S.
    apply IHle.
    apply H1.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
  -
    apply le_n.
  -
    apply le_S.
    apply IHn.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

Theorem R_my_function_equiv : forall m n o,
  R m n o <-> m + n = o.
Proof.
Admitted.
































