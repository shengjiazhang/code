Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Arith.Arith.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check [2;2;2].

Theorem silly : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros.
(*   1 goal
n, m, o, p : nat
H : n = m
H0 : n = m -> [n; o] = [m; p]
______________________________________(1/1)
[n; o] = [m; p] *)
  apply H0.
(*   1 goal
n, m, o, p : nat
H : n = m
H0 : n = m -> [n; o] = [m; p]
______________________________________(1/1)
n = m *)
  apply H.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Fixpoint evenb (n : nat) : bool :=
match n with
|O => true
|S O => false
|S (S n') => evenb n'
end.
Definition oddb (n : nat) : bool :=
let res := evenb n in
res.
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite H. (* 将 l 替换为 rev l' *)
  symmetry. (* 对称性，将等式左右两边交换 *)
  apply rev_involutive. (* 应用 rev_involutive 引理 *)
Qed.

Check rev_involutive.
(* rev_involutive
     : forall (A : Type) (l : list A), rev (rev l) = l *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
(*   1 goal
a, b, c, d, e, f : nat
H : [a; b] = [c; d]
H0 : [c; d] = [e; f]
______________________________________(1/1)
[a; b] = [e; f] *)
  apply trans_eq with ([c;d]).
  apply H.
  apply H0.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros.
  injection H as Hmn. 
(* 通过在此处编写 injection H as Hmn，我们让 Coq 利用构造子的单射性来产生所有它能从 H 所推出的等式 *)
  apply Hmn.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros.
  injection H.
  intros.
  rewrite H1.
  rewrite H0.
  reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  injection H.
  intros.
  rewrite H0 in H1.
  injection H1.
  intros.
  symmetry in H3.
  rewrite H3 in H2.
  apply H2.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros.
  destruct n as[|n'].
  -
    simpl.
    reflexivity.
  -
    simpl.
(*     1 goal
n' : nat
H : (0 =? S n') = true
______________________________________(1/1)
S n' = 0
这个前提H是不可能成立的，因为S n'一定是大于等于1的，这时我们使用discriminate策略 *)
  discriminate H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. 
  apply eq in H. 
  symmetry in H.
  apply H.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem double_injective: forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n.
  -
    simpl.
    intros m eq.
    destruct m.
    +
      reflexivity.
    +
      discriminate eq.
  -
    simpl.
    intros m eq.
    destruct m.
    +
      discriminate eq.
    +
      apply f_equal.
      apply IHn.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  -
    intros m eq.
    destruct m.
    + 
      reflexivity.
    +
      discriminate eq.
  -
    intros m eq.
    destruct m.
    +
      discriminate eq.
    +
      simpl.
      apply IHn in eq.
      apply f_equal.
      apply eq.
Qed.

Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros.
  simpl.
  (* 这里的simpl策略并不能完成化简，为此我们可以使用unfold策略，展开square的定义 *)
  unfold square.
(*   1 goal
n, m : nat
______________________________________(1/1)
n * m * (n * m) = n * n * (m * m) *)
  (* 我们再运用乘法交换律和乘法结合律就可以轻松证明目标，这不做赘述 *)
Admitted.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros.
  unfold sillyfun.
  destruct (n=?3) eqn:E1.
  -(* n=3 *)
    reflexivity.
  -(* n<>3 *)
    destruct (n=?5) eqn:E2.
    +(* n=5 *)
      reflexivity.
    +(* n<>5 *)
      reflexivity.
Qed.



























