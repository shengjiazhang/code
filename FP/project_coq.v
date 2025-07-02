(* Final Project --- June, 2025
You are allowed to search and use any property provided in the standard library 
of Coq. *)

Require Import Nat.
Require Import List.
Require Import Lia.
Require Import Arith.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers by induction. *)
Lemma mul_3_r : forall  n : nat, 
  n*3 = n + n + n.
Proof.
  induction n.
  - simpl; reflexivity.
  - simpl. rewrite IHn. repeat rewrite <- plus_n_Sm. reflexivity.
  (*FILL IN HERE*)
Qed.

(* 2. Define a function called pNumber so that (pNumber n) returns true 
iff n is the product of two consecutive numbers, i.e. n = n' * (n'+1) for some n'. *)

Fixpoint pNumberFrom (k n : nat) : bool :=
  match k with
  | 0 => (0 * 1 =? n)
  | S k' => if (k * (k + 1) =? n) then true else pNumberFrom k' n
  end.

Definition pNumber (n : nat) : bool :=
  pNumberFrom n n.
   (* FILL IN HERE *) (* admit. *)

Example pNumber_test1 : pNumber 56 = true.
Proof. 
  auto.
(* FILL IN HERE *)
Qed.

Example pNumber_test2 : pNumber 25 = false.
Proof. 
  auto.
(* FILL IN HERE *)
Qed.

(* 3. Let three sequences of numbers F1(n), F2(n) and F3(n) be given as follows.
   F1(0) = 1
   F1(n) = 2 * F1(n-1)   for n > 0.

   F2(0) = F2(1) = 1
   F2(n+2) = F2(n) + F2(n+1)    for n >= 0.

   F3(n) = F1(n) + F2(n)   for n >= 0.

Define the function Seq such that (Seq n) returns the sequence

[F1(0); F2(0); F3(0); F1(1); F2(1); F3(1); ... ; F1(n); F2(n); F3(n)].
*)

Fixpoint F1 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * F1 n'
  end.

Fixpoint F2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S n' => F2 n' + F2 (n'-1)
  end.

Definition F3 (n : nat) : nat := F1 n + F2 n.

Fixpoint Seq (n: nat) : list nat :=
  match n with 
  | 0 => [F1 0; F2 0; F3 0]
  | S n' => Seq n' ++ [F1 n; F2 n; F3 n]
  end.
(* FILL IN HERE *) (* admit. *)

Example Seq_test :  Seq 5 = [1; 1; 2; 2; 1; 3; 4;
       2; 6; 8; 3; 11; 16; 5; 21; 32; 8; 40].
Proof. 
  auto.
Qed.
(* FILL IN HERE *)
(* Admitted. *)

(* 4. Let modP be the predicate such that (modP n m) holds iff n is divisible 
by m. Prove the following theorem about modP. *)

Inductive modP : nat -> nat -> Prop :=
 | m0 : forall n, modP 0 (S n) 
 | m1 : forall n m, modP n m -> modP (n+m) m.

Lemma add_reorder : forall n m q : nat, n + m + q = n + q + m.
Proof.
  intros n m q.
  (* n + m + q = (n + m) + q *)
  rewrite <- Nat.add_assoc.
  (* = n + (m + q) *)
  rewrite (Nat.add_comm m q).
  (* = n + (q + m) *)
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

Theorem modP_add : forall p q m, modP p m -> modP q m -> modP (p+q) m.
Proof. (*FILL IN HERE*)
  intros.
  induction H.
  - simpl. assumption.
  - rewrite add_reorder. constructor. auto.
Qed.
(* Admitted. *)

(* 5. Write a function (transform):

      transform : list nat -> list (list nat )

   which transforms a list into a pair (l1, l2), where l1 
   contains all the odd numbers divisible by 3 in the original list; 
   and l2 contains all the other numbers. 
   The order of elements in the two sublists should be the same as their 
   order in the original list. 

   Hint: You may use the Coq function (filter).
*)
Definition odd_div3 (n : nat) : bool :=
  odd n && (n mod 3 =? 0).

Definition transform (l : list nat) : list nat * list nat :=
  (filter odd_div3 l, filter (fun x => negb (odd_div3 x)) l).
   (* FILL IN HERE *) (* admit. *)

Example transform_test: 
transform [3;7;6;9;4;5;16;14;15] = ([3; 9; 15],
       [7; 6; 4; 5; 16; 14]).
Proof. 
  auto.
Qed.
(* FILL IN HERE *) 
(* Admitted. *)

(* 6. Consider the following type:

Inductive btree : Set :=
 | leaf : btree 
 | node : nat -> btree -> btree -> btree.
 
Define a function cut such that, for any function 
test : nat -> bool, we have (cut test t) returns a subtree of t 
by replacing all subtrees whose roots do not pass test with leaf. 
*)

Inductive btree : Set :=
 | leaf : btree 
 | node : nat -> btree -> btree -> btree.

Fixpoint cut (test: nat -> bool) (t: btree) : btree :=
  match t with
  | leaf => leaf
  | node n l r =>
      if test n then
        node n (cut test l) (cut test r)
      else
        leaf
  end.
(* FILL IN HERE *) (* admit. *)

Example bt_test : cut odd (node 5 (node 1 leaf (node 3 leaf leaf)) 
                                   (node 9 (node 7 leaf leaf) (node 10 leaf leaf))) 
                   = (node 5 (node 1 leaf (node 3 leaf leaf)) 
                                   (node 9 (node 7 leaf leaf) leaf)).
Proof. 
  auto.
Qed.
(* FILL IN HERE *) 
(* Admitted. *)

(* 7. The following definitions specify the abstract syntax of
    some boolean expressions and an evaluation function. *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | Neg : bexp -> bexp
  | And : bexp -> bexp -> bexp
  | Or  : bexp -> bexp -> bexp.

Fixpoint eval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | Neg b => negb (eval b)
  | And b1 b2 => (eval b1) && (eval b2)
  | Or b1 b2 => (eval b1) || (eval b2)
  end.

(* Suppose we define a function that takes a boolean expression 
   and slightly simplifies it, changing every occurrence of [And BTrue b2] and
   [Or BFalse b2] into [b2], [And BFalse b2] into [BFalse], and [Or BTrue b2] 
   into [BTrue]. *)

Fixpoint optimize (b:bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse 
  | Neg BTrue => BFalse
  | Neg BFalse => BTrue
  | Neg b1 => Neg (optimize b1)
  | And BTrue b2 => optimize b2
  | And BFalse b2 => BFalse
  | And b1 b2 => And (optimize b1) (optimize b2)
  | Or BTrue b2 => BTrue
  | Or BFalse b2 => b2
  | Or b1 b2 => Or (optimize b1) (optimize b2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of boolean expressions. *)

Theorem optimize_sound: forall b,
  eval (optimize b) = eval b.
Proof. 
  intros.
  induction b; auto.
  - destruct b; auto; simpl; apply f_equal; apply IHb.
  - simpl; rewrite <- IHb1; rewrite <- IHb2; destruct b1; auto.
  - simpl; rewrite <- IHb1; rewrite <- IHb2; destruct b1; auto.
Qed.
(* FILL IN HERE *) 
(* Admitted. *)