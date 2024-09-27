Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Arith.Arith.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T : Type} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2 
                      (H1 : s1 =~ re1)
                      (H2 : s2 =~ re2)
                      : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2 (H : s1 =~ re1)
                      : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2 (H : s2 =~ re2)
                      : s2 =~ (Union re1 re2)
  | MStarO re : [] =~ (Star re)
  | MStarApp s1 s2 re 
                      (H1 : s1 =~ re)
                      (H2 : s2 =~ (Star re))
                      : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex3 : [1; 2 ; 3] =~ App (Char 1) (App (Char 2) (Char 3)).
Proof.
  apply (MApp [1] _ [2 ; 3]).
  -
    apply MChar.
  -
    apply (MApp [2] _ [3]).
    +
      apply MChar.
    +
      apply MChar.
Qed.

Fixpoint reg_exp_of_list {T : Type} (l : list T) :=
  match l with
  | [] => EmptyStr
  | h :: t => App (Char h) (reg_exp_of_list t)
  end.


Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  split.
  -
    intros HP.
    destruct H.
    +
      reflexivity.
    + 
      unfold not in H.
      contradiction H.
  -
    intros Hb.
    destruct H.
    +
      apply H.
    +
      discriminate Hb.
Qed.

Inductive isodd : nat -> Prop :=
  | e_1 : isodd 1
  | e_n (n : nat) (H : isodd n) : isodd (S (S n)).

Inductive iseven : nat -> Prop :=
  |o_O : iseven O
  |o_n : forall n , iseven n -> iseven (S (S n)). 

Example test_4 : iseven 4.
Proof.
  apply o_n.
  apply o_n.
  apply o_O.
Qed.

Print test_4.
(* test_4 = o_n 2 (o_n 0 o_O)
     : iseven 4 *)

Example test_4' : iseven 4.
Proof.
  Show Proof.
  apply o_n.
  Show Proof.
  apply o_n.
  Show Proof.
  apply o_O.
  Show Proof.
Qed.
(* ?Goal
(o_n 2 ?Goal)
(o_n 2 (o_n 0 ?Goal))
(o_n 2 (o_n 0 o_O)) *)

Definition test_4'' := o_n 2 (o_n 0 o_O).

Definition ev_plus2 : Prop :=
  forall n, forall (_ : iseven n), iseven (n + 2).
Definition ev_plus2' : Prop :=
  forall n, iseven n -> iseven (n + 2).

Check ev_plus2.

Definition ev_plus'' (n : nat) (H : iseven n) : iseven (2 + n) :=
  o_n n H.

Fixpoint get_length {T : Type} (l : list T) : nat :=
  match l with
  | [] => O
  | h :: t => S (get_length t)
  end.
Compute get_length [1;2;3].

Inductive is_equal {T : Type} : list T -> list T -> Prop :=
  | Nnil : is_equal [] []
  | NSS (t1 t2 : T) (l1 l2 : list T) (H : is_equal l1 l2) :
    is_equal (t1 :: l1) (t2 :: l2). 

Example testll : is_equal [1;2;3] [4;5;6].
Proof.
  apply NSS.
  apply NSS.
  apply NSS.
  apply Nnil.
Qed.

Definition add1 : nat -> nat.
  intro n.
  Show Proof.
  apply S.
  Show Proof.
  apply n. 
Defined.

Print add1.

(* Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q. *)

(* Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) =>
    match H1 with
    | conj HP HQ =>
      match H2 with
      | conj HQ' HR => conj HP HR
      end
    end.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl HP => or_intror HP
    | or_intror HQ => or_introl HQ
    end.








