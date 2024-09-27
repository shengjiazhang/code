Require Import Coq.Arith.Arith.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.
Check nil.
Check cons.
(* list
     : Type -> Type
nil
     : forall X : Type, list X
cons
     : forall X : Type, X -> list X -> list X
 *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  |O => nil X
  |S n => cons X x (repeat X x n)
  end.
Check repeat.
(* repeat
     : forall X : Type, X -> nat -> list X
 *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'.
(* repeat'
     : forall X : Type, X -> nat -> list X
 *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.
Check repeat''.
(* repeat''
     : forall X : Type, X -> nat -> list X
 *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123 := cons 1 (cons 2 (cons 3 nil)).
Check list123.
(* list123
     : list nat
 *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.
Compute repeat''' 1 3.
(*      = cons 1 (cons 1 (cons 1 nil))
     : list nat
 *)

Inductive list' {X : Type} : Type :=
  |nil'
  |cons' (x : X) (l : list').
 
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check @nil.
Check [1;2;3].

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with 
  |[]=>None
  |h::tl => match n with
            | O => Some h
            | S n' => nth_error tl n'
            end
  end.

Compute nth_error [4;5;6;7] 0.
Compute nth_error [[1];[2]] 1.
Compute nth_error [true] 2.
(*   = Some 4
     : option nat
     = Some [2]
     : option (list nat)
     = None
     : option bool
 *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with 
  |[]=>None
  |h::tl => Some h
  end.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof.
  simpl.
  reflexivity.
Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof.
  reflexivity.
Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
Compute doit3times negb true.
(*   = false
     : bool
 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint evenb (n : nat) : bool :=
match n with
|O => true
|S O => false
|S (S n') => evenb n'
end.

Definition oddb (n : nat) : bool :=
let res := evenb n in
res.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof.
reflexivity.
Qed.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | h::tl => S (length tl)
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Compute filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ].
(*   = [ [3]; [4]; [8] ]. *)

Compute doit3times (fun n => n * n) 2 .
(* 2*2*2*2*2*2*2*2*2 = 8*8*8 = 256 *)

Definition partition {X : Type} (test : X -> bool) (l : list X) : (list X) * (list X) :=
  ((filter test l) , (filter (fun x => negb (test x)) l)).

Compute partition evenb [1;2;3;4;5].
(*   = ([2; 4], [1; 3; 5])
     : list nat * list nat
 *)

Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  |nil => nil
  |h::tl => (f h) :: (map f tl)
  end.
Compute map evenb [2;1;2;5].
(*   = [true; false; true; false]
     : list bool
 *)
Compute map (fun n => [evenb n ; oddb n]) [2;1;2;5].
(*   = [[true; true]; [false; false]; [true; true]; [false; false]]
     : list (list bool)
 *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Notation "l1 ++ l2" := (app l1 l2) (right associativity, at level 60).

(* 引理 *)
Lemma map_app_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| x xs IHl].
  - reflexivity.
  - simpl.
    rewrite map_app_distr.
    rewrite IHl.
    reflexivity.
Qed.

Fixpoint fold {X Y : Type} (f : X->Y->Y) (l : list X) (y : Y) : Y :=
  match l with
  | nil => y
  | h::tl => f h (fold f tl y)
  end.

Check @fold.
(* @fold
     : forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y *)

Fixpoint plus (n m : nat) : nat :=
match n with
|O => m
|S n' =>S (plus n' m)
end.
Check plus.

Compute fold plus [1;2;3;4] 0.
(*    = 10
     : nat *)

Compute fold app [[1];[];[2;3];[4]] [].
(*    = [1; 2; 3; 4]
     : list nat *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.

Check ftrue.
(* ftrue
     : nat -> bool *)

Compute ftrue 1.
Compute ftrue 2.
(* ftrue
     : nat -> bool
     = true
     : bool
     = true
     : bool *)

Check plus.
(* plus
     : nat -> nat -> nat *)

Definition plus3 := plus 3.
Check plus3.
(* plus3
     : nat -> nat *)

(* 3+5=8 *)
Compute plus3 5.
(*      = 8
     : nat *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun (_ : X) (n : nat) => S n) l O.

Compute fold_length [].
Compute fold_length [1;2;3].

Definition fold_map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
fold (fun (x : X) (y: list Y) => f x :: y) l [].
Compute fold_map evenb [2;1;2;5].
(*   = [true; false; true; false]
     : list bool
 *)












