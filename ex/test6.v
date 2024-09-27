
(* 二元组 *)
Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

Notation "( x , y )" := (pair x y).

Definition fst (p:natprod) : nat := 
match p with
|(x , y)=>x
end.

Definition snd (p:natprod) : nat := 
match p with
|(x , y)=>y
end.

Definition swap_pair (p:natprod) : natprod :=
match p with
|(x , y)=>(y , x) 
end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p.
(* (snd (n1, n2), fst (n1, n2)) = swap_pair (n1, n2) *)
simpl.
reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.

(*数值列表*)
Inductive natlist : Type := 
|nil
|cons(n:nat )(l:natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* 生成一个含count个元素n的列表 *)
Fixpoint repeat(n count : nat) : natlist :=
match count with
|O=>nil
|S count'=>n::(repeat n count')
end.
(* 计算列表长度 *)
Fixpoint length(l:natlist) : nat :=
match l with
|nil=>0
|h::t=>S (length t)
end.
(* 把列表l2添加到l1后 *)
Fixpoint app(l1 l2 : natlist) : natlist :=
match l1 with
|nil=>l2
|h::t=>h::(app t l2)
end.

Notation "l1 ++ l2" := (app l1 l2) (right associativity, at level 60).

Fixpoint nonzeros (l:natlist) : natlist :=
match l with 
|nil=>l
|h::t=>match h with
      |O=>nonzeros t
      |S n=>h::nonzeros t
      end
end.

Compute nonzeros [0;1;0;2;3;0;0].

Fixpoint isodd (n : nat) : bool :=
match n with
|O=>false
|S O=>true
|S (S n')=>isodd n'
end.

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
|nil=>l
|h::t=>if (isodd h) then h::oddmembers t 
       else oddmembers t
end.

Compute oddmembers [0;1;0;2;3;5;0].

Fixpoint countoddmembers (l:natlist) : nat :=
match l with
|nil=>O
|h::t=>if (isodd h) then S (countoddmembers t)
       else countoddmembers t
end.

Compute countoddmembers [1;0;3;1;4;5].

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1,l2 with
|nil , _=>l2
|_ , nil=>l1
|h1::t1 , h2::t2=>[h1;h2] ++ (alternate t1 t2)
end.

Compute alternate [1;2;3] [4;5;6].
Compute alternate [1] [4;5;6].
Compute alternate [1;2;3] [4].
Compute alternate [] [20;30].

(* 前驱函数 *)
Definition pred (n : nat) : nat := 
match n with
|O=>O
|S n'=>n'
end.

(* 获得表头表尾 *)
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t=> h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
intros.
destruct l as [|n l'].
-
(* pred (length [ ]) = length (tl [ ]) *)
reflexivity.
-
(* pred (length (n :: l')) = length (tl (n :: l')) *)
reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros.
induction l1.
-
(* ([ ] ++ l2) ++ l3 = [ ] ++ l2 ++ l3 *)
  simpl.
  reflexivity.
-
(* IHl1 : (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3
______________________________________(1/1)
((n :: l1) ++ l2) ++ l3 = (n :: l1) ++ l2 ++ l3 *)
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.
(* 反转列表 *)
Fixpoint rev (l : natlist) : natlist :=
match l with 
|nil=>nil
|h::t=>rev t ++ [h]
end.
Compute rev [1;2;3].

(* 引理 *)
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
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
Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
intros.
induction n.
-
  reflexivity.
-
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + S m.
Proof.
intros.
induction n.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
-
  simpl.
  apply plus_n_O.
-
  simpl.
  rewrite IHn.
  apply plus_n_Sm.
Qed. 

(* 证明反转一个列表不会改变它的长度。 *)
Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
intros.
induction l.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite app_length.
  simpl.
  rewrite IHl.
  rewrite plus_comm.
  reflexivity.
Qed.

Search rev.
(* rev_length_firsttry: forall l : natlist, length (rev l) = length l *)

(* app_assoc: forall l1 l2 l3 : natlist,(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) *)
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
-
  simpl.
  induction l2.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite app_assoc.
    simpl.
    reflexivity.
-
  simpl.
  rewrite IHl1.
  rewrite app_assoc.
  reflexivity.
Qed.

(*引理rev_app_distr: forall l1 l2 : natlist,rev (l1 ++ l2) = rev l2 ++ rev l1 *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros.
induction l.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite rev_app_distr.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros.
induction l1.
-
  simpl.
  reflexivity.
-
  destruct n.
  +
    simpl.
    apply IHl1.
  +
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(*辅助函数*)
Fixpoint eql (n1 n2 : nat) : bool :=
match n1 , n2 with
|O , O => true
|O , S _ => false
|S _ , O=> false
|S n1' , S n2'=>eql n1' n2'
end.

Notation "x =? y" := (eql x y) (at level 70) : nat_scope.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1 , l2 with
|nil , nil=>true
|nil , _ =>false
|_ , nil=>false
|h1::t1 , h2::t2=>if h1=?h2 then eqblist t1 t2
                  else false
end.

Compute eqblist [1;2;3] [1;2;3].
Compute eqblist [1;2;3] [1;2;4].

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
intros.
induction l.
-
  simpl.
  reflexivity.
-
  simpl.
(* 引入引理：H : true = eql n n *)
  assert(H : true = eql n n ).
  {
    induction n.
    -
      simpl.
      reflexivity.
    -
      simpl.
      apply IHn.
  }
  rewrite <- H.
  apply IHl.
Qed.

Inductive natoption : Type :=
| Some (n : nat)
| None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
match l with
|nil=>None
|a::l'=>match n with 
       |O=>Some a
       |S n'=>nth_error l' n'
       end
end.

Compute nth_error [4;5;6;7] 0.
Compute nth_error [4;5;6;7] 4.

Definition option_elim (d : nat) (o : natoption) : nat :=
match o with 
|None=>d
|Some n'=>n'
end.
Compute option_elim 0 (nth_error [4;5;6;7] 0).

Definition hd' (l:natlist) :natoption :=
match l with
|nil=>None
|h::t=>Some h
end.
Compute hd' [1;2;3;6].

Inductive id : Type :=
|Id (n : nat).

Definition eqb_id (id1 id2 : id) : bool := 
match id1 , id2 with
|Id n1 , Id n2=>n1=?n2
end.
Compute (eqb_id (Id 1) (Id 1)).

Inductive partial_map : Type :=
|empty
|recard (i : id) (v : nat) (m : partial_map).

Definition update (i : id) (v : nat) (m : partial_map):= 
recard i v m.

Fixpoint find (x : id) (d : partial_map) : natoption :=
match d with
|empty=>None
|recard i v d'=>if eqb_id x i then Some v
                else (find x d')
end.
























