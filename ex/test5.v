(*给定自然数 n，欲判定其是否为偶数，则需递归检查 n-2 是否为偶数。*)
Fixpoint evenb(n : nat) : bool := 
match n with
|O=>true
|S 0=>false
|S (S n')=>evenb n'
end.

(*给定自然数 n，欲判定其是否为奇数*)
Definition oddb(n : nat) : bool :=
negb(evenb n).


(*多参数递归函数构造：递归定义加法*)
Fixpoint plus(n:nat) (m:nat) :nat :=
match n with
|O=>m
|S n'=>S(plus n' m)
end.

(*乘法*)
Fixpoint mult(n m :nat) : nat :=
match n with
|0=>O
|S n'=>plus m (mult n' m)
end.

(*减法*)
Fixpoint minus(n m :nat):nat :=
match n,m with
|O,O=>O
|O,S _=>O
|S _,O=>n
|S n',S m'=>minus n' m'
end.

(*幂*)
Fixpoint exp (n m :nat):nat:=
match m with
|O=>S O
|S m'=>mult n (exp n m')
end.

(* 阶乘 *)
Fixpoint factorial (n:nat):nat:=
match n with
|O=>S O
|S n'=>mult n (factorial n')
end.


(* 判断是否相等 *)
Fixpoint eql (n m : nat) : bool :=
match n with
|O=>match m with 
    |0=>true
    |S _=>false
    end
|S n'=>match m with
    |O=>false
    |S m'=>eql n' m'
    end
end.

Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
end.

Definition nege (n : bool) : bool :=
match n with
|true=>false
|false=>true
end.

Notation "x =? y" := (eql x y) (at level 70) : nat_scope.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition ltb (n m : nat) : bool :=
match n with 
|O => match m with 
    |O=>false
    |S _=>true
    end
|S _=>leb n m && nege (eql n m)
end.

Theorem plus_id_exercise : forall n m o:nat,
n = m -> m = o -> n + m = m + o.
Proof.
  intros.
  rewrite -> H.
  rewrite <- H0.
  reflexivity.
Qed.

Theorem mult_n_1 : forall n : nat,
n * 1 = n.
Proof.
intros.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
(n + 1) =? 0 = false.
Proof.
intros.
(*destruct 策略会生成_两个_子目标,as [| n'] 这种标注被称为 '引入模式'。它告诉 
Coq 应当在每个子目标中 使用什么样的变量名。总体而言，在方括号之间的是一个由 | 隔
开的 '列表的列表'。在上面的例子中，第一个元素是 一个空列表，因为 O 构造子是一个空
构造子（它没有任何参数）。 第二个元素提供了包含单个变量名 n' 的列表，因为 S 是一
个单构造子。*)
destruct n as [| n']. 
(*____________________________________(1/2)
(0 + 1 =? 0) = false
______________________________________(2/2)
(S n' + 1 =? 0) = false
*)
-reflexivity.
-reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
negb (negb b) = b.
Proof.
intros.
destruct b.
-reflexivity.
-reflexivity.
Qed.

Definition andb (b1 b2 : bool) : bool := 
match b1 with
|true=>b2
|false=>false
end.

Theorem andb_true_elim2 : forall b c : bool,
andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  - simpl in H. apply H.
  - destruct c.
    + reflexivity.
    + simpl in H. apply H.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
0 =? (n + 1) = false.
Proof.
intros.
destruct n as[|n'].
reflexivity.
reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall(b : bool), f (f b) = b.
Proof.
intros.
(* 
f : bool -> bool
H : forall x : bool, f x = x
b : bool
*)
rewrite H.
(*f b = b*)
rewrite H.
(*b = b*)
reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall(b : bool), f (f b) = b.
Proof.
intros.
rewrite H.
rewrite H.
(*negb (negb b) = b*)
apply negb_involutive.
(*应用上面已经证明过的定理，当然也可以使用destruct策略重新证明*)
Qed. 

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros.
destruct b,c.
-reflexivity.
-simpl in H.
 rewrite H.
 reflexivity.
-simpl in H.
 rewrite H.
 reflexivity.
-reflexivity.
Qed.

(*定义二进制表达，大端序*)
Inductive bin : Type :=
  | Z 
  | A (n:bin)
  | B (n:bin).

(*自增函数*)
Fixpoint incr (m:bin) : bin :=
match m with
|Z=>B Z
|A m'=>B m'
|B m'=>A (incr m')
end.

(*到自然数的转换*)
Fixpoint bin_to_nat (m:bin):nat := 
match m with
|Z=>O
|A m'=>2*(bin_to_nat m')
|B m'=>2*(bin_to_nat m')+1
end.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
intros.
induction n.
-
(*0 = 0 + 0*)
 reflexivity.
-
(* 1 goal
n' : nat
IHn' : n' = n' + 0
______________________________________(1/1)
S n' = S n' + 0
 *)
 simpl.
 rewrite <- IHn.
 reflexivity.
Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
intros.
induction n as[|n' IHn'].
-
  reflexivity.
-
  simpl.
  apply IHn'.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite->IHn.
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
(*应用上面已经证明的定理*)
-
  simpl.
  rewrite -> IHn.
  apply plus_n_Sm.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
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

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(*参数乘2*)

Lemma double_plus : forall n, double n = n + n .
Proof.
intros.
induction n.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite->IHn.
  rewrite->plus_n_Sm.
  reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). 
  { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
intros.
assert(H:n+m=m+n).
{
  apply plus_comm.
(*应用之前已经证明过的定理*)
} 
rewrite -> H.
reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
assert (H : n+(m+p)=n+m+p).
{
  rewrite plus_assoc.
(*加法结合律*)
  reflexivity.
}
assert (H' : m+n=n+m).
{
  apply plus_comm.
(*应用之前已经证明过的定理:加法交换律*)
}
rewrite H.
rewrite->plus_assoc.
rewrite H'.
reflexivity.
Qed.

Theorem mult_n_Sm : forall n m:nat,
  n * S m = n * m + n.
Proof.
  intros.
  induction n.
-
  simpl.
  reflexivity.
-
  simpl.
  rewrite IHn.
  rewrite<-plus_n_Sm.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [|m' IHm'].
-
  simpl. (* 根据乘法定义，0 * n = 0 = n * 0 *)
  rewrite mult_0_r. (* 使用乘法零右恒等性 *)
  reflexivity. (* 完成证明 *)
-
  simpl.
  rewrite IHm'.
  rewrite mult_n_Sm.
  rewrite plus_comm.
  reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
replace (n + (m + p)) with ((n + m) + p).
-replace (n + m) with (m + n).
 +rewrite plus_assoc.
  reflexivity.
 +apply plus_comm.
-rewrite plus_assoc.
 reflexivity.
Qed.

