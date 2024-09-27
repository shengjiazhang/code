Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.
From Coq Require Import Lia.

Notation "1" := true.
Notation "0" := false.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* 一位全加器 *)
Definition full_adder (a b cin : bool) : bool * bool :=
  let sum := xorb a (xorb b cin) in
  let cout := (a && b) || (b && cin) || (a && cin) in
  (sum, cout).

(* 把列表l2添加到l1后 *)
Fixpoint app (l1 l2 : list bool) : list bool :=
  match l1 with
  | nil => l2
  | n :: l1' =>n :: (app l1' l2)
  end.
Notation "l1 ++ l2" := (app l1 l2) (right associativity, at level 60).

(* 计算列表长度 *)
Fixpoint length(l:list bool) : nat :=
  match l with
  |nil=>0
  |h::t=>S (length t)
  end.

(* 获得两数中的最大值 *)
Fixpoint max(n m : nat) : nat :=
  match n , m with
  |O , O => O
  |O , S _ => m
  |S _ , O => n
  |S n', S m' => S (max n' m')
  end.

(* 用false/0填充较短的列表 [1;1;1] 5 => [1;1;1;0;0]*)
Fixpoint pad(l : list bool) (size : nat) : list bool :=
  match size with
  |O => l
  |S n => match l with
          |nil => 0::pad nil n
          |h::t => h :: pad t n
          end
  end.

(* 利用pad函数和max函数来确保两个列表具有相同的长度,如果其中有列表为nil则全为nil *)
Definition eql_length (l1 l2 : list bool) : (list bool * list bool) :=
  match l1 , l2 with
  |[] , [] | _ , [] | [] , _ => ([] , [])
  | _ , _ =>let len := max (length l1) (length l2) in
  (pad l1 len, pad l2 len)
  end.
(* Compute eql_length [1;1] [1;1;1]. *)

(* 行波进位加法器的定义，如果输入为空则输出也为空 *)
Fixpoint ripple_carry_adder_aux (xs ys : list bool) (cin : bool) : (list bool) * bool :=
  match xs, ys with
  | [], [] => ([], cin)
  | x::xt, y::yt =>
      let (sum, cout) := full_adder x y cin in
      let (rest, carry) := ripple_carry_adder_aux xt yt cout in
      (sum::rest, carry)
  | _, _ => ([], false) (* 长度不同，通过填充解决 *)
  end.
Definition ripple_carry_adder (xs ys : list bool) (cin : bool) : (list bool) * bool :=
  let (xs', ys') := eql_length xs ys in
  match xs', ys' with
  | [], [] => ([], cin)
  | _, _ => 
      let (sum, carry) := ripple_carry_adder_aux xs' ys' cin in
      (sum, carry)
  end.
Compute ripple_carry_adder [1;1] [1;1;1;1] 0.

(* 格式转换，如果进位为1则把进位放到列表中 ([0;1] 1)=>[0;1;1]，否则不放，如果列表为空则输入列表也为空 *)
Definition extend (res : list bool * bool) : list bool := 
  match res with
  |(nil , _)=> nil
  |(l , 1) => l ++ [ 1 ]
  |(l , 0) => l 
  end.
(* Compute extend (ripple_carry_adder [1;1] [1;1;1;1] 0).  *)

(* 把bool列表转化为nat，空列表则设为缺省值0 *)
Fixpoint bl_to_nat (l : list bool) : nat :=
  match l with
  |nil => O
  |[ true ]=> 1
  |h::t=>match h with
        |true=>S (2 * (bl_to_nat t))
        |false=>2 * (bl_to_nat t)
        end
  end.

Compute bl_to_nat (pad [] 6).
Compute bl_to_nat [].

(* 避免l为空 ,两个boollist相加输出为nat ，如果其中一个列表为空则输出缺省值0 *)
Definition bl_add (l1 l2 : list bool) : nat :=
  match l1 , l2 with
  |[] , [] | [] , _ | _ , [] => O
  |_ , _ => (bl_to_nat l1) + (bl_to_nat l2)
  end.

(* Compute bl_add [1] [1;1]. *)

(* 获得表头表尾 *)
Definition hd (l : list bool) : list bool :=
  match l with
  | nil => nil
  | h :: t=> [h]
  end.
Definition tl (l : list bool) : list bool :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* 引理1 *)
Lemma bl_to_nat_app_false : forall l, bl_to_nat (false :: l) = 2 * bl_to_nat l.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
(* 引理2 *)
Lemma bl_to_nat_app_true : forall l, bl_to_nat (true :: l) = S (2 * bl_to_nat l).
Proof.
  intros.
  destruct l.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.
(* 引理3 *)
Lemma ripple_carry_adder_nil : forall cin,
  ripple_carry_adder [] [] cin = ([], cin).
Proof.
  intros.
  reflexivity.
Qed.
(* 引理4 *)
Lemma pad_nil_bl_to_nat : forall size,
  bl_to_nat (pad [] size) = O.
Proof.
  intros.
  simpl.
  induction size.
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite IHsize.
    reflexivity.
Qed.
(* 引理5 *)
Lemma pad_O : forall l,
  pad l O = l.
Proof.
  intros.
  induction l.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.
Lemma app_b : forall b l l',
  (b::l) ++ l' = b::(l++l').
Proof.
  intros.
  reflexivity.
Qed.
(* 引理6 *)
Lemma pad_false_change_value:forall l,
  bl_to_nat (l ++ [0]) = bl_to_nat l.
Proof.
  intros l.
  induction l.
  -
    simpl.
    reflexivity.
  -
    rewrite app_b.
    destruct a.
    +
      rewrite bl_to_nat_app_true.
      rewrite -> bl_to_nat_app_true.
      rewrite IHl.
      reflexivity.
    +
      rewrite bl_to_nat_app_false.
      rewrite -> bl_to_nat_app_false.
      rewrite IHl.
      reflexivity.
Qed.

Axiom pad_size1 : forall l size,
 (size <= (length l)) -> ((pad l size) = l).

Axiom pad_size2 : forall l size,
 (size > (length l)) -> ((pad l (S size)) = (pad l size) ++ [0]).

(* 引理7 *)
Lemma pad_does_not_change_value : forall l size,
  bl_to_nat (pad l size) = bl_to_nat l.
Proof.
  intros l size.
Admitted.

Theorem adder_correct : forall l1 l2 : list bool,
  (l1<>nil /\ l2<>nil /\ (length l1 = length l2)) ->
  (bl_to_nat (extend (ripple_carry_adder l1 l2 0)) = bl_add l1 l2).
Proof.
Admitted.

Example adder_test1 : 
bl_to_nat (extend(ripple_carry_adder [1;1;1;1] [1;1;1;1] 0)) = bl_add [1;1;1;1] [1;1;1;1].
Proof.
  reflexivity.
Qed.

(* 移位函数 ,去除最低位，相当于把头部元素删掉，如果只有一位则为[0]*)
Definition shift (l : list bool) : list bool :=
  match l with
  | nil => nil 
  | [ _ ] => [0]
  | _ :: l'  => l' 
  end.

(* Compute shift [1]. *)

(* 得到第列表中n位，n需要大于零并且小于length l，如果n大于length l输出缺省值0？ *)
Fixpoint get_index (n : nat) (l : list bool) : bool :=
  match l with
  |nil => 0 (* ? *)
  |h :: tl => match n with
              |O => h
              |S n' => get_index n' tl
              end
   end.

(* Search option.
Compute get_index 3 [1;0;1;0].
Compute get_index 5 [1;0;1;0]. *)

(* 状态定义 *)
Inductive state : Type :=
|IDLE 
|START 
|WAIT1 
|CHECK 
|WAIT2 
|DONE.
(* Check state. *)

(* 定义状态机的状态和变量 *)
Definition current_state := IDLE.
Definition C := [0].
Definition reg_A := [0;0;1;0].
Definition reg_B := [0;0;0;1].
Definition reg_M := [0;0;1;1].
Definition cnt := O. (* 计数器，用于迭代 reg_A 的位 *)
Definition reg_C_0 : bool := 
xorb (get_index O C) (andb (get_index cnt reg_A) (get_index O reg_B)).
(* 对应于 Verilog 中的 reg_C_0 = C[0]^(reg_A[cnt]&reg_B[0]) *)
Definition add_start := 0.
Definition add_done := 0.
Definition add_res := [0].
Definition add_A := [0].
Definition add_B := [0].
Definition done := 0.
Definition reg_result := [0].

(* 状态转移函数 *)
Definition next_state current_state : state :=
  match current_state with
  | IDLE => if add_start then START else IDLE
  | START => if (cnt) =? (length (reg_A)) then DONE else
             if (get_index cnt reg_A) then WAIT1 else CHECK
  | WAIT1 => if add_done then CHECK else WAIT1
  | CHECK => if reg_C_0 then START else WAIT2
  | WAIT2 => if add_done then START else WAIT2
  | DONE => IDLE
  end.














