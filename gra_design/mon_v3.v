From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Notation "1" := true.
Notation "0" := false.

Inductive is_valid : list bool -> Prop :=
  | valid_1 : is_valid [1]
  | valid_cons : forall (l : list bool) (b : bool), is_valid l -> is_valid (cons b l).

(* 一位全加器 *)
Definition full_adder (a b cin : bool) : bool * bool :=
  let sum := xorb a (xorb b cin) in
  let cout := (a && b) || (b && cin) || (a && cin) in
  (sum, cout).

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
          |h::t => pad t n ++ [ h ]
          end
  end.

Compute pad [1;1;0] 5.
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
Compute extend (ripple_carry_adder [1;1] [1;1;1;1] 0).

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

(* 移位函数 ,去除最低位，相当于把头部元素删掉，如果只有一位则为[0]*)
Definition shift (l : list bool) : list bool :=
  match l with
  | nil => nil 
  | [ _ ] => [0]
  | _ :: l'  => l' 
  end.

Compute shift [1;1;1].

(* 得到第列表中n位，n需要大于零并且小于length l，如果n大于length l输出缺省值0？ *)
Fixpoint get_index (n : nat) (l : list bool) : bool :=
  match l with
  |nil => 0 (* ? *)
  |h :: tl => match n with
              |O => h
              |S n' => get_index n' tl
              end
   end.

Compute get_index 4 [1;0;1;0].










