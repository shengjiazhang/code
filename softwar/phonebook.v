Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.

(* 定义电话号码类型，这里简单用字符串表示 *)
Definition phone := string.

(* 电话簿定义为从名字（字符串）到电话号码列表的函数 *)
Definition phone_book := string -> list phone.

(* 定义一个空电话簿，任意名字都返回空列表 *)
Definition empty_phone_book : phone_book := fun _ => [].

(* 查找操作：直接返回电话簿中对应名字的电话号码列表 *)
Definition find_phone (pb: phone_book) (name: string) : list phone :=
  pb name.

(* 添加操作：如果名字匹配，则将电话号码 p 添加到列表前面；否则保持原值 *)
Definition add_phone (pb: phone_book) (name: string) (p: phone) : phone_book :=
  fun x => if String.eqb x name then p :: pb x else pb x.

(* 删除操作：如果名字匹配，则将对应列表清空；否则保持原值 *)
Definition del_phone (pb: phone_book) (name: string) : phone_book :=
  fun x => if String.eqb x name then [] else pb x.

(* 在 Coq 中，所有函数都是纯函数（immutable），所以不存在“就地修改”对象的概念。
   也就是说，我们无法直接修改传入的 phone_book，而是返回一个更新后的新的 phone_book。 *)
Definition phone_book1 := empty_phone_book.
Definition phone_book2 := add_phone phone_book1 "jiajia" "18739508251".
Definition phone_book3 := add_phone phone_book2 "lala" "18795845741".

Compute find_phone phone_book3 "lala".
Compute find_phone phone_book3 "jiajia".

(* 证明：添加电话号码后，通过查找操作返回的列表中包含该号码 *)
Theorem add_phone_contains : forall pb name p,
  In p (find_phone (add_phone pb name p) name).
Proof.
  intros pb name p.
  unfold find_phone, add_phone.
  (* 当 x = name 时，String.eqb name name 返回 true *)
  rewrite String.eqb_refl.
  simpl.
  left; reflexivity.
Qed.

