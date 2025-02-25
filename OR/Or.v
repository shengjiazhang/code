Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Import ListNotations.
Require Import Lia.
Require Import Coq.Reals.Reals.
Require Export PropExtensionality.
Require Import Extraction.

Lemma lt_imply_gt : forall n m : nat, n < m -> m > n.
Proof. intros. lia. Qed.

Lemma gt_imply_lt : forall n m : nat, n > m -> m < n.
Proof. intros. lia. Qed.

Lemma lt_ge_dec : forall x y : nat, {x < y} + {x >= y}.
Proof. intros. destruct (le_gt_dec y x); auto. Defined.

Infix "?<" := (lt_ge_dec) (at level 30).

(* Definition fin (n : nat) := {i | i < n}.

Lemma test : fin 0 -> False.
Proof.
  intros. destruct H. inversion l. 
Qed. *)

Definition fin (n : nat) :=
  match n with
  | O => unit
  | S n0 => {i | i < n}
  end.
Notation "''I_' n" := (fin n) (at level 40).
Definition vec {A : Type} (n : nat) := fin n -> A.
Notation "a .[ i ]" := ((a:vec _) (i:fin _)) (at level 2).

(* `fin 0` is unique  *)
Lemma fin_0_unique : forall i : fin 0, i = tt.
Proof. intros. induction i. auto. Qed.

(* Two `fin 0` is equal  *)
Lemma fin_0_eq : forall i j : fin 0, i = j.
Proof. intros. destruct i,j. auto. Qed.

(* Two `fin (S n)` is equal, iff value is equal *)
Lemma fin_S_eq : forall {n} x1 x2 (H1 : x1 < S n) (H2 : x2 < S n),
    exist (fun i => i < S n) x1 H1 = exist _ x2 H2 <-> x1 = x2.
Proof. 
  intros. split; intros.
  - inversion H. auto.
  - subst. apply f_equal. apply proof_irrelevance.  
Qed.

(* Two `fin (S n)` is not equal, iff, value is not equal  *)
Lemma fin_S_neq : forall {n} x1 x2 (H1 : x1 < S n) (H2 : x2 < S n),
    exist (fun i => i < S n) x1 H1 <> exist _ x2 H2 <-> x1 <> x2.
Proof.
  intros. rewrite fin_S_eq. reflexivity.
Qed.

Definition finEqdec : forall {n} (i j : fin n), {i = j} + {i <> j}.
Proof.
  intros. destruct n. destruct i,j; auto. destruct i as [i], j as [j].
  destruct (Nat.eq_dec i j).
  - subst. left. apply fin_S_eq; auto.
  - right. apply fin_S_neq; auto.
Defined.

Check fin 5.
Check vec 5.

Check lt_ge_dec.

Notation "[ | n ]" := (exist _ n _) (format "[ | n ]").

(** A default entry of `fin` *)
Definition fin0 {n : nat} : fin n :=
  match n with
  | O => tt
  | S n0 => exist _ 0 (Nat.lt_0_succ _)
  end.

(* fin n类型转化为nat类型 *)
Definition fin2nat {n} : fin n -> nat :=
  match n with
  | O => fun _ => 0                                (* if n=0, then 0  *)
  | S n0 => fun (f : fin (S n0)) => proj1_sig f    (* if n>0, then proj1(f) *)
  end.

Definition fin2nat' {n} (i : fin n) : nat.
  destruct n. 
  - apply 0.  
  - destruct i. apply x.
Defined.

(* proj1_sig 是 Coq 中用于处理类型 sig 的投影函数，它从一个 sig 类型的构造器中提取第一个组件。
sig 是一种用于表示依赖对的类型，其中每个值由两个部分组成：
第一部分是类型 A 的一个元素。
第二部分是一个关于第一部分的证明。
fin (S n0) 是一个 sig 类型的实例，它代表的自然数 f 确实小于等于 n0。proj1_sig f 返回的就是 f 中的自然数值。 *)

Lemma fin_eq_iff : forall {n} (f1 f2 : fin n), f1 = f2 <-> fin2nat f1 = fin2nat f2.
Proof.
  intros. destruct n.
  - destruct f1, f2. simpl. split; reflexivity.
  - destruct f1, f2. simpl. apply fin_S_eq.
Qed.

Lemma fin_neq_iff : forall {n} (f1 f2 : fin n), f1 <> f2 <-> fin2nat f1 <> fin2nat f2.
Proof.  intros. rewrite fin_eq_iff. split; auto. Qed.

Lemma fin2nat_lt_Sn : forall {n} (f : fin (S n)), fin2nat f < S n.
Proof. intros. simpl. destruct f. simpl. auto. Qed.

Lemma fin2nat_lt_n_gt0 : forall {n} (f : fin n), 0 < n -> fin2nat f < n.
Proof.
  intros. destruct n.
  - simpl. auto. 
  - apply fin2nat_lt_Sn.
Qed.

Lemma fin2nat_fin0 : forall {n}, @fin2nat n fin0 = 0.
Proof. intros. destruct n; simpl; reflexivity. Qed.

Definition nat2fin {n} (i : nat) : fin n.
  destruct n. apply tt.                     (* if n=0, tt : fin 0  *)
  destruct (i ?< S n).
  - refine [|i]. auto.                      (* if i< n, {i | i < S n} *)
  - refine [|0]. apply Nat.lt_0_succ.       (* if i>=n, {0 | 0 < S n} *)
Defined.

(** Convert from [nat] to [fin]
    nat类型转为fin S n类型 *)
Definition nat2finS {n} (i : nat) : fin (S n).
  destruct (i ?< S n).
  - refine [|i]. auto.                      (* if i< n, {i | i < S n} *)
  - refine [|0]. apply Nat.lt_0_succ.       (* if i>=n, {0 | 0 < S n} *)
Defined.

Notation "# i" := (nat2finS i) (at level 2).

Compute @fin2nat 3 (@nat2finS 2 2).
Compute @fin2nat' 3 (@nat2finS 2 2).

(* 拿到fin n集合中的所有元素 *)
Definition finseq (n : nat) : list (fin n) := 
  match n with 
  | O => []
  | S n' => map (@nat2finS _) (seq 0 n)
  end.

Lemma nat2fin_fin2nat_id : forall n (f : fin n), nat2fin (fin2nat f) = f.
Proof.
  intros. destruct n. 
  - simpl. destruct f. reflexivity.
  - destruct f. simpl fin2nat. simpl. destruct (x ?< S n).
    * apply fin_S_eq. reflexivity. 
    * lia.  
Qed.
  
Lemma fin2nat_nat2fin_id : forall n i, i < n -> fin2nat (@nat2fin n i) = i.
Proof.
  intros. unfold nat2fin, fin2nat. destruct n. lia.
  destruct (i ?< S n); simpl. reflexivity. lia.
Qed.
  
Lemma nat2fin_overflow : forall {n} i, i >= n -> @nat2fin n i = fin0.
Proof.
  intros.
  unfold nat2fin.
  destruct n. apply fin_0_eq.
  destruct (i ?<S n). lia. cbn. reflexivity.
Qed.
  
Lemma fin2nat_nat2fin_overflow : forall n i, i >= n -> fin2nat (@nat2fin n i) = 0.
Proof.
  intros. destruct (i ?< n). lia. rewrite nat2fin_overflow; auto.
  apply fin2nat_fin0.
Qed.

(** Convert from [fin n] to [fin m] *)
Definition fin2fin {n m} (f : fin n) : fin m := nat2fin (fin2nat f).

(** ** Conversion between nat-Function (f) and Fin-Function (ff) *)
Section ff2f_f2ff.
  Context {A} {Azero : A}.

  (** `ff` to `f` *)
  Definition ff2f {n} (ff : fin n -> A) : nat -> A := fun i => ff (nat2fin i).
  
  (** `f` to `ff` *)
  Definition f2ff {n} (f : nat -> A) : fin n -> A := fun i => f (fin2nat i).

  (* Note: Equality of two nat-function is defined on top n elements *)
  Lemma ff2f_f2ff_id : forall {n} (f : nat -> A) i, i < n -> @ff2f n (f2ff f) i = f i.
  Proof. intros. unfold f2ff,ff2f. rewrite fin2nat_nat2fin_id; auto. Qed.
  
End ff2f_f2ff.   

Notation "v .1" := (v (@nat2finS _ 0)) (at level 2).
Notation "v .2" := (v (@nat2finS _ 1)) (at level 2).
Notation "v .3" := (v (@nat2finS _ 2)) (at level 2).

Notation "v .x" := (v.1) (at level 2).

(* 列表到向量 *)
Definition l2v {A} n {Azero:A} (l : list A) : vec n := fun i => nth (fin2nat i) l Azero.

(* 向量到列表 *)
Definition v2l {A} {n} (v : vec n) : list A := map v (finseq n).

Definition f2v {tA} {n} (f : nat -> tA) : @vec tA n := fun i => f (fin2nat i).

Compute l2v 2 [R0; R1].

Compute v2l (l2v 2 [R0; R1]).

Definition vrepeat {tA : Type} (n : nat) (a : tA) : @vec tA n := fun _ => a.

Definition vzero {tA n Azero}: @vec tA n := vrepeat n Azero.

Compute v2l (vrepeat 3 R0).

(* 定义向量相加函数 *)
Definition vadd {n : nat} (v1 v2 : vec n) : vec n :=
  fun i => Rplus (v1 i) (v2 i).
Infix "+" := vadd : vec_scope.

(* 向量乘法 *)
Definition vcmul {n : nat} (k : R) (v : vec n) : vec n :=
  fun i => Rmult k (v i).
Notation "k \.* a" := (vcmul k a) (at level 40, left associativity).

(* 向量减法 *)
Definition vsub {n : nat} (v1 v2 : vec n) : vec n :=
  vadd v1 (vcmul (-1) v2).

(* 向量点积函数 *)
Definition vdot {n : nat} (v1 v2 : vec n) : R :=
  fold_left Rplus (v2l (fun i => Rmult (v1 i) (v2 i))) 0%R.
Notation "< a , b >" := (vdot a b) (at level 0, no associativity) : vec_scope.

(* 向量模长 *)
Definition vlen {n : nat} (v : vec n) : R :=
  sqrt (vdot v v).
Notation "|| a ||" := (vlen a) (at level 40) : vec_scope.

(* 向量是否为单元向量 *)
Definition vunit {n : nat} (v : vec n) : Prop :=
  (vlen v) = 1%R.

Definition vorth {n : nat} (v1 v2 : vec n) : Prop :=
  (vdot v1 v2) = 0%R.
Notation "a _|_ b" := (vorth a b) (at level 50, no associativity) : vec_scope.

Open Scope vec_scope.
Open Scope R_scope.

(* 投影函数 *)
Definition vproj {n : nat} a b : vec n := ((vdot a b) / (vdot b b)) \.* b.
Definition vperp {n : nat} a b : vec n := vadd a (vcmul (-1) (vproj a b)).

(* 对向量正规化 *)
Definition vnorml {n : nat} (v : vec n) : vec n :=
  fun i => Rdiv (v i) (vlen v).

(* 求两个向量夹角 *)
Definition vangle {n : nat} (v1 v2 : vec n) : R :=
  acos (Rdiv (vdot v1 v2) (Rmult (vlen v1) (vlen v2))).
Notation "a /_ b" := (vangle a b) (at level 50, no associativity) : vec_scope.

(* 两个向量×乘 *)
Definition v3cross (a b : vec 3) : vec 3 :=
  @l2v R 3 0%R [a.2 * b.3 - a.3 * b.2; a.3 * b.1 - a.1 * b.3; a.1 * b.2 - a.2 * b.1].
Notation "a \x b" := (v3cross a b) (at level 50, no associativity) : vec_scope.

(* 累积 *)
Fixpoint lprod (l : list R) (r : R) : R :=
  match l with
  | [] => r 
  | h :: t => h * (lprod t 1)
  end.

(* 求一个向量累积 *)
Definition vprod {n} (a : @vec R n) := lprod (v2l a) 1.
Notation "\prod a" := (vprod a) (at level 2) : vec_scope.

(* 对向量正规化 *)
Definition vnorm {n} (a : vec n) : vec n := vcmul (1 / (vlen a)) a.

Definition vtest : vec 2 := (@l2v R 2 0 [R1; R1]).
Compute v2l (@vnorml 2 vtest).
Compute v2l (@vnorm 2 vtest).

Definition vzeroN (n : nat) : vec n := @l2v R n 0 (repeat 0 n).

Compute vzeroN 5.

(** i = j -> a.[nat2fin i] = a.[nat2fin j] *)
 Lemma vnth_eq : forall {tA n} (a : @vec tA n) i j (Hi : lt i n) (Hj : lt j n),
    i = j -> a.[nat2fin i] = a.[nat2fin j].
Proof. intros. subst. f_equal. Qed.















(* 矩阵r行c列 *)
Definition mat A r c := (@vec (@vec A c) r).
Notation smat A n :=(mat A n n).

Definition fequ {n} (i j : fin n) : bool := fin2nat i =? fin2nat j.

Definition mat1 {n} : smat R n := fun i j => if (fequ i j) then 1 else 0.

Notation cvec A n := (mat A n 1). (*列向量*)
Notation rvec A n := (mat A 1 n). (*行向量*)

(* 列表到矩阵 
   先把列表中的每个元素(list tA)转化为vec c。然后再对一个list (vec c)类型的列表转化为 vec {vec c} r*)
Definition l2m {tA r c} {vzero : vec c} {Azero : tA} (d : list (list tA)) : mat tA r c :=
  @l2v (vec c) r vzero (map (@l2v tA c Azero) d).

(* 矩阵到列表 *)
Definition m2l {A r c} (m : mat A r c) : list (list A) := map v2l (v2l m).

Compute @l2m R 4 2 (vzeroN 2) 0 [[0;1]; [1;2]; [2;3]; [3;4]].
Compute @m2l R 4 2 (@l2m R 4 2 (vzeroN 2) 0 [[0;1]; [1;2]; [2;3]; [3;4]]).

(* 矩阵转置 *)
Definition mtrans {tA r c} (M : mat tA r c) : mat tA c r := fun i j => M j i.
Notation "m \T" := (mtrans m) (at level 40, left associativity).

(* 矩阵加法 *)
Definition madd {r c} (M1 M2 : mat R r c) : mat R r c :=
  fun i j => (M1 i j) + (M2 i j).
Definition mtest := @l2m R 2 2 (vzeroN 2) 0 [[1;1]; [1;1]].
Compute @m2l R 2 2 (madd mtest mtest).

(* 矩阵标量乘法 *)
Definition mcmul {r c} (k : R) (M : mat R r c) : mat R r c :=
  fun i j => k * (M i j).

(* 矩阵相乘 *)
Definition mmul {r c s} (M1 : mat R r c) (M2 : mat R c s) : mat R r s :=
  fun i j => vdot (M1 i) (fun k => M2 k j).

(* 矩阵与向量相乘 *)
Definition mmulv {r c} (M : mat R r c) (v : vec c) : vec r :=
  fun i => vdot (M i) v. 
Notation "m *v v" := (mmulv m v) (at level 40, left associativity).

(* 从列表中选择第 k 个元素：该函数通过递归遍历列表，根据索引 k 的值，返回第 k 个元素。
返回新列表：同时返回删除该元素后的剩余列表。 *)
Fixpoint pick {tA : Type} (Azero : tA) (l : list tA) (k : nat) : tA * list tA :=
  match k with
  | 0 => (hd Azero l, tl l)
  | S k' =>
      match l with
      | [] => (Azero, [])
      | x :: l' =>
          let (a,l0) := pick Azero l' k' in
          (a, ([x] ++ l0)%list)
      end
  end.


(* seq 0 n：生成序列 [0, 1, ..., n-1]，表示从 0 到 n-1 的自然数索引，这些索引用于从列表 l 中依次挑选元素。

map (fun i => pick Azero l i)：对每个索引 i，调用函数 pick，从列表 l 中选择第 i 个元素，并返回一个二元组 (x, lx)，
其中 x 是选中的第 i 个元素，lx 是去掉该元素后的剩余列表，最后生成一个二元组的列表。

map (fun k => ...)：对每个 pick 函数返回的二元组 (x, lx)，递归调用 permAux Azero n' lx，
从去掉元素 x 的列表 lx 中生成长度为 n' 的排列。然后通过 map (cons x) 将元素 x 放到每个生成的排列前面，形成新的排列。
let '(x, lx) := k in 使用的是模式匹配的语法，称为析构绑定（destructuring binding）。
模式匹配：这个语法用于直接从元组 k 中提取元素。k 应该是一个二元组 (x, lx)，其中 x 是第一个元素，lx 是第二个元素。
' 符号：在这里，单引号表示模式匹配，即将 k 解构为其组成部分。它在 Coq 中是必要的，表示将 k 进行模式匹配而不是直接将其视为一个变量。

map (cons x) (permAux Azero n' lx) 作用在(permAux Azero n' lx)生成的列表[l1;l2;l3...]，其中ln类型为list tA，作用之后就变成了：
[x::l1; x::l2...]相当于是把头元素加了进去，这样得到的一个列表类型为list (list tA)，又因为fun k =>...，是对每个k都进行这样的映射操作，
因此最后得到的列表为：[[x1::l11; x1::l12...]; ...; [xn::ln1; x2::ln2]]，类型为list (list (list tA))。所以要用一个concat。
其中xi为列表l中的元素,对应的lij则为其全排列组合的一种情况。

concat：最后将所有生成的排列组合(list (list (list tA)))成一个平坦的列表list (list tA)。 *)
Fixpoint permAux {tA : Type} (Azero : tA) (n : nat) (l : list tA) : list (list tA) :=
  match n with
  | 0 => [[]]
  | S n' =>
      concat
        (map
           (fun k =>
              let '(x, lx) := k in
              map (cons x) (permAux Azero n' lx))
           (map (fun i => pick Azero l i) (seq 0 n)))
  end.

(** Get permutation of a list *)
Definition perm {tA : Type} (Azero : tA) (l : list tA) : list (list tA) := permAux Azero (length l) l.

Compute perm 0%nat [1%nat;2%nat;3%nat].

(* 累乘，acc中保存当前的乘积，f为当前位置的映射函数，得到f(0)到f(n)累乘的结果 *)
Fixpoint seqprodAux (n : nat) (f : nat -> R) (acc : R) : R :=
  match n with
  | O => acc
  | S n' => seqprodAux n' f (f n' * acc)
  end.
Definition seqprod (n : nat) (f : nat -> R) : R := seqprodAux n f 1.

Definition f2m {tA : Type} {r c} (f : nat -> nat -> tA) : mat tA r c :=
  @f2v _ r (fun i => @f2v tA c (f i)).


(* 用于计算列表 l 中有多少元素小于给定的自然数 a。
   n 是当前累加器的值，表示到目前为止已找到的比 a 小的元素的个数。
   b 是当前遍历的列表中的元素。 *)
Definition ronum1 (a : nat) (l : list nat) : nat :=
  fold_left (fun (n : nat) (b : nat) => Nat.add n (if b ?< a then 1 else 0)) l 0%nat.

Compute ronum1 3 [1%nat;2%nat;4%nat;5%nat].

(* ronum l 计算排列 l 的逆序数（即多少个元素对发生了反转）
  逆序数（inversion number）是用来描述一个排列中两个元素相对顺序是否与它们的大小相反的概念。
  具体来说，逆序数表示在一个排列中，有多少对元素的顺序是与其在自然顺序中应该呈现的顺序相反的。
  如果排列的逆序数是偶数，则称该排列为偶排列，行列式项不需要改变符号。
  如果逆序数是奇数，则称为奇排列，行列式项需要乘以 -1。 *)
Fixpoint ronum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => ronum1 x l' + ronum l'
  end.

Compute perm O (seq O 4).

(* 求行列式 *)
Definition mdet {n} : smat R n -> R :=
  match n with
  | O => fun _ => 1        (* the determinant of a empty matrix is 1 *)
  | S n' =>
      fun (M : smat R (S n')) =>
        (* 列号 0,1,..,(n-1) 的全排列 *)
        let colIds := perm O (seq O n) in
        (* 每个式 *)
        let item (l:list nat) : R :=
          (let x := seqprod n (fun i => M.[#i].[#(nth i l O)]) in (* i是行，(nth i l O)找到当前列的第i个元素，缺省值为0 *)
           if odd (ronum l) then - x else x) in
        (* 求和 *)
        fold_left Rplus (map item colIds) 0 (* item中的l就是colIds中的元素 *)
  end.

Compute @mdet 2 (l2m [[1;2]; [1;1]]).

Definition msubmatNat (M : nat -> nat -> R) (i j : nat) : nat -> nat -> R :=
  fun i0 j0 =>
    M (if i0 ?< i then i0 else S i0) (if j0 ?< j then j0 else S j0).
  
(* 得到(M i j)的余子矩阵 *)
Definition msubmat {n} (M : smat R (S n)) (i j : 'I_(S n)) : smat R n :=
  fun i0 j0 =>
    let i1 := if (fin2nat i0) ?< (fin2nat i) then #(fin2nat i0) else #(S (fin2nat i0)) in
    let j1 := if (fin2nat j0) ?< (fin2nat j) then #(fin2nat j0) else #(S (fin2nat j0)) in
    M.[i1].[j1].

(* 求其行列式 *)
Definition mminor {n} (M : smat R (S n)) (i j : 'I_(S n)) : R := mdet (msubmat M i j).

(* 求其对应的代数余子式 *)
Definition mcofactor {n} (M : smat R (S n)) (i j : 'I_(S n)) : R :=
  let x := mminor M i j in
  if Nat.even (fin2nat i + fin2nat j) then x else - x.

(* 求伴随矩阵，余子式矩阵的转置 *)
Definition madj {n} : smat R n -> smat R n := 
  match n with
  | O => fun M => M 
  | S n' => fun M i j => mcofactor M j i (* 转置 *)
  end.
Notation "M \A" := (madj M) (at level 2) : mat_scope.

Compute @m2l R 2 2 (@madj 2 (l2m [[1;2]; [1;1]])).

Definition minvAM {n} (M : smat R n) := mcmul (Rdiv 1 (mdet M)) (madj M). (*求逆矩阵 *)

Compute @m2l R 2 2 (@mmul 2 2 2 (l2m [[1;2]; [1;1]]) (@minvAM 2 (l2m [[1;2]; [1;1]]))).


















Definition quat := @vec R 4. 

Notation "q .W" := (q (@nat2finS _ 0)) (at level 2).
Notation "q .X" := (q (@nat2finS _ 1)) (at level 2).
Notation "q .Y" := (q (@nat2finS _ 2)) (at level 2).
Notation "q .Z" := (q (@nat2finS _ 3)) (at level 2).

(* quat -> vec 3 *)
Definition q2im (q : quat) : vec 3 := @l2v R 3 0%R [q.X; q.Y; q.Z].

(* vec 3 -> quat，标量部分补0 *)
Definition im2q (q : vec 3) : quat := @l2v R 4 0%R [0; q.X; q.Y; q.Z].

(* W -> vec 3 -> quat *)
Definition si2q (w : R) (v : vec 3) : quat := @l2v R 4 0%R [w; v.1; v.2; v.3].

(* 四元组矢量部分取负，求逆 *)
Definition qconj (q :  quat) : quat := @l2v R 4 0 [q.W; -q.X; -q.Y; -q.Z].

(* 轴角 -> 四元组 *)
Definition aa2q (n : vec 3) (θ : R) : quat := @l2v R 4 0 [cos (θ/2); sin (θ/2) * n.1; sin (θ/2) * n.2; sin (θ/2) * n.3].

(* 求四元组长度 *)
Definition qlen (q : quat) : R :=
  sqrt(q.W * q.W + q.X * q.X + q.Y * q.Y + q.Z * q.Z).

(* 是否为单位四元组 *)
Definition qunit (q : quat) : Prop := qlen q = 1.

(** ** Quaternion addition 四元数加法 *)
Definition qadd (q1 q2 : quat) : quat := vadd q1 q2.

(** ** Quaternion negation 四元数取负 *)
Definition qopp (q : quat) : quat := vcmul (-1) q.

(* Quaternion subtraction 四元数减法 *)
Definition qsub (q1 q2 : quat) : quat := qadd q1 (qopp q2).

(* 四元数乘法 *)
Definition qmul (q1 q2 : quat) : quat :=
  @l2v R 4 0 [q1.W * q2.W - q1.X * q2.X - q1.Y * q2.Y - q1.Z * q2.Z;
       q1.W * q2.X + q1.X * q2.W + q1.Y * q2.Z - q1.Z * q2.Y; 
       q1.W * q2.Y - q1.X * q2.Z + q1.Y * q2.W + q1.Z * q2.X;
       q1.W * q2.Z + q1.X * q2.Y - q1.Y * q2.X + q1.Z * q2.W].

(* 四元组 -> 矩阵，涉及左右两个矩阵
   q1*q2 = ML(q1)q2 /\ q1*q2 = MR(q2)*q1 *)
Definition qmatL (q : quat) := let '(w,x,y,z) := (q.W,q.X,q.Y,q.Z) in
  @l2m R 4 4 (@l2v R 4 0 [0;0;0;0]) 0 [[w;-x;-y;-z]; [x;w;-z;y]; [y;z;w;-x]; [z;-y;x;w]].

Definition qmatR (q : quat) := let '(w,x,y,z) := (q.W,q.X,q.Y,q.Z) in
  @l2m R 4 4 (@l2v R 4 0 [0;0;0;0]) 0 [[w;-x;-y;-z]; [x;w;z;-y]; [y;-z;w;x]; [z;y;-x;w]].

Lemma qmatL_spec: forall p q, qmul p q = mmulv (qmatL p) q.
Proof.
Admitted.









(* 矩阵M每一行都是单位矩阵/\行与行相互正交 *)
Definition mcolsOrth {r c} (M : mat R r c) : Prop :=
(forall i, vunit (M i)) /\ (forall j k, j <> k -> M j _|_ M k).

(* M是否为正交矩阵 *)
Definition morth {n} (M : smat R n) : Prop := mmul (M\T) M = mat1.

(* M是正交矩阵且M行列式为1 *)
Definition SOnP {n} (M : smat R n): Prop := (morth M) /\ (mdet M) = 1.

Lemma morth_iff_mcolsOrth : forall {n} (M : smat R n), morth M <-> mcolsOrth M.
Proof.
Admitted.

Context {n : nat} (M N : smat R n) (a b : @vec R n).
Lemma morth_keep_dot : morth M -> vdot (M *v a) (M *v b) = (vdot a b).
Proof.
Admitted.
Lemma morth_keep_length : morth M -> vlen (M *v a) = vlen a. (* ... *)
Proof.
Admitted.

Lemma morth_keep_angle : morth M -> (M *v a) /_ (M *v b) = a /_ b.
Proof.
Admitted.

Lemma SO3_keep_v3cross :forall (M : smat R 3) (a b : @vec R 3), SOnP M -> (M *v a) \x (M *v b) = M *v (a \x b).
Proof.
Admitted.

Definition Rx (θ : R) : smat R 3 :=
  @l2m R 3 3 (@vzero R 3 0) 0 [[1; 0; 0]; [0; cos θ; -sin θ]; [0; sin θ; cos θ]]. 
Definition Ry (θ : R) : smat R 3 :=
  @l2m R 3 3 (@vzero R 3 0) 0 [[cos θ; 0; sin θ]; [0; 1; 0]; [-sin θ; 0; cos θ]].
Definition Rz (θ : R) : smat R 3 :=
  @l2m R 3 3 (@vzero R 3 0) 0 [[cos θ; -sin θ; 0]; [sin θ; cos θ; 0]; [0; 1; 1]].

Variable θ1 θ2 θ3 :R.
Notation c1 := (cos θ1).
Notation c2 := (cos θ2).
Notation c3 := (cos θ3).
Notation s1 := (sin θ1).
Notation s2 := (sin θ2).
Notation s3 := (sin θ3).

Definition S123 (c1 c2 c3 : R) : smat R 3 :=
  @l2m R 3 3 (@vzero R 3 0) 0 
  [[c2 * c3; s1 * s2 * c3 - c1 * s3; c1 * s2 * c3 + s1 * s3];
   [c2 * s3; s1 * s2 * s3 + c1 * c3; c1 * s2 * s3 - s1 * c3];
   [- s2; s1 * c2; c1 * c2]].

Theorem S123_spec : S123 c1 c2 c3 = mmul (mmul (Rz θ3) (Ry θ2)) (Rx θ1).
Proof.
Admitted.

Lemma S123_phi_singular : forall φ θ ψ : R, (θ = PI/2)/\ (θ = -PI/2) ->
                            forall φ' : R, exists ψ' : R, (S123 φ', θ, ψ') = (S123 φ, θ, ψ).
Proof.
Admitted.

(* atan2 函数：接受 y 和 x 两个参数，返回 [-pi, pi] 范围内的角度 *)
Definition atan2 (y x : R) : R := 0.
Definition ϕ' (C : smat R 3) := atan (C.3.2 / C.3.3).
Definition θ' (C : smat R 3) := asin (-C.3.1).
Definition ψ' (C : smat R 3) := atan (C.2.1 / C.1.1).












Definition qrot (q p : quat) : quat := qmul (qmul q p) (qconj q).
Definition qrotv (q : quat) (a:vec 3) : vec 3 := q2im (qrot q (im2q a)).

(* Q操作标量不变 *)
Lemma qrot_keep_w: forall p q:quat, (qrot q p).W = p.W.
Proof.
Admitted.
(* QV操作点积不变 *)
Lemma qrot_keep_dot: forall (q:quat) (a b:vec 3), vdot (qrotv q a) (qrotv q b) = vdot a b.
Proof.
Admitted.

Definition ab2q (a b : vec 3) : quat := si2q (vdot a b) (v3cross a b).
Definition ab2q' (a b : vec 3) : quat := qmul (im2q b) (qconj (im2q a)).
Lemma ab2q_eq_ab2q' : forall a b, ab2q a b = ab2q' a b.
Proof.
Admitted.

Lemma ab2q_eq : forall (a b : vec 3), let q := ab2q a b in
  let c := qrotv q a in vunit a -> vunit b -> ab2q b c = q.
Proof.
Admitted.

Fact vlen_vv' : forall (v : vec 3) (q : quat), vlen v = vlen (qrotv q v).
Proof.
Admitted.

(* 保角 *)
Fact vangle_vv' : forall (θ : R) (q : quat) (n v0 v1 : vec 3) (s0 s1 s2 : R),
  let v:=(vadd (vadd (s0 \.* v0)  (s1 \.* v1)) (s2 \.* n)) in
  let v':=(qrotv q v) in
  (Rlt 0 θ) -> (Rlt θ (2*PI))->
  (vunit v0)->(vunit v1)->(vnorm (v3cross v0 v1) = n)->((vangle v0 v1) = θ/2)->(s0<>0)->(s1<>0)->
  vangle (vperp v n) (vperp v' n) = θ. 
Proof.
Admitted.

(* 轴角到3D向量，即a沿n旋转θ。 *)
Definition rotaa (θ : R) (n : vec 3) (a : vec 3) : vec 3 :=
  vadd (vadd (vcmul (vdot a n) n) (vcmul (cos θ) (vsub a (vcmul (vdot a n) n)))) (vcmul (sin θ) (v3cross n a)).

Lemma qrot_spec_byAxisAngle : forall (θ : R) (n v : vec 3),
  vunit n -> qrotv (aa2q n θ) v = rotaa θ n v.
Proof.
Admitted.

Definition qzero : quat := @l2v R 4 0%R [0; 0; 0; 0].

Lemma qrot_twice : forall (q1 q2:quat) (v:vec 3), 
q1 <> qzero -> q2 <> qzero ->
qrot q2 (qrot q1 (im2q v)) = qrot (qmul q2 q1) (im2q v).
Proof.
Admitted.

(* 四元组转化为3*3矩阵 *)
Definition q2m (q : quat) := let '(w,x,y,z) := (q.W,q.X,q.Y,q.Z) in
  @l2m R 3 3 (@l2v R 3 0 [0;0;0]) 0 
  [[w*w+x*x-y*y-z*z;2*(x*y-w*z);2*(x*z+w*y)]; 
   [2*(x*y+w*z);w*w-x*x+y*y-z*z;2*(y*z-x*w)]; 
   [2*(x*z-y*w);2*(y*z+w*x);w*w-x*x-y*y+z*z]].

Lemma q2m_spec : forall (q : quat) (v : vec 3),  qunit q -> qrotv q v = (q2m q) *v v.
Proof.
Admitted.

