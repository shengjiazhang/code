(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector implemented with Fin-fun model
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
  1. High-dimensional vectors can be expressed by repeating the `vec` structure.
  2. Four forms of a "list/function/vector"
     
     FF --- vec
     | \  / |
     |  \/  |
     |  /\  |
     | /  \ |
     F ---- list
     
     FF: Fin-indexing-Function,
     F : natural-number-indexing-Function
     vec : vector has given length, made be list
     list : a list of data
     
     These forms have conversion functions between each other.
 *)


Require Export FinMatrix.CoqExt.ListExt.
Require Export FinMatrix.CoqExt.Hierarchy.
Require Import FinMatrix.CoqExt.RExt.
Require Export FinMatrix.Matrix.Fin.
Require Export FinMatrix.Matrix.Sequence.
Require Import Extraction.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.
Generalizable Variable tB Badd Bzero.

(** Control the scope *)
Open Scope R_scope.
Open Scope nat_scope.
Open Scope A_scope.
Open Scope vec_scope.

(* ######################################################################### *)
(** * vec type and basic operations *)

(* ======================================================================= *)
(** ** Definition of vector type [vec] *)

(** A n-dimensional vector over tA type *)
Definition vec {tA : Type} (n : nat) := 'I_n -> tA.

(** Make a vec type explicitly *)
Definition vmake {tA : Type} {n : nat} (f : 'I_n -> tA) : @vec tA n := f.

(* ======================================================================= *)
(** ** Get element of a vector *)

(** v.i *)
(* Definition vnth {tA n} (a : @vec tA n) (i : 'I_n) : tA := a i. *)
(* Notation "a .[ i ]" := (vnth a i) : vec_scope. *)

Notation vnth tA n a i := ((a : @vec tA n) (i : 'I_n)).
Notation "a .[ i ]" := (vnth _ _ a i) : vec_scope.

(** i = j -> a.[nat2fin i] = a.[nat2fin j] *)
Lemma vnth_eq : forall {tA n} (a : @vec tA n) i j (Hi: i < n) (Hj: j < n),
    i = j -> a.[nat2fin i Hi] = a.[nat2fin j Hj].
Proof.
  intros. subst. apply f_equal. fin.
Qed.
(* Proof. intros. subst. f_equal. apply fin_eq_iff; auto. Qed. *)

(* Note that: these notatiosn are dangerous.
   For example, `@nat2finS 3 0` ~ `@nat2finS 3 3` are all expected index.
   but `@nat2finS 3 4` ~ `...` will become `@nat2finS 3 0`, its error index.
 *)
Notation "a .1" := (a.[#0]) : vec_scope.
Notation "a .2" := (a.[#1]) : vec_scope.
Notation "a .3" := (a.[#2]) : vec_scope.
Notation "a .4" := (a.[#3]) : vec_scope.

(* These notations are disabled, see the explanation in Basic.v *)
(* Notation "a .x" := (a.1) : vec_scope. *)
(* Notation "a .y" := (a.2) : vec_scope. *)
(* Notation "a .z" := (a.3) : vec_scope. *)

(* ======================================================================= *)
(** ** Equality of vector *)

(** a = b <-> forall i, a.[i] = b.[i] *)
Lemma veq_iff_vnth : forall {tA} {n} (a b : @vec tA n),
    a = b <-> forall (i : 'I_n), a.[i] = b.[i].
Proof.
  intros. split; intros; subst; auto.
  (* extensionality 是一个原则，通常用于描述对象的等同性。
  具体来说，对于集合或函数而言，如果它们的元素或输出是相同的，则可以认为它们是相同的。 *)
  extensionality i; auto.
Qed.

(* Full type information of `veq_iff_vnth` *)
(*
Check @veq_iff_vnth:
  forall (A : Type) (n : nat) (a b : vec n),
    a = b <-> (forall i : fin n, (a : vec n) (i : fin n) = (b : vec n) (i : fin n)).
*)


(** a[(i,H1)] = b[(i,H2)] -> a[(i,H3)] = b[(i,H4)] *)
Lemma vnth_sameIdx_imply : forall {tA n} {a b : @vec tA n} {i} {H1 H2 H3 H4 : i < n},
    a (nat2fin i H1) = b (nat2fin i H2) ->
    a (nat2fin i H3) = b (nat2fin i H4).
Proof.
  intros.
  replace (nat2fin i H3) with (nat2fin i H1);
  replace (nat2fin i H4) with (nat2fin i H2); auto; fin.
  (* intros.
  replace (nat2fin i H3 : 'I_n) with (nat2fin i H1 : 'I_n).
  replace (nat2fin i H4 : 'I_n) with (nat2fin i H2 : 'I_n); auto.
  apply fin_eq_iff; auto. apply fin_eq_iff; auto. *)
Qed.

(** {u = v} + {u <> v} *)
#[export] Instance veq_dec : forall {tA n} {AeqDec : Dec (@eq tA)},
    Dec (@eq (@vec tA n)).
Proof.
  intros. constructor. induction n; intros.
  - left. extensionality i. fin.
  - destruct (IHn (fun i => a #i) (fun i => b #i)) as [H|H].
    + destruct (Aeqdec (a#n) (b#n)) as [H1|H1].
      * left. extensionality i. destruct (i ??< n) as [E|E].
        ** pose proof (equal_f H). specialize (H0 (fPredRange i E)).
           simpl in H0. rewrite nat2finS_fin2nat in H0. auto.
        ** pose proof (fin2nat_lt i). assert (fin2nat i = n) by lia.
           assert (i = #n).
           { eapply fin2nat_imply_nat2fin in H2. rewrite <- H2.
             erewrite nat2finS_eq. auto. }
           subst. auto.
      * right. intro. destruct H1. subst. auto.
    + right. intro. subst. easy.
      Unshelve. auto.
Qed.

(** The equality of 0-D vector *)
Lemma v0eq : forall {tA} (a b : @vec tA 0), a = b.
Proof.
  intros. apply veq_iff_vnth. intro. fin.
Qed.
(* Proof. intros. apply veq_iff_vnth. intros. exfalso. apply fin0_False; auto. Qed. *)

Lemma v0neq : forall {tA} (a b : @vec tA 0), a <> b -> False.
Proof. intros. destruct H. apply v0eq. Qed.

(** The equality of 1-D vector *)
Lemma v1eq_iff : forall {tA} (a b : @vec tA 1), a = b <-> a.1 = b.1.
Proof.
  intros. split; intros; subst; auto.
  apply veq_iff_vnth. intros. destruct i. 
  destruct i. apply (vnth_sameIdx_imply H). lia.
  (* intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H)|].
  lia. *)
Qed.

Lemma v1neq_iff : forall {tA} (a b : @vec tA 1), a <> b <-> a.1 <> b.1.
Proof.
  intros. rewrite v1eq_iff. tauto.
Qed.
(* Proof. intros. rewrite v1eq_iff. tauto. Qed. *)

(** The equality of 2-D vector *)
Lemma v2eq_iff : forall {tA} (a b : @vec tA 2), a = b <-> a.1 = b.1 /\ a.2 = b.2.
Proof.
  intros. split; intros.
  - split; subst; auto.
  - destruct H. apply veq_iff_vnth. intros.
    destruct i.
    destruct i. apply (vnth_sameIdx_imply H).
    destruct i. apply (vnth_sameIdx_imply H0).
    lia.
  (* intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 H2]. repeat destruct nat_ltb_reflect; try lia.
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  lia. *)
Qed.

Lemma v2neq_iff : forall {tA} (a b : @vec tA 2), a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2).
Proof. intros. rewrite v2eq_iff. tauto. Qed.

(** The equality of 3-D vector *)
Lemma v3eq_iff : forall {tA} (a b : @vec tA 3),
    a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 H3]]. (* repeat destruct nat_ltb_reflect; try lia. *)
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  lia.
Qed.

Lemma v3neq_iff : forall {tA} (a b : @vec tA 3),
    a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3).
Proof. intros. rewrite v3eq_iff. tauto. Qed.

(** The equality of 4-D vector *)
Lemma v4eq_iff : forall {tA} (a b : @vec tA 4),
    a = b <-> a.1 = b.1 /\ a.2 = b.2 /\ a.3 = b.3 /\ a.4 = b.4.
Proof.
  intros. split; intros; subst; auto. unfold nat2finS in H; simpl in H.
  destruct H as [H1 [H2 [H3 H4]]]. (* repeat destruct nat_ltb_reflect; try lia. *)
  apply veq_iff_vnth; intros. destruct i as [n Hn].
  destruct n; [apply (vnth_sameIdx_imply H1)|].
  destruct n; [apply (vnth_sameIdx_imply H2)|].
  destruct n; [apply (vnth_sameIdx_imply H3)|].
  destruct n; [apply (vnth_sameIdx_imply H4)|].
  lia.
Qed.

Lemma v4neq_iff : forall {tA} (a b : @vec tA 4),
    a <> b <-> (a.1 <> b.1 \/ a.2 <> b.2 \/ a.3 <> b.3 \/ a.4 <> b.4).
Proof. intros. rewrite v4eq_iff. tauto. Qed.

(** a <> b <-> ∃ i, a.[i] <> b.[i] *)
Lemma vneq_iff_exist_vnth_neq : forall {tA n} (a b : @vec tA n),
    a <> b <-> exists i, a.[i] <> b.[i].
Proof.
  intros. rewrite veq_iff_vnth. split; intros.
  - apply not_all_ex_not. auto. 
  - apply ex_not_not_all. auto.
  (* intros. rewrite veq_iff_vnth. split; intros.
  - apply not_all_ex_not; auto.
  - apply ex_not_not_all; auto. *)
Qed.
(* not_all_ex_not : 
      forall (U : Type) (P : U -> Prop),
      ~ (forall n : U, P n) -> exists n : U, ~ P n.

   ex_not_not_all :
      forall (U : Type) (P : U -> Prop),
      (exists n : U, ~ P n) -> ~ (forall n : U, P n).
 *)
 
(* ======================================================================= *)
(** ** Cast between two [vec] type that are actually of equal dimensions *)

(** Cast from [vec n] type to [vec m] type if [n = m] *)
Definition vcast {tA} n m (a : @vec tA n) (H : n = m) : @vec tA m :=
  eq_rect_r (fun n0 => vec n0 -> vec m) (fun a0 : vec m => a0) H a.


(* ######################################################################### *)
(** * Make a vector *)

(* ======================================================================= *)
(** ** Vector with same elements *)
Section vrepeat.
  Context {tA} {Azero : tA} {n : nat}.
  
  Definition vrepeat (a : tA) : @vec tA n := fun _ => a.
  (* Definition vrepeat' (a : tA) : @vec tA n := fun (i : 'I_n) => a. *)

  (** (repeat a).i = a *)
  Lemma vnth_vrepeat : forall a i, (vrepeat a).[i] = a.
  Proof. intros. unfold vrepeat; auto. Qed.

End vrepeat.

(* ======================================================================= *)
(** ** Zero vector *)
Section vzero.
  Context {tA} (Azero : tA) {n : nat}.
  
  Definition vzero : @vec tA n := vrepeat Azero.

  (** vzero.i = 0 *)
  Lemma vnth_vzero : forall i, vzero.[i] = Azero.
  Proof. intros. apply vnth_vrepeat. Qed.

End vzero.

(* ======================================================================= *)
(** ** Convert between function and vector *)
Section f2v_v2f.
  Context {tA} (Azero : tA).

  Definition f2v {n} (f : nat -> tA) : @vec tA n := fun (i : 'I_n) => f i.

  (** (f2v a).i = a i *)
  Lemma vnth_f2v : forall {n} (f : nat -> tA) (i : 'I_n), (@f2v n f).[i] = f i.
  Proof. auto. Qed.

  Lemma f2v_inj : forall {n} (f g : nat -> tA),
      @f2v n f = @f2v n g -> (forall i, i < n -> f i = g i).
  Proof. intros. unfold f2v in *. apply (equal_f H (nat2fin i H0)). Qed.

  Definition v2f {n} (a : @vec tA n) : (nat -> tA) :=
    fun i => match i ??< n with
           | left E => a (nat2fin i E)
           | _ => Azero
           end.
  
  (* Definition v2f' {n} (a : @vec tA n) : (nat -> tA) :=
    fun i => match (lt_ge_dec i n) with
            | left E => a (nat2fin i E)
            | _ => Azero
            end. *)
  
  (** (v2f a) i = a.[nat2fin i] *)
  Lemma nth_v2f : forall {n} (a : @vec tA n) (i : nat) (H : i < n),
      (v2f a) i = a.[nat2fin i H].
  Proof. intros. unfold v2f. fin. Qed.
  
  (** (v2f a) i = a[#i] *)
  Lemma nth_v2f_nat2finS : forall {n} (a : @vec tA (S n)) i,
      i < S n -> (v2f a) i = a.[#i].
  Proof.
    intros. rewrite nth_v2f with (H:=H).
    rewrite nat2finS_eq with (E:=H). auto.
  Qed.
  
  Lemma v2f_inj : forall {n} (a b : @vec tA n),
      (forall i, i < n -> (v2f a) i = (v2f b) i) -> a = b.
  Proof.
    intros. apply veq_iff_vnth; intros.
    specialize (H i (fin2nat_lt _)).
    unfold v2f in *. fin. destruct E. fin.
  Qed.

  (** f2v (v2f a) = a *)
  Lemma f2v_v2f : forall {n} (a : vec n), (@f2v n (v2f a)) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_f2v.
    rewrite nth_v2f with (H:=fin2nat_lt _). fin.
  Qed.

  (** v2f (f2v a) = a *)
  Lemma v2f_f2v : forall {n} (a : nat -> tA) i, i < n -> v2f (@f2v n a) i = a i.
  Proof. intros. rewrite nth_v2f with (H:=H). rewrite vnth_f2v. auto. Qed.

End f2v_v2f.

(* ======================================================================= *)
(** ** Convert between list and vector *)
Section l2v_v2l.
  Context {tA} (Azero : tA).

  Definition l2v {n : nat} (l : list tA) : vec n := fun (i : 'I_n) => nth i l Azero.
  (* Definition l2v' {n} (l : list tA) : vec n := fun (i : 'I_n) => nth i l Azero. *)

  (** (l2v l).i = nth i l *)
  Lemma vnth_l2v : forall {n} (l : list tA) (i : 'I_n), (@l2v n l).[i] = nth i l Azero. 
  Proof. 
    unfold l2v. auto.
  Qed.
  (* Proof. auto. Qed. *)

  (** l2v l1 = l2v l2 -> l1 = l2 *)
  Lemma l2v_inj : forall {n} (l1 l2 : list tA),
      length l1 = n -> length l2 = n -> @l2v n l1 = @l2v n l2 -> l1 = l2.
  Proof.
    intros. unfold l2v in *.
    apply list_eq_ext with (Azero:=Azero)(n:=n); auto; intros.
    pose proof (equal_f H1). specialize (H3 (nat2fin i H2)); simpl in H3. auto.
  Qed.

  Definition v2l {n} (a : vec n) : list tA := map a (finseq n).
  (* Definition v2l' {n} (a : vec n) : list tA := map a (finseq n). *)

  (** nth i (v2l a) = a.i *)
  Lemma nth_v2l : forall {n} (a : vec n) (i : nat) (E : i < n),
      nth i (v2l a) Azero = a (nat2fin i E).
  Proof.
    intros. unfold v2l. rewrite nth_map_finseq with (E:=E). auto.
  Qed.
  (* Proof. intros. unfold v2l. rewrite nth_map_finseq with (E:=E). auto. Qed. *)
  
  (** length (v2l a) = n *)
  Lemma v2l_length : forall {n} (a : vec n), length (v2l a) = n.
  Proof. intros. unfold v2l. rewrite map_length, finseq_length. auto. Qed.

  (** v2l a = v2l b -> a = b *)
  Lemma v2l_inj : forall {n} (a b : vec n), v2l a = v2l b -> a = b.
  Proof.
    intros. unfold v2l in *. apply veq_iff_vnth; intros.
    rewrite map_ext_in_iff in H. apply (H i). apply In_finseq.
  Qed.

  (** l2v (v2l a) = a *)
  Lemma l2v_v2l : forall {n} (a : vec n), (@l2v n (v2l a)) = a.
  Proof.
    intros. apply veq_iff_vnth. intros.
    rewrite vnth_l2v. destruct i. rewrite nth_v2l with (E:=E). auto.
  Qed.
  (* Proof.
    intros. apply veq_iff_vnth; intros.
    rewrite vnth_l2v. rewrite nth_v2l with (E:=fin2nat_lt _).
    rewrite nat2fin_fin2nat. auto.
  Qed. *)

  (** v2l (l2v l) = l *)
  Lemma v2l_l2v : forall {n} (l : list tA), length l = n -> v2l (@l2v n l) = l. 
  Proof. 
    intros. apply list_eq_ext with (Azero:=Azero) (n:=n); auto; intros.
    - rewrite nth_v2l with (E:=H0). rewrite vnth_l2v. auto.
    - apply v2l_length.
  Qed.
  (* Proof.
    intros. apply list_eq_ext with (Azero:=Azero)(n:=n); intros; auto.
    - rewrite nth_v2l with (E:=H0). rewrite vnth_l2v.
      rewrite fin2nat_nat2fin. auto.
    - apply v2l_length.
  Qed. *)
  
  (** ∀ v, (∃ l, l2v l = a) *)
  Lemma l2v_surj : forall {n} (a : vec n), (exists l, @l2v n l = a).
  Proof. intros. exists (v2l a). apply l2v_v2l. Qed.

  (** ∀ l, (∃ v, v2l v = l) *)
  Lemma v2l_surj : forall {n} (l : list tA), length l = n -> (exists a : vec n, v2l a = l).
  Proof. intros. exists (l2v l). apply v2l_l2v; auto. Qed.

  (** a = b -> v2l a = v2l b *)
  Lemma v2l_eq : forall n (a b : vec n), a = b -> v2l a = v2l b.
  Proof. intros. subst. auto.  Qed.

End l2v_v2l.

(* ======================================================================= *)
(** ** Convert vector to its elements *)

Lemma veq_exist_1 : forall {tA} (a : @vec tA 1), exists a1 : tA, a = l2v a1 [a1].
Proof. intros. exists (a.1). apply v2l_inj; cbv; list_eq. Qed.

Lemma veq_exist_2 : forall {tA} (a : @vec tA 2), exists a1 a2 : tA, a = l2v a1 [a1;a2].
Proof. intros. exists (a.1),(a.2). apply v2l_inj; cbv; list_eq. Qed.

Lemma veq_exist_3 : forall {tA} (a : @vec tA 3), exists a1 a2 a3 : tA, a = l2v a1 [a1;a2;a3].
Proof. intros. exists (a.1),(a.2),(a.3). apply v2l_inj; cbv; list_eq. Qed.

Lemma veq_exist_4 : forall {tA} (a : @vec tA 4),
  exists a1 a2 a3 a4 : tA, a = l2v a2 [a1;a2;a3;a4].
Proof. intros. exists (a.1),(a.2),(a.3),(a.4). apply v2l_inj; cbv; list_eq. Qed.
  

(* ======================================================================= *)
(** ** Automation for vector operations *)

(** Simplify vectorAutomation for vector operations *)
Ltac auto_vec :=
  intros;
  (* solve simple goals *)
  auto with vec;
  (* auto rewrite obvious goals, and then solve again *)
  autorewrite with vec; auto with vec;
  (* auto unfold obvious definitions, and then rewrite and solve again *)
  try autounfold with vec; autorewrite with vec; auto with vec;
  (* auto unfold low-level element abstraction, and then solve again *)
  try autounfold with tA; auto with vec.

(** Proof vector equality with point-wise element equalities over list *)
Ltac veq :=
  (* convert vector equality to list equality *)
  apply v2l_inj; cbv;
  (* convert list equality to point-wise element equalities *)
  list_eq.

Section test.
  (* [1;2;3] *)
  Let v : vec 3 := fun (i : 'I_3) => S i.
  (* Compute (v2l v). *)
  (* Compute (l2v 3 [1;2;3]). *)
  
  Goal @l2v _ 0 3 [1;2;3] = v.
  Proof.
    (* method 1: calculated all elements *)
    (* veq. *)
    (* method 2: one element every time *)
    apply veq_iff_vnth; intros.
    repeat (destruct i; simpl; auto; try lia).
  Qed.
End test.

(** destruct a vector to its elements *)
Ltac v2e a :=
  let a1 := fresh "a1" in
  let a2 := fresh "a2" in
  let a3 := fresh "a3" in
  let a4 := fresh "a4" in
  let Ha := fresh "Ha" in
  match type of a with
  | vec 1 =>
      destruct (veq_exist_1 a) as (a1,Ha); try rewrite Ha in *;
      try clear a Ha
  | vec 2 =>
      destruct (veq_exist_2 a) as (a1,(a2,Ha)); try rewrite Ha in *;
      try clear a Ha
  | vec 3 =>
      destruct (veq_exist_3 a) as (a1,(a2,(a3,Ha))); try rewrite Ha in *;
      try clear a Ha
  | vec 4 =>
      destruct (veq_exist_4 a) as (a1,(a2,(a3,(a4,Ha)))); try rewrite Ha in *;
      try clear a Ha
  end.

(** destruct a vector to its elements, and recursively destruct the result items *)
Ltac v2eALL a :=
  let a1 := fresh "a1" in
  let a2 := fresh "a2" in
  let a3 := fresh "a3" in
  let a4 := fresh "a4" in
  let Ha := fresh "Ha" in
  match type of a with
  | vec 1 =>
      destruct (veq_exist_1 a) as (a1,Ha); try rewrite Ha in *;
      try clear a Ha; try (v2e a1)
  | vec 2 =>
      destruct (veq_exist_2 a) as (a1,(a2,Ha)); try rewrite Ha in *;
      try clear a Ha; try (v2e a1; v2e a2)
  | vec 3 =>
      destruct (veq_exist_3 a) as (a1,(a2,(a3,Ha))); try rewrite Ha in *;
      try clear a Ha; try (v2e a1; v2e a2; v2e a3)
  | vec 4 =>
      destruct (veq_exist_4 a) as (a1,(a2,(a3,(a4,Ha)))); try rewrite Ha in *;
      try clear a Ha; try (v2e a1; v2e a2; v2e a3; v2e a4)
  end.

Section test.
  Goal forall tA (v : @vec tA 3), v = v.
  Proof. intros. v2e v. auto. Qed.
  
  Goal forall tA (v : @vec (@vec tA 2) 3), v = v.
  Proof. intros. v2eALL v. auto. Qed.
End test.


(* ======================================================================= *)
(** ** vector with specific size *)
Section vec_specific.
  Context {tA} {Azero : tA}.
  Variable a1 a2 a3 a4 : tA.
  
  Definition mkvec0 : @vec tA 0 := fun _ => Azero. (* anything is ok *)
  Definition mkvec1 : @vec tA 1 := l2v Azero [a1].
  Definition mkvec2 : @vec tA 2 := l2v Azero [a1;a2].
  Definition mkvec3 : @vec tA 3 := l2v Azero [a1;a2;a3].
  Definition mkvec4 : @vec tA 4 := l2v Azero [a1;a2;a3;a4].
End vec_specific.

(* ======================================================================= *)
(** ** Vector by mapping one vector *)
  
Definition vmap {tA tB n} (f: tA -> tB) (a : @vec tA n) : @vec tB n := fun i => f (a i).

Section props.
  Context (tA tB : Type) (f : tA -> tB).

  (** (vmap f a).i = f (a.i) *)
  Lemma vnth_vmap : forall n (a : vec n) i, (vmap f a).[i] = f (a.[i]).
  Proof. intros. unfold vmap; auto. Qed.
End props.

#[export] Hint Rewrite vnth_vmap : vec.


(* ======================================================================= *)
(** ** Vector by mapping two vectors *)

Definition vmap2 {tA tB tC n} (f : tA -> tB -> tC) (a : @vec tA n) (b : @vec tB n)
  : @vec tC n := fun i => f a.[i] b.[i].

Section props.
  Context (tA tB tC : Type) (f : tA -> tB -> tC).

  (** (vmap2 f a b).i = f (a.i) (b.i) *)
  Lemma vnth_vmap2 : forall n (a b : vec n) i, (vmap2 f a b).[i] = f a.[i] b.[i].
  Proof. intros. unfold vmap2; auto. Qed.

  (* vmap2 f a b = vmap id (fun i => f u.i v.i) *)
  Lemma vmap2_eq_vmap : forall {n} (a b : vec n),
      vmap2 f a b = vmap (fun a => a) (fun i => f a.[i] b.[i]).
  Proof. intros. auto. Qed.
End props.

#[export] Hint Rewrite vnth_vmap2 : vec.


(** vmap2 on same type *)
Section vmap2_sametype.
  Context `{ASGroup}.

  (** vmap2 f a b = vmap2 f b a *)
  Lemma vmap2_comm : forall {n} (a b : vec n),
      vmap2 Aadd a b = vmap2 Aadd b a.
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. agroup. Qed.
  
  (** vmap2 f (vmap2 f a b) c = vmap2 f a (vmap2 f b c) *)
  Lemma vmap2_assoc : forall {n} (a b c : vec n),
      vmap2 Aadd (vmap2 Aadd a b) c = vmap2 Aadd a (vmap2 Aadd b c).
  Proof. intros. apply veq_iff_vnth; intros. unfold vmap2. agroup. Qed.
End vmap2_sametype.

(* ======================================================================= *)
(** ** Vector with only one element is 1 *)
Section veye.
  Context {tA} (Azero Aone : tA).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veye {n} (i : 'I_n) : @vec tA n :=
    fun j => if i ??= j then 1 else 0.
  
  (** (veye i).i = 1 *)
  Lemma vnth_veye_eq : forall {n} i, (@veye n i).[i] = 1.
  Proof. intros. unfold veye. fin. Qed.

  (** (veye i).j = 0 *)
  Lemma vnth_veye_neq : forall {n} i j, i <> j -> (@veye n i).[j] = 0.
  Proof. intros. unfold veye. fin. Qed.
  
  (** veye <> 0 *)
  Lemma veye_neq0 : forall {n} i, @veye n i <> vzero.
  Proof.
    intros. intro. rewrite veq_iff_vnth in H. specialize (H i).
    rewrite vnth_veye_eq, vnth_vzero in H. easy.
  Qed.
  
End veye.

(* ======================================================================= *)
(** ** natural basis, 自然基（最常见的一种标准正交基) *)
Section veyes.
  Context {tA} (Azero Aone : tA).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation vzero := (vzero 0).
  Context {one_neq_zero : 1 <> 0}.

  Definition veyes (n : nat) : @vec (@vec tA n) n := fun i => veye Azero Aone i.

  (** veyes.ii = 1 *)
  Lemma vnth_veyes_eq : forall {n} i, (veyes n).[i].[i] = 1.
  Proof. intros. unfold veyes. apply vnth_veye_eq. Qed.

  (** veyes.ij = 0 *)
  Lemma vnth_veyes_neq : forall {n} i j, i <> j -> (veyes n).[i].[j] = 0.
  Proof. intros. unfold veyes. apply vnth_veye_neq; auto. Qed.
  
End veyes.


(* ######################################################################### *)
(** * Get head, tail, slice of a vector *)

(* ======================================================================= *)
(** ** Get head or tail element *)

(** Get head element *)
Definition vhead {tA n} (a : @vec tA (S n)) : tA := a.[fin0].

(** Get tail element *)
Definition vtail {tA n} (a : @vec tA (S n)) : tA := a.[#n].

Section props.
  Context tA {Azero : tA}.

  (** vhead a is = a.0 *)
  Lemma vhead_spec : forall {n} (a : @vec tA (S n)), vhead a = (v2f Azero a) 0.
  Proof.
    intros. unfold vhead. erewrite nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. lia.
  Qed.

  (** vhead a = a $ 0 *)
  Lemma vhead_eq : forall {n} (a : @vec tA (S n)), vhead a = a.[fin0].
  Proof. auto. Qed.

  (** vtail a = a.(n - 1) *)
  Lemma vtail_spec : forall {n} (a : @vec tA (S n)), vtail a = (v2f Azero a) n.
  Proof.
    intros. unfold vtail. erewrite nth_v2f. erewrite nat2finS_eq. f_equal.
    Unshelve. lia.
  Qed.

  (** vtail a = a $ (n - 1) *)
  Lemma vtail_eq : forall {n} (a : @vec tA (S n)), vtail a = a.[#n].
  Proof. auto. Qed.
End props.

#[export] Hint Rewrite vhead_eq : vec.
#[export] Hint Rewrite vtail_eq : vec.


(* ======================================================================= *)
(** ** Get head or tail elements *)
Section vheadN_vtailN.
  Context {tA} {Azero : tA}.

  (** Get head elements *)
  Definition vheadN {m n} (a : @vec tA (m + n)) : @vec tA m :=
    fun i => a.[fAddRangeR i].

  (** i < m -> (vheadN a).i = (v2f a).i *)
  Lemma vheadN_spec : forall {m n} (a : @vec tA (m + n)) i,
      i < m -> v2f Azero (vheadN a) i = (v2f Azero a) i.
  Proof.
    intros. unfold vheadN. erewrite !nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. all: try lia.
  Qed.

  (** (vheadN a).i = a.i *)
  Lemma vnth_vheadN : forall {m n} (a : @vec tA (m + n)) i,
      (vheadN a).[i] = a.[fAddRangeR i].
  Proof. auto. Qed.

  (** Get tail elements *)
  Definition vtailN {m n} (a : @vec tA (m + n)) : @vec tA n :=
    fun i => a.[fAddRangeAddL i].

  (** i < n -> (vtailN a).i = (v2f a).(m + i) *)
  Lemma vtailN_spec : forall {m n} (a : @vec tA (m + n)) i,
      i < n -> v2f Azero (vtailN a) i = (v2f Azero a) (m + i).
  Proof.
    intros. unfold vtailN. erewrite !nth_v2f. f_equal.
    apply fin_eq_iff; auto. Unshelve. all: try lia.
  Qed.

  (** (vtailN a).i = a.(n + i) *)
  Lemma vnth_vtailN : forall {m n} (a : @vec tA (m + n)) i,
      (vtailN a).[i] = a.[fAddRangeAddL i].
  Proof. auto. Qed.
End vheadN_vtailN.

(* ======================================================================= *)
(** ** Get slice of a vector *)
Section vslice.
  Context {tA} {Azero : tA}.

  (** {i<n}, {j<n}, {k:=S j-i} -> {i+k < n} *)
  Definition vslice_idx {n} (i j : 'I_n) (k : 'I_(S j - i)) : 'I_n.
    refine (nat2fin (i + k) _).
    pose proof (fin2nat_lt k). pose proof (fin2nat_lt j).
    apply nat_lt_sub_imply_lt_add in H. rewrite commutative.
    apply nat_ltS_lt_lt with (m := j); auto.
  Defined.
  
  (** Get a slice from vector `v` which contain elements from v$i to v$j.
      1. Include the i-th and j-th element
      2. If i > i, then the result is `vec 0` *)
  Definition vslice {n} (a : @vec tA n) (i j : 'I_n) : @vec tA (S j - i) :=
    fun k => a.[vslice_idx i j k].

  Lemma vnth_vslice : forall {n} (a : @vec tA n) (i j : 'I_n) k,
      (vslice a i j).[k] = a.[vslice_idx i j k].
  Proof. intros. auto. Qed.
End vslice.

Section test.
  Let n := 5.
  Let a : vec n := l2v 9 [1;2;3;4;5].
  (* Compute v2l (vslice a (nat2finS 1) (nat2finS 3)). *)
End test.


(* ######################################################################### *)
(** * Update a vector *)

(* ======================================================================= *)
(** ** Set element of a vector *)
Section vset.
  Context {tA} {Azero : tA}.

  (** Set i-th element vector `a` with `x` *)
  Definition vset {n} (a : @vec tA n) (i : 'I_n) (x : tA) : @vec tA n :=
    fun j => if j ??= i then x else a.[j].

  (** (vset a i x).i = x *)
  Lemma vnth_vset_eq : forall {n} (a : @vec tA n) (i : 'I_n) (x : tA),
      (vset a i x).[i] = x.
  Proof. intros. unfold vset. fin. Qed.
  
  (** (vset a i x).j = a.[j] *)
  Lemma vnth_vset_neq : forall {n} (a : @vec tA n) (i j : 'I_n) (x : tA),
      i <> j -> (vset a i x).[j] = a.[j].
  Proof. intros. unfold vset. fin. Qed.
  
End vset.

(* ======================================================================= *)
(** ** Swap two elements of a vector *)
Section vswap.
  Context {tA : Type}.
  
  (* Swap the i-th and j-th element of vector `a` *)
  Definition vswap {n} (a : @vec tA n) (i j : 'I_n) : @vec tA n :=
    fun k => if k ??= i
           then a.[j]
           else (if k ??= j then a.[i] else a.[k]).

  Lemma vnth_vswap_i : forall {n} (a : @vec tA n) (i j : 'I_n),
      (vswap a i j).[i] = a.[j].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vnth_vswap_j : forall {n} (a : @vec tA n) (i j : 'I_n),
      (vswap a i j).[j] = a.[i].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vnth_vswap_other : forall {n} (a : @vec tA n) (i j k : 'I_n),
      i <> k -> j <> k -> (vswap a i j).[k] = a.[k].
  Proof. intros. unfold vswap. fin. Qed.

  Lemma vswap_vswap : forall {n} (a : @vec tA n) (i j : 'I_n),
      vswap (vswap a i j) j i = a.
  Proof. intros. apply veq_iff_vnth; intros. unfold vswap. fin. Qed.

End vswap.

(* ======================================================================= *)
(** ** Insert element to a vector *)
Section vinsert.
  Context {tA} {Azero : tA}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  Definition vinsert {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA) : @vec tA (S n).
    intros j. destruct (j ??< i) as [E|E].
    - refine (a.[fPredRange j _]).
      apply Nat.lt_le_trans with i; auto.
      apply nat_lt_n_Sm_le.
      apply fin2nat_lt.
    - destruct (j ??= i) as [E1|E1].
      + apply x.
      + refine (a.[fPredRangeP j _]).
        assert (j > i).
        apply nat_ge_neq_imply_gt; auto. apply not_lt; auto.
        apply Nat.lt_lt_0 in H; auto.
  Defined.
  
  (** Another definition, which have simpler logic, but need `Azero`. *)
  Definition vinsert' {n} (v : @vec tA n) (i : 'I_(S n)) (x : tA) : @vec tA (S n) :=
    f2v (fun j => if j ??< i
                then (v2f v) j
                else (if j ??= i
                      then x
                      else (v2f v) (pred j))).

  (* These two definitions are equivalent *)
  Lemma vinsert_eq_vinsert' : forall {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA),
      vinsert a i x = vinsert' a i x.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vinsert, vinsert',f2v,v2f,fPredRange, fPredRangeP.
    destruct i as [i Hi], j as [j Hj]; simpl. fin.
  Qed.

  (** j < i -> (v2f (vinsert a i x)) j = (v2f a) i *)
  Lemma vinsert_spec_lt : forall {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA) (j : nat),
      j < i -> v2f (vinsert a i x) j = v2f a j.
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v. fin.
  Qed.

  (** (v2f (vinsert a i x)) i = x *)
  Lemma vinsert_spec_eq : forall {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA),
      v2f (vinsert a i x) i = x.
  Proof.
    intros. rewrite vinsert_eq_vinsert'.
    pose proof (fin2nat_lt i). unfold vinsert',v2f,f2v. fin.
  Qed.
  
  (** i < j -> 0 < j -> j < S n -> (v2f (vinsert a i x)) j = (v2f a) (pred i) *)
  Lemma vinsert_spec_gt : forall {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA) (j : nat),
      i < j -> 0 < j -> j < S n -> v2f (vinsert a i x) j = v2f a (pred j).
  Proof.
    intros. rewrite vinsert_eq_vinsert'. pose proof (fin2nat_lt i).
    unfold vinsert',v2f,f2v. fin.
  Qed.
  
  (** j < i -> (vinsert a i x).[j] = a.[j] *)
  Lemma vnth_vinsert_lt :
    forall {n} (a : @vec tA n) (i j : 'I_(S n)) x (H : j < i),
      (vinsert a i x).[j] =
        a.[fPredRange j (nat_lt_ltS_lt _ _ _ H (fin2nat_lt _))].
  Proof.
    intros. pose proof (vinsert_spec_lt a i x j H).
    erewrite !nth_v2f in H0. fin. rewrite H0. f_equal. apply fin_eq_iff; auto.
    Unshelve. fin. pose proof (fin2nat_lt i). lia.
  Qed.

  (** (vinsert a i x).[i] = a *)
  Lemma vnth_vinsert_eq : forall {n} (a : @vec tA n) (i : 'I_(S n)) x,
      (vinsert a i x).[i] = x.
  Proof.
    intros. pose proof (vinsert_spec_eq a i x).
    pose proof (fin2nat_lt i). unfold v2f in *. fin. 
  Qed.

  (** 0 < j -> (vinsert a i x).[j] = a.(pred j) *)
  Lemma vnth_vinsert_gt :
    forall {n} (a : @vec tA n) (i j : 'I_(S n)) x (H : 0 < j),
      i < j -> (vinsert a i x).[j] = a.[fPredRangeP j H].
  Proof.
    intros.
    pose proof (vinsert_spec_gt a i x j H0 H (fin2nat_lt _)).
    erewrite !nth_v2f in H1. fin. rewrite H1. fin. Unshelve. fin.
    pose proof (fin2nat_lt j). fin.
  Qed.

  (** Invert 0 into vzero get vzero *)
  Lemma vinsert_vzero_eq0 : forall {n} i, @vinsert n vzero i Azero = vzero.
  Proof.
    intros. rewrite vinsert_eq_vinsert'.
    apply veq_iff_vnth; intros j. rewrite vnth_vzero.
    destruct i as [i Hi], j as [j Hj].
    unfold vinsert',f2v,v2f; simpl. fin.
  Qed.

  (** If insert x into vector a get vzero, then x is 0 *)
  Lemma vinsert_eq0_imply_x0 {AeqDec : Dec (@eq tA)} : forall {n} (a : @vec tA n) i x,
      vinsert a i x = vzero -> x = Azero.
  Proof.
    intros. rewrite veq_iff_vnth in *. specialize (H i).
    rewrite vnth_vzero in H. rewrite <- H.
    symmetry. apply vnth_vinsert_eq.
  Qed.

  (** If insert x into vector _a_ get vzero, then _a_ is vzero *)
  Lemma vinsert_eq0_imply_v0 {AeqDec : Dec (@eq tA)} : forall {n} (a : @vec tA n) i x,
      vinsert a i x = vzero -> a = vzero.
  Proof.
    intros.
    pose proof (vinsert_eq0_imply_x0 a i x H). subst.
    rewrite !veq_iff_vnth in *; intros j.
    destruct (j ??< i).
    - specialize (H (fSuccRange j)). erewrite vnth_vinsert_lt in H; fin.
    - specialize (H (fSuccRangeS j)). erewrite vnth_vinsert_gt in H; fin.
      Unshelve. fin. fin.
  Qed.

  (** Insert x into vector _a_ get vzero, iff _a_ is vzero and _x_ is 0 *)
  Lemma vinsert_eq0_iff {AeqDec : Dec (@eq tA)} : forall {n} (a : @vec tA n) i x,
      vinsert a i x = vzero <-> (a = vzero /\ x = Azero).
  Proof.
    logic.
    - apply vinsert_eq0_imply_v0 in H; auto.
    - apply vinsert_eq0_imply_x0 in H; auto.
    - subst. apply vinsert_vzero_eq0.
  Qed.

  (** Insert x into vector _a_ is not vzero, iff _a_ is not vzero or _x_ is 0 *)
  Lemma vinsert_neq0_iff {AeqDec : Dec (@eq tA)} : forall {n} (a : @vec tA n) i x,
      vinsert a i x <> vzero <-> (a <> vzero \/ x <> Azero).
  Proof. intros. rewrite vinsert_eq0_iff. tauto. Qed.

End vinsert.

Section test.
  Let n := 5.
  Let a : vec n := l2v 9 [1;2;3;4;5].
  (* Compute v2l (vinsert a #1 7). *)
  (* Compute v2l (vinsert a #5 7). *)
End test.    

(* ======================================================================= *)
(** ** Remove one element at given position *)
Section vremove.
  Context {tA} {Azero : tA}.
  Notation v2f := (v2f Azero).

  (** Removes i-th element from vector `a` *)
  Definition vremove {n} (a : @vec tA (S n)) (i : 'I_(S n)) : @vec tA n :=
    fun j => if j ??< i
           then a (fSuccRange j)
           else a (fSuccRangeS j). 

  (* Another definition, which have simpler logic, but need `Azero`. *)
  Definition vremove' {n} (a : @vec tA (S n)) (i : 'I_(S n)) : @vec tA n :=
    f2v (fun j => if j ??< i then v2f a j else v2f a (S j)).
  
  (* These two definitions are equivalent *)
  Lemma vremove_eq_vremove' : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)),
      vremove a i = vremove' a i.
  Proof.
    intros. apply veq_iff_vnth; intros j.
    unfold vremove, vremove', f2v, v2f.
    unfold fSuccRange, fSuccRangeS.
    destruct i as [i Hi], j as [j Hj]; simpl. fin.
    erewrite nat2finS_eq. apply fin_eq_iff; auto. Unshelve. auto.
  Qed.

  (** j < i -> (vremove a i).j = v.j *)
  Lemma vremove_spec_lt : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)) (j : nat),
      j < i -> v2f (vremove a i) j = v2f a j.
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold v2f,vremove',f2v.
    destruct i as [i Hi]; simpl in *. fin.
  Qed.
  
  (** i <= j -> j < n -> (vremove a i).j = v.(S j) *)
  Lemma vremove_spec_ge : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)) (j : nat),
      i <= j -> j < n -> v2f (vremove a i) j = v2f a (S j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi]; simpl in *. fin.
  Qed.

  (** j < i -> (vremove a i).j = a.j *)
  Lemma vnth_vremove_lt : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)) (j : 'I_n),
      j < i -> (vremove a i).[j] = v2f a j.
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *. fin.
  Qed.
  
  (** i <= j -> j < n -> (vremove a i).j = a.(S j) *)
  Lemma vnth_vremove_ge : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)) (j : 'I_n),
      i <= j -> j < n -> (vremove a i).[j] = v2f a (S j).
  Proof.
    intros. rewrite vremove_eq_vremove'. unfold vremove',f2v,v2f.
    destruct i as [i Hi], j as [j Hj]; simpl in *. fin.
  Qed.

  (** vremove (vinsert a i x) i = a *)
  Lemma vremove_vinsert : forall {n} (a : @vec tA n) (i : 'I_(S n)) (x : tA),
      vremove (vinsert a i x) i = a.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f; simpl in *. fin.
  Qed.
  
  (** vinsert (vremove a i) (a.[i]) = a *)
  Lemma vinsert_vremove : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)),
      vinsert (vremove a i) i (a.[i]) = a.
  Proof.
    intros. rewrite vremove_eq_vremove', (vinsert_eq_vinsert' (Azero:=Azero)).
    apply veq_iff_vnth; intros j.
    destruct i as [i Hi], j as [j Hj].
    unfold vremove',vinsert',f2v,v2f; simpl in *. fin.
  Qed.
  
End vremove.

Section vmap_vinsert_vremove.
  Context {tA tB tC : Type} {Azero : tA} {Bzero : tB} {Czero : tC}.
  Context (f1 : tA -> tB).
  Context (f2 : tA -> tB -> tC).

  (** vmap f (vremove a i) = vremove (vmap f v) i *)
  Lemma vmap_vremove : forall {n} (a : @vec tA (S n)) i,
      vmap f1 (vremove a i) = vremove (vmap f1 a) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (j ??< i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      erewrite !nth_v2f. unfold vmap. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      erewrite !nth_v2f. unfold vmap. auto.
      Unshelve. lia. lia.
  Qed.

  (** vmap2 f (vremove a i) (vremove b i) = vremove (vmap2 a b) i *)
  Lemma vmap2_vremove_vremove : forall {n} (a : @vec tA (S n)) (b : @vec tB (S n)) i,
      vmap2 f2 (vremove a i) (vremove b i) = vremove (vmap2 f2 a b) i.
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (j ??< i).
    - rewrite (vnth_vremove_lt (Azero:=Azero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); auto.
      rewrite (vnth_vremove_lt (Azero:=Czero)); auto.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
    - rewrite (vnth_vremove_ge (Azero:=Azero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Bzero)); try lia.
      rewrite (vnth_vremove_ge (Azero:=Czero)); try lia.
      erewrite !nth_v2f. rewrite vnth_vmap2. auto.
      Unshelve. lia. lia.
  Qed.

  (** vmap2 (vinsert a i x) b = vinsert (vmap2 a (vremove b i)) i (f x b.i) *)
  Lemma vmap2_vinsert_l : forall {n} (a : @vec tA n) (b : @vec tB (S n)) i (x : tA),
      vmap2 f2 (vinsert a i x) b =
        vinsert (vmap2 f2 a (vremove b i)) i (f2 x (b.[i])).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (j ??< i) as [E|E].
    - rewrite (vnth_vinsert_lt (Azero:=Azero)) with (H:=E).
      rewrite (vnth_vinsert_lt (Azero:=Czero)) with (H:=E).
      rewrite vnth_vmap2. fin.
      rewrite (vnth_vremove_lt (Azero:=Bzero)); fin.
      erewrite nth_v2f with (H:=fin2nat_lt _); fin.
    - destruct (j ??= i) as [E1|E1]; fin.
      + apply fin2nat_eq_iff in E1; rewrite E1.
        rewrite (vnth_vinsert_eq (Azero:=Azero)).
        rewrite (vnth_vinsert_eq (Azero:=Czero)). auto.
      + assert (i < j) by lia.
        assert (0 < j) by lia.
        rewrite (vnth_vinsert_gt (Azero:=Azero)) with (H:=H0); auto.
        rewrite (vnth_vinsert_gt (Azero:=Czero)) with (H:=H0); auto.
        rewrite vnth_vmap2. fin.
        rewrite (vnth_vremove_ge (Azero:=Bzero)); fin.
        * assert (S (pred j) < S n).
          rewrite Nat.succ_pred; try lia. apply fin2nat_lt.
          rewrite nth_v2f with (H:=H1). fin. destruct j. fin.
        * pose proof (fin2nat_lt j). lia.
  Qed.
  
  (** vmap2 a (vinsert b i x) = vinsert (vmap2 (vremove a i) b) i (f a.i x) *)
  Lemma vmap2_vinsert_r : forall {n} (a : @vec tA (S n)) (b : @vec tB n) i (x : tB),
      vmap2 f2 a (vinsert b i x) =
        vinsert (vmap2 f2 (vremove a i) b) i (f2 (a.[i]) x).
  Proof.
    intros. apply veq_iff_vnth; intros j. rewrite vnth_vmap2.
    destruct (j ??< i) as [E|E].
    - assert (j < n). pose proof (fin2nat_lt i). lia.
      rewrite (vnth_vinsert_lt (Azero:=Bzero)) with (H:=E).
      rewrite (vnth_vinsert_lt (Azero:=Czero)) with (H:=E).
      rewrite vnth_vmap2. f_equal.
      rewrite (vnth_vremove_lt (Azero:=Azero)); auto. simpl.
      rewrite nth_v2f with (H:=fin2nat_lt _). fin.
    - destruct (j ??= i) as [E1|E1].
      + apply fin2nat_eq_iff in E1; rewrite E1.
        rewrite (@vnth_vinsert_eq _ Bzero).
        rewrite (@vnth_vinsert_eq _ Czero). auto.
      + assert (i < j) by lia.
        assert (0 < j) by lia.
        rewrite (vnth_vinsert_gt (Azero:=Bzero)) with (H:=H0); auto.
        rewrite (vnth_vinsert_gt (Azero:=Czero)) with (H:=H0); auto.
        rewrite vnth_vmap2. f_equal.
        rewrite (vnth_vremove_ge (Azero:=Azero)); fin.
        * assert (S (pred j) < S n).
          rewrite Nat.succ_pred; try lia. apply fin2nat_lt.
          rewrite nth_v2f with (H:=H1). fin. destruct j. fin.
        * pose proof (fin2nat_lt j). lia.
  Qed.

End vmap_vinsert_vremove.

(* ======================================================================= *)
(** ** Remove element at head or tail *)
Section vremoveH_vremoveT.
  Context {tA} {Azero : tA}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vremoveH *)
  
  (** Remove head element *)
  Definition vremoveH {n} (a : @vec tA (S n)) : @vec tA n :=
    fun i => a.[fSuccRangeS i].

  (** i < n -> (vremoveH a).i = v.(S i) *)
  Lemma vremoveH_spec : forall {n} (a : @vec tA (S n)) (i : nat),
      i < n -> v2f (vremoveH a) i = v2f a (S i).
  Proof.
    intros. unfold vremoveH,v2f. fin.
  Qed.
  
  (** (vremoveH a).i = a.(S i) *)
  Lemma vnth_vremoveH : forall {n} (a : @vec tA (S n)) (i : 'I_n),
      (vremoveH a).[i] = a.[fSuccRangeS i].
  Proof. intros. unfold vremoveH. auto. Qed.

  (** v1.1 = v2.1 -> vremoveH v1 = vremoveH v2 -> v1 = v2 *)
  Lemma vremoveH_inj : forall n (v1 v2 : @vec tA (S n)),
      v1.1 = v2.1 -> vremoveH v1 = vremoveH v2 -> v1 = v2.
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H0.
    bdestruct (i =? 0).
    - replace (v1.1) with (v1 fin0) in H. replace (v2.1) with (v2 fin0) in H.
      replace (v1 i) with (v1 fin0). replace (v2 i) with (v2 fin0).
      all: fin. all: destruct i; fin.
    - assert (0 < i) by fin.
      specialize (H0 (fPredRangeP i H2)).
      rewrite !vnth_vremoveH in H0. fin.
  Qed.
  
  (** a <> 0 -> vhead a = 0 -> vremoveH a <> 0 *)
  Lemma vremoveH_neq0_if : forall {n} (a : @vec tA (S n)),
      a <> vzero -> vhead a = Azero -> vremoveH a <> vzero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveH in H1. rewrite vhead_eq in H0.
    destruct (i ??= 0) as [E|E].
    - rewrite vnth_vzero. destruct i; simpl in *; subst.
      f_equal. apply fin_eq_iff; auto.
    - assert (0 < i). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fPredRangeP i H)).
      rewrite fSuccRangeS_fPredRangeP in H1. rewrite H1. cbv. auto.
  Qed.

  (** vremoveH also hold, if hold for all elements *)
  Lemma vremoveH_hold : forall {n} (a : @vec tA (S n)) (P : tA -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveH a).[i])).
  Proof. intros. unfold vremoveH. auto. Qed.

  
  (** *** vremoveT *)

  (** Remove tail element *)
  Definition vremoveT {n} (a : @vec tA (S n)) : @vec tA n :=
    fun i => a.[fSuccRange i].

  (** i < n -> (vremoveT a).i = a.i *)
  Lemma vremoveT_spec : forall {n} (a : @vec tA (S n)) (i : nat),
      i < n -> v2f (vremoveT a) i = v2f a i.
  Proof.
    intros. unfold vremoveT,v2f. fin.
    erewrite fSuccRange_nat2fin. apply fin_eq_iff; auto.
    Unshelve. auto.
  Qed.
  
  (** (vremoveT a).i = a.i *)
  Lemma vnth_vremoveT : forall {n} (a : @vec tA (S n)) (i : 'I_n),
      (vremoveT a).[i] = a.[fSuccRange i].
  Proof. intros. unfold vremoveT. auto. Qed.

  (** vremoveT v1 = vremoveT v2 -> v1 #n = v2 #n -> v1 = v2 *)
  Lemma vremoveT_inj : forall n (v1 v2 : @vec tA (S n)),
      vremoveT v1 = vremoveT v2 -> v1 #n = v2 #n -> v1 = v2.
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H.
    bdestruct (i =? n).
    - replace (v1 i) with (v1 #n). replace (v2 i) with (v2 #n). all: fin.
    - assert (i < n) by fin.
      specialize (H (fPredRange i H2)). rewrite !vnth_vremoveT in H. fin.
  Qed.
  
  (** v <> 0 -> vtail v = 0 -> vremoveT v <> 0 *)
  Lemma vremoveT_neq0_if : forall {n} (a : @vec tA (S n)),
      a <> vzero -> vtail a = Azero -> vremoveT a <> vzero.
  Proof.
    intros. intro. destruct H. apply veq_iff_vnth; intros.
    rewrite veq_iff_vnth in H1. unfold vremoveT in H1.
    rewrite vtail_eq in H0.
    destruct (i ??= n) as [E|E].
    - destruct i; simpl in *; subst. rewrite vnth_vzero. f_equal.
      erewrite nat2finS_eq. apply fin_eq_iff; auto.
    - assert (i < n). pose proof (fin2nat_lt i). lia.
      specialize (H1 (fPredRange i H)).
      rewrite fSuccRange_fPredRange in H1. rewrite H1. cbv. auto.
      Unshelve. auto.
  Qed.

  (** vremoveT also hold, if hold for all elements *)
  Lemma vremoveT_hold : forall {n} (a : @vec tA (S n)) (P : tA -> Prop),
      (forall i, P (a.[i])) -> (forall i, P ((vremoveT a).[i])).
  Proof. intros. unfold vremoveT. auto. Qed.

End vremoveH_vremoveT.

(* ======================================================================= *)
(** ** Remove elements at head or tail *)
Section vremoveHN_vremoveTN.
  Context {tA} {Azero : tA}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vremoveHN *)
  
  (** Remove head elements *)
  Definition vremoveHN {m n} (a : @vec tA (m + n)) : @vec tA n :=
    fun i => a.[fAddRangeAddL i].

  (** i < n -> (vremoveHN a).i = a.(m + i) *)
  Lemma vremoveHN_spec : forall {m n} (a : @vec tA (m + n)) (i : nat),
      i < n -> v2f (vremoveHN a) i = v2f a (m + i).
  Proof.
    intros. unfold vremoveHN. erewrite !nth_v2f. f_equal.
    apply fin2nat_imply_nat2fin; simpl. auto.
    Unshelve. all: lia.
  Qed.
  
  (** (vremoveHN a).i = a.(m + i) *)
  Lemma vnth_vremoveHN : forall {m n} (a : @vec tA (m + n)) (i : 'I_n),
      (vremoveHN a).[i] = a.[fAddRangeAddL i].
  Proof. auto. Qed.
  
  (** a <> 0 -> vheadN v = 0 -> vremoveHN a <> 0 *)
  Lemma vremoveHN_neq0_if : forall {m n} (a : @vec tA (m + n)),
      a <> vzero -> vheadN a = vzero -> vremoveHN a <> vzero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vheadN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveHN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= i) as [E|E].
    - specialize (H1 (fAddRangeAddL' i E)).
      rewrite fAddRangeAddL_fAddRangeAddL' in H1. rewrite H1. cbv. auto.
    - assert (i < m). lia.
      specialize (H0 (fAddRangeR' i H)).
      rewrite fAddRangeR_fAddRangeR' in H0. rewrite H0. cbv. auto.
  Qed.
  
  
  (** *** vremoveTN *)

  (** Remove tail elements *)
  Definition vremoveTN {m n} (a : @vec tA (m + n)) : @vec tA m :=
    fun i => a.[fAddRangeR i].

  (** i < n -> (vremoveTN a).i = a.i *)
  Lemma vremoveTN_spec : forall {m n} (a : @vec tA (m + n)) (i : nat),
      i < m -> v2f (vremoveTN a) i = v2f a i.
  Proof.
    intros. unfold vremoveTN,v2f. fin.
  Qed.
  
  (** (vremoveTN a).i = a.i *)
  Lemma vnth_vremoveTN : forall {m n} (a : @vec tA (m + n)) (i : 'I_m),
      (vremoveTN a).[i] = a.[fAddRangeR i].
  Proof. intros. auto. Qed.
  
  (** a <> 0 -> vtailN v = 0 -> vremoveTN a <> 0 *)
  Lemma vremoveTN_neq0_if : forall {m n} (a : @vec tA (m + n)),
      a <> vzero -> vtailN a = vzero -> vremoveTN a <> vzero.
  Proof.
    intros. intro.
    rewrite veq_iff_vnth in H0. unfold vtailN in H0.
    rewrite veq_iff_vnth in H1. unfold vremoveTN in H1.
    destruct H. apply veq_iff_vnth; intros.
    destruct (m ??<= i) as [E|E].
    - specialize (H0 (fAddRangeAddL' i E)).
      rewrite fAddRangeAddL_fAddRangeAddL' in H0. rewrite H0. cbv. auto.
    - assert (i < m). lia.
      specialize (H1 (fAddRangeR' i H)).
      rewrite fAddRangeR_fAddRangeR' in H1. rewrite H1. cbv. auto.
  Qed.

End vremoveHN_vremoveTN.

(* ======================================================================= *)
(** ** Construct vector with a vector an an element at the head or tail *)
Section vconsH_vconsT.
  Context {tA} {Azero : tA}.
  Notation v2f := (v2f Azero).
  Notation vzero := (vzero Azero).

  (** *** vconsH *)

  (** cons at head: [x; a] *)
  Definition vconsH {n} (x : tA) (a : @vec tA n) : @vec tA (S n).
    intros i. destruct (i ??= 0). exact x.
    assert (0 < i). apply neq_0_lt_stt; auto.
    apply (a.[fPredRangeP i H]).
  Defined.

  (** i = 0 -> (v2f [x; a]) i = a *)
  Lemma vconsH_spec_0 : forall {n} x (a : @vec tA n) (i : nat),
      i = 0 -> v2f (vconsH x a) i = x.
  Proof.
    intros. subst. unfold vconsH,v2f; simpl. auto.
  Qed.

  (** 0 < i -> i < n -> [x; a].i = a.(pred i) *)
  Lemma vconsH_spec_gt0 : forall {n} x (a : @vec tA n) (i : nat),
      0 < i -> i < n -> v2f (vconsH x a) i = v2f a (pred i).
  Proof.
    intros. unfold vconsH,v2f; simpl. fin.
  Qed.

  (** i = 0 -> [x; a].i = a *)
  Lemma vnth_vconsH_0 : forall {n} x (a : @vec tA n) i,
      i = fin0 -> (vconsH x a).[i] = x.
  Proof. intros. subst. unfold vconsH. simpl. auto. Qed.
  
  (** 0 < i -> [x; a].i = a.(pred i)  *)
  Lemma vnth_vconsH_gt0 : forall {n} x (a : @vec tA n) (i : 'I_(S n)) (H: 0 < i),
      (vconsH x a).[i] = a.[fPredRangeP i H].
  Proof.
    intros. unfold vconsH. fin.
  Qed.

  (** [x; v1] = [x; a2] -> x1 = x2 /\ v1 = v2 *)
  Lemma vconsH_inj : forall n x1 x2 (v1 v2 : @vec tA n),
      vconsH x1 v1 = vconsH x2 v2 -> x1 = x2 /\ v1 = v2.
  Proof.
    intros. rewrite veq_iff_vnth in H. split.
    - specialize (H fin0). auto.
    - apply veq_iff_vnth. intros. specialize (H (fSuccRangeS i)).
      erewrite !vnth_vconsH_gt0 in H. fin.
      Unshelve. all: fin.
  Qed.

  (** [x; a] = 0 <-> x = 0 /\ v = 0 *)
  Lemma vconsH_eq0_iff : forall {n} x (a : @vec tA n),
      vconsH x a = vzero <-> x = Azero /\ a = vzero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H fin0). rewrite vnth_vconsH_0 in H; auto.
      + specialize (H (fSuccRangeS i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsH_gt0. f_equal.
        rewrite fPredRangeP_fSuccRangeS. auto.
    - destruct H. subst. destruct (i ??= 0).
      + rewrite vnth_vconsH_0; auto. destruct i; simpl in *. apply fin_eq_iff; auto.
      + erewrite vnth_vconsH_gt0; auto.
        Unshelve. rewrite fin2nat_fSuccRangeS. lia. lia.
  Qed.
  
  (** [x; a] <> 0 <-> x <> 0 \/ a <> 0 *)
  Lemma vconsH_neq0_iff : forall {n} x (a : @vec tA n),
      vconsH x a <> vzero <-> x <> Azero \/ a <> vzero.
  Proof. intros. rewrite vconsH_eq0_iff. tauto. Qed.

  (** vconsH (vhead a) (vremoveH a) = a *)
  Lemma vconsH_vhead_vremoveH : forall {n} (a : @vec tA (S n)),
      vconsH (vhead a) (vremoveH a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (i ??= 0).
    - rewrite vnth_vconsH_0. 
      + unfold vhead. f_equal. destruct i; simpl in *; auto. apply fin_eq_iff; auto.
      + destruct i; simpl in *. apply fin_eq_iff; auto.
    - erewrite vnth_vconsH_gt0. rewrite vnth_vremoveH. f_equal.
      rewrite fSuccRangeS_fPredRangeP. auto.
      Unshelve. lia.
  Qed.

  (** vremoveH (vconsH a x) = a *)
  Lemma vremoveH_vconsH : forall {n} x (a : @vec tA n), vremoveH (vconsH x a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros i. rewrite vnth_vremoveH.
    erewrite vnth_vconsH_gt0. f_equal. apply fPredRangeP_fSuccRangeS.
    Unshelve. rewrite fin2nat_fSuccRangeS. lia.
  Qed.
  
  (** vhead (vconsH a x) = x *)
  Lemma vhead_vconsH : forall {n} (a : @vec tA n) x, vhead (vconsH x a) = x.
  Proof. intros. unfold vhead. rewrite vnth_vconsH_0; auto. Qed.

  (** [0; vzero] = vzero *)
  Lemma vconsH_0_vzero : forall {n}, @vconsH n Azero vzero = vzero.
  Proof. intros. unfold vconsH. apply veq_iff_vnth; intros. fin. Qed.
  
  
  (** *** vconsT *)

  (** cons at tail: [a; x] *)
  Definition vconsT {n} (a : @vec tA n) (x : tA) : @vec tA (S n).
    intros i. destruct (i ??< n) as [E|E].
    - apply (a.[fPredRange i E]).
    - apply x.
  Defined.
  
  (** i = n -> (v2f [a; x]) i = a *)
  Lemma vconsT_spec_n : forall {n} x (a : @vec tA n) (i : nat),
      i = n -> v2f (vconsT a x) i = x.
  Proof. intros. subst. unfold vconsT,v2f; simpl. fin. Qed.

  (** i < n -> (v2f [a; x]) i = a.(pred i) *)
  Lemma vconsT_spec_lt : forall {n} x (a : @vec tA n) (i : nat),
      i < n -> v2f (vconsT a x) i = v2f a i.
  Proof. intros. unfold vconsT,v2f; simpl. fin. Qed.

  (** i = n -> [a; x].i = a *)
  Lemma vnth_vconsT_n : forall {n} x (a : @vec tA n) (i : 'I_(S n)),
      fin2nat i = n -> (vconsT a x).[i] = x.
  Proof. intros. unfold vconsT. fin. Qed.

  (** i < n -> [a; x].i = a.(pred i) *)
  Lemma vnth_vconsT_lt : forall {n} x (a : @vec tA n) (i : 'I_(S n)) (H: i < n),
      (vconsT a x).[i] = a (fPredRange i H).
  Proof. intros. unfold vconsT. fin. Qed.

  (** [v1; x] = [a2; x] -> v1 = v2 /\ x1 = x2 *)
  Lemma vconsT_inj : forall n (v1 v2 : @vec tA n) x1 x2,
      vconsT v1 x1 = vconsT v2 x2 -> v1 = v2 /\ x1 = x2.
  Proof.
    intros. rewrite veq_iff_vnth in H. split.
    - apply veq_iff_vnth. intros. specialize (H (fSuccRange i)).
      erewrite !vnth_vconsT_lt in H. fin.
    - specialize (H #n). rewrite !vnth_vconsT_n in H; auto.
      Unshelve. all: fin.
  Qed.

  (** [a; x] = 0 <-> a = 0 /\ x = 0*)
  Lemma vconsT_eq0_iff : forall {n} (a : @vec tA n) x,
      vconsT a x = vzero <-> a = vzero /\ x = Azero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros; auto.
      + specialize (H (fSuccRange i)). rewrite vnth_vzero in *. rewrite <- H.
        erewrite vnth_vconsT_lt. f_equal.
        rewrite fPredRange_fSuccRange. auto.
      + specialize (H (nat2finS n)). rewrite vnth_vconsT_n in H; auto.
        rewrite fin2nat_nat2finS; auto.
    - pose proof (fin2nat_lt i).
      destruct H. subst. destruct (i ??= n).
      + rewrite vnth_vconsT_n; auto.
      + erewrite vnth_vconsT_lt; auto.
        Unshelve. all: try lia. rewrite fin2nat_fSuccRange. apply fin2nat_lt.
  Qed.
  
  (** [a; x] <> 0 <-> a <> 0 \/ x <> 0*)
  Lemma vconsT_neq0_iff : forall {n} (a : @vec tA n) x,
      vconsT a x <> vzero <-> a <> vzero \/ x <> Azero.
  Proof.
    intros. rewrite vconsT_eq0_iff. split; intros.
    apply not_and_or in H; auto. apply or_not_and; auto.
  Qed.

  (** vconsT (vremoveT a) (vtail a) = a *)
  Lemma vconsT_vremoveT_vtail : forall {n} (a : @vec tA (S n)),
      vconsT (vremoveT a) (vtail a) = a.
  Proof.
    intros. apply veq_iff_vnth; intros. destruct (i ??= n).
    - destruct i as [i Hi]. simpl in *. subst. rewrite vnth_vconsT_n; auto.
      rewrite vtail_eq. f_equal. erewrite nat2finS_eq. apply fin_eq_iff; auto.
    - erewrite vnth_vconsT_lt. rewrite vnth_vremoveT. f_equal.
      rewrite fSuccRange_fPredRange. auto.
      Unshelve. all: try lia. pose proof (fin2nat_lt i). lia.
  Qed.

  (** vremoveT (vconsT a x) = a *)
  Lemma vremoveT_vconsT : forall {n} (a : @vec tA n) x, vremoveT (vconsT a x) = a.
  Proof.
    intros. apply veq_iff_vnth; intros i. rewrite vnth_vremoveT.
    erewrite vnth_vconsT_lt. f_equal. apply fPredRange_fSuccRange.
    Unshelve. rewrite fin2nat_fSuccRange. apply fin2nat_lt.
  Qed.
  
  (** vtail (vconsT a x) = x *)
  Lemma vtail_vconsT : forall {n} (a : @vec tA n) x, vtail (vconsT a x) = x.
  Proof.
    intros. unfold vtail. rewrite vnth_vconsT_n; auto.
    rewrite fin2nat_nat2finS; auto.
  Qed.

  (** [vzero; 0] = vzero *)
  Lemma vconsT_vzero_eq0 : forall {n}, @vconsT n vzero Azero = vzero.
  Proof.
    intros. unfold vconsT. apply veq_iff_vnth; intros. fin.
  Qed.

  (** vmap2 f (vconsT a x) (vconsT b y) = vconsT (vmap2 f a b) (f x y) *)
  Lemma vmap2_vconsT_vconsT : forall {n} (a b : @vec tA n) (x y : tA) (f : tA -> tA -> tA),
      vmap2 f (vconsT a x) (vconsT b y) = vconsT (vmap2 f a b) (f x y).
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_vmap2.
    unfold vconsT. fin.
  Qed.
  
End vconsH_vconsT.

(* ======================================================================= *)
(** ** Construct vector by append two vectors *)
Section vapp.
  Context {tA} {Azero : tA}.
  Notation vec := (@vec tA).
  Notation vzero := (vzero Azero).

  (** Append two vectors, denoted with a ++ b *)
  Definition vapp {n m} (a : vec n) (b : vec m) : vec (n + m).
    intros i. destruct (i ??< n) as [E|E].
    - exact (a.[fAddRangeR' i E]).
    - assert (n <= i). apply Nat.nlt_ge; auto.
      exact (b.[fAddRangeAddL' i H]).
  Defined.
  Infix "++" := vapp : vec_scope.
  
  (** i < n -> (a ++ b).i = u.i *)
  Lemma vapp_spec_l : forall {n m} (a : vec n) (b : vec m) (i : nat),
      i < n -> v2f Azero (a ++ b) i = v2f Azero a i.
  Proof.
    intros. unfold vapp.
    assert (i < n + m). lia.
    rewrite nth_v2f with (H:=H0). rewrite nth_v2f with (H:=H). fin.
  Qed.
  
  (** n <= i -> i < n + m -> (a ++ b).[i] = a.(i - n) *)
  Lemma vapp_spec_r : forall {n m} (a : vec n) (b : vec m) (i : nat),
      n <= i -> i < n + m -> v2f Azero (a ++ b) i = v2f Azero b (i - n).
  Proof.
    intros. unfold vapp.
    rewrite nth_v2f with (H:=H0). simpl. fin.
    assert (i - n < m). lia. rewrite nth_v2f with (H:=H1). f_equal.
    apply fin_eq_iff; auto.
  Qed.
  
  (** i < n -> (a ++ b).[i] = a.[i] *)
  Lemma vnth_vapp_l : forall {n m} (a : vec n) (b : vec m) (i : 'I_(n + m)) (H : i < n),
      (a ++ b).[i] = a.[fAddRangeR' i H].
  Proof. intros. destruct i as [i Hi]. unfold vapp. simpl. fin. Qed.
  
  (** n <= i -> (a ++ b).[i] = b.[i] *)
  Lemma vnth_vapp_r : forall {n m} (a : vec n) (b : vec m) (i : 'I_(n + m)) (H : n <= i),
      (a ++ b).[i] = b.[fAddRangeAddL' i H].
  Proof. intros. destruct i as [i Hi]. unfold vapp. simpl in *. fin. Qed.

  (** (a ++ b) = 0 <-> a = 0 /\ b = 0 *)
  Lemma vapp_eq0_iff : forall {n m} (a : vec n) (b : vec m),
      a ++ b = vzero <-> a = vzero /\ b = vzero.
  Proof.
    intros. rewrite !veq_iff_vnth. split; intros.
    - split; intros.
      + specialize (H (fAddRangeR i)).
        erewrite vnth_vapp_l in H. rewrite fAddRangeR'_fAddRangeR in H.
        rewrite H. cbv. auto.
      + specialize (H (fAddRangeAddL i)).
        erewrite vnth_vapp_r in H. erewrite fAddRangeAddL'_fAddRangeAddL in H.
        rewrite H. cbv. auto.
    - destruct H. destruct (i ??< n) as [E|E].
      + rewrite vnth_vapp_l with (H:=E). rewrite H. cbv. auto.
      + erewrite vnth_vapp_r. rewrite H0. cbv. auto.
        Unshelve. all: try lia.
        * rewrite fin2nat_fAddRangeR. apply fin2nat_lt.
        * rewrite fin2nat_fAddRangeAddL. lia.
  Qed.
  
  (** vapp (vheadN a) (vtailN a) = a *)
  Lemma vapp_vheadN_vtailN : forall {n m} (a : vec (n + m)), vheadN a ++ vtailN a = a.
  Proof.
    intros. apply veq_iff_vnth; intros.
    destruct (i ??< n) as [E|E].
    - erewrite vnth_vapp_l. rewrite vnth_vheadN.
      rewrite fAddRangeR_fAddRangeR'. auto.
    - erewrite vnth_vapp_r. rewrite vnth_vtailN.
      rewrite fAddRangeAddL_fAddRangeAddL'. auto.
      Unshelve. auto. lia.
  Qed.

End vapp.
Infix "++" := vapp : vec_scope.

Section vapp_extra.
  Context {tA tB tC : Type}.

  (* map2 (a++b) (c++d) = (map2 a c) ++ (map2 b d) *)
  Lemma vmap2_vapp_vapp :
    forall {n m} (f : tA -> tB -> tC)
           (a : @vec tA n) (b : @vec tA m) (c : @vec tB n) (d : @vec tB m),
      vmap2 f (a ++ b) (c ++ d) = (vmap2 f a c) ++ (vmap2 f b d).
  Proof.
    intros. unfold vmap2. apply veq_iff_vnth. intros.
    destruct (i ??< n).
    - erewrite !vnth_vapp_l. auto.
    - erewrite !vnth_vapp_r. auto.
      Unshelve. auto. lia.
  Qed.

End vapp_extra.


(* ######################################################################### *)
(** * Predicate of vectors *)

(* ======================================================================= *)
(** ** All elements of the vector hold *)
Section vforall.
  Context {tA : Type}.

  (** Every element of `a` satisfy the `P` *)
  Definition vforall {n} (a : @vec tA n) (P : tA -> Prop) : Prop := forall i, P (a.[i]).
End vforall.

(* ======================================================================= *)
(** ** At least one element of the vector holds *)
Section vexist.
  Context {tA : Type}.

  (** There exist element of `v` satisfy the `P` *)
  Definition vexist {n} (a : @vec tA n) (P : tA -> Prop) : Prop := exists i, P (a.[i]).
End vexist.

(* ======================================================================= *)
(** ** An element belongs to the vector *)
Section vmem.
  Context {tA : Type}.

  (** Element `x` belongs to the vector `a` *)
  Definition vmem {n} (a : @vec tA n) (x : tA) : Prop := vexist a (fun x0 => x0 = x).

  Lemma vmem_vnth : forall {n} (a : @vec tA n) (i : 'I_n), vmem a (a.[i]).
  Proof. intros. hnf. exists i; auto. Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq tA)}.
    
    (** {x ∈ a} + {x ∉ a} *)
    Lemma vmem_dec : forall {n} (a : @vec tA n) (x : tA), {vmem a x} + {~vmem a x}.
    Proof.
      intros. unfold vmem, vexist. induction n.
      - right. intro. destruct H. apply fin0_False; auto.
      - rewrite <- (vconsH_vhead_vremoveH a).
        destruct (Aeqdec (vhead a) x) as [H|H].
        + left. exists fin0. rewrite vnth_vconsH_0; auto.
        + destruct (IHn (vremoveH a)) as [H1|H1].
          * left. destruct H1 as [i H1]. exists (fSuccRangeS i).
            erewrite vnth_vconsH_gt0.
            rewrite fPredRangeP_fSuccRangeS. auto.
          * right. intro. destruct H1. destruct H0 as [i H0].
            destruct (i ??= 0).
            ** rewrite vnth_vconsH_0 in H0; auto; try easy.
               destruct i; simpl in *; apply fin_eq_iff; auto.
            ** erewrite vnth_vconsH_gt0 in H0.
               eexists (fPredRangeP i _). apply H0.
               Unshelve. all: try lia. rewrite fin2nat_fSuccRangeS. lia.
    Qed.
    
  End AeqDec.
  
End vmem.

(* ======================================================================= *)
(** ** An vector belongs to another vector *)
Section vmems.
  Context {tA : Type}.

  (** Every element of vector `a` belongs to vector `b` *)
  Definition vmems {r s} (a : @vec tA r) (b : @vec tA s) : Prop :=
    vforall a (fun x => vmem b x).

  Lemma vmems_refl : forall {n} (a : @vec tA n), vmems a a.
  Proof. intros. unfold vmems, vforall. apply vmem_vnth. Qed.

  Lemma vmems_trans : forall {r s t} (a : @vec tA r) (b : @vec tA s) (c : @vec tA t),
      vmems a b -> vmems b c -> vmems a c.
  Proof.
    intros. unfold vmems, vforall in *. intros.
    specialize (H i). destruct H as [j H]. rewrite <- H. auto.
  Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq tA)}.

    (** {a ⊆ b} + {~(a ⊆ b)} *)
    Lemma vmems_dec : forall {r s} (a : @vec tA r) (b : @vec tA s),
        {vmems a b} + {~vmems a b}.
    Proof.
      intros. unfold vmems, vforall. induction r.
      - left. intro. exfalso. apply fin0_False; auto.
      - rewrite <- (vconsH_vhead_vremoveH a).
        specialize (IHr (vremoveH a)). destruct IHr as [H|H].
        + destruct (vmem_dec b (vhead a)) as [H1|H1].
          * left. intros. destruct (i ??= 0).
            ** rewrite vnth_vconsH_0; auto.
               destruct i; simpl in *; apply fin_eq_iff; auto.
            ** erewrite vnth_vconsH_gt0; auto.
          * right. apply ex_not_not_all. exists fin0. rewrite vnth_vconsH_0; auto.
        + right. intro. destruct H. intro.
          specialize (H0 (fSuccRangeS i)).
          assert (0 < (fSuccRangeS i)).
          apply fin2nat_fSuccRangeS_gt0.
          rewrite vnth_vconsH_gt0 with (H:=H) in H0.
          rewrite fPredRangeP_fSuccRangeS in H0. auto.
          Unshelve. lia.
    Qed.
    
  End AeqDec.
End vmems.

(* ======================================================================= *)
(** ** Two vectors are equivalent (i.e., contain each other) *)
Section vequiv.
  Context {tA : Type}.

  (** Two vectors are equivalent (i.e., contain each other) *)
  Definition vequiv {r s} (a : @vec tA r) (b : @vec tA s) : Prop :=
    vmems a b /\ vmems b a.

  Lemma vequiv_refl : forall {n} (a : @vec tA n), vequiv a a.
  Proof. intros. unfold vequiv. split; apply vmems_refl. Qed.
  
  Lemma vequiv_syms : forall {r s} (a : @vec tA r) (b : @vec tA s), vequiv a b -> vequiv b a.
  Proof. intros. unfold vequiv in *. tauto. Qed.
  
  Lemma vequiv_trans : forall {r s t} (a : @vec tA r) (b : @vec tA s) (c : @vec tA t),
      vequiv a b -> vequiv b c -> vequiv a c.
  Proof.
    intros. unfold vequiv in *. destruct H as [H1 H2], H0 as [H3 H4]. split.
    apply vmems_trans with b; auto.
    apply vmems_trans with b; auto.
  Qed.

  (* If we have AeqDec *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq tA)}.

    (** {a ∼ b} + {~(a ∼ b)} *)
    Lemma vequiv_dec : forall {r s} (a : @vec tA r) (b : @vec tA s),
        {vequiv a b} + {~ vequiv a b}.
    Proof.
      intros. unfold vequiv. destruct (vmems_dec a b), (vmems_dec b a); try tauto.
    Qed.
  End AeqDec.
End vequiv.

Section test.
  Let a : vec 2 := l2v 9 [1;2].
  Let b : vec 3 := l2v 9 [1;2;1].
  Example vequiv_example1 : vequiv a b.
  Proof.
    unfold a, b, vequiv, vmems, vmem, vforall, vexist. split.
    - intros. destruct i as [i Hi].
      repeat (destruct i; try lia); try rewrite vnth_l2v; simpl.
      exists (nat2finS 0); auto.
      exists (nat2finS 1); auto.
    - intros. destruct i as [i Hi].
      repeat (destruct i; try lia); try rewrite vnth_l2v; simpl.
      exists (nat2finS 0); auto.
      exists (nat2finS 1); auto.
      exists (nat2finS 0); auto.
  Qed.
End test.

(* (* ======================================================================= *) *)
(* (** ** An vector belongs to one but not belong to another *) *)
(* Section vdiff. *)
(*   Context {tA : Type}. *)

(*   (** Elements belong to vector `u` but not belongs to vector `v` *) *)
(*   Definition vdiff {r s} (a : @vec tA r) (b : @vec tA s) : Prop. *)
(*     Check fun i => vmem  *)
(*     vforall a (fun x => vmem b x). *)

(* End vmems. *)


(* ######################################################################### *)
(** * Folding of a vector *)

(* ======================================================================= *)
(** ** Folding of a vector *)
Section vfold.
  Context {tA tB : Type} {Azero : tA} {Bzero : tB}. 

  (** ((x + a.1) + a.2) + ... *)
  Definition vfoldl {n} (a : @vec tA n) (x : tB) (f : tB -> tA -> tB) : tB :=
    seqfoldl (v2f Azero a) n x f.
  
  (** ... + (v.(n-1) + (v.n + x)) *)
  Definition vfoldr {n} (a : @vec tA n) (x : tB) (f : tA -> tB -> tB) : tB :=
    seqfoldr (v2f Azero a) n x f.

  (** Convert `vfoldl` to `seqfoldl` *)
  Lemma vfoldl_eq_seqfoldl :
    forall {n} (a : @vec tA n) (x : tB) (f : tB -> tA -> tB) (s : nat -> tA),
      (forall i, a.[i] = s (i)) -> vfoldl a x f = seqfoldl s n x f.
  Proof.
    intros. unfold vfoldl. apply seqfoldl_eq; auto.
    intros. rewrite nth_v2f with (H:=H0). rewrite H.
    rewrite fin2nat_nat2fin. auto.
  Qed.
  
End vfold.


(* ######################################################################### *)
(** * Algebraic operations *)

(* ======================================================================= *)
(** ** Sum of a vector *)
Section vsum.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation seqsum := (@seqsum _ Aadd 0).

  (** ∑a = a.0 + a.1 + ... + a.(n-1) *)
  Definition vsum {n} (a : @vec tA n) := seqsum n (v2f 0 a).
  Notation "\sum a" := (vsum a) : vec_scope.

  (** (∀ i, a.i = b.i) -> Σa = Σb *)
  Lemma vsum_eq : forall {n} (a b : @vec tA n), (forall i, a.[i] = b.[i]) -> \sum a = \sum b.
  Proof.
    intros. unfold vsum. apply seqsum_eq; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.

  (** (∀ i, a.i = 0) -> Σa = 0 *)
  Lemma vsum_eq0 : forall {n} (a : @vec tA n), (forall i, a.[i] = 0) -> \sum a = 0.
  Proof.
    intros. unfold vsum. apply seqsum_eq0; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.
  
  (** `vsum` of (S n) elements, equal to addition of Sum and tail *)
  Lemma vsumS_tail : forall {n} (a : @vec tA (S n)),
      \sum a = \sum (fun i => a.[fSuccRange i]) + a.[nat2finS n].
  Proof.
    intros. unfold vsum. rewrite seqsumS_tail. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal.
      erewrite fSuccRange_nat2fin. auto.
    - erewrite nth_v2f. erewrite nat2finS_eq. auto.
      Unshelve. all: try lia.
  Qed.

  (** `vsum` of (S n) elements, equal to addition of head and Sum *)
  Lemma vsumS_head : forall {n} (a : @vec tA (S n)),
      \sum a = a.[nat2finS 0] + \sum (fun i => a.[fSuccRangeS i]).
  Proof.
    intros. unfold vsum. rewrite seqsumS_head; auto. f_equal.
    apply seqsum_eq; intros. erewrite !nth_v2f. f_equal.
    erewrite fSuccRangeS_nat2fin. auto.
    Unshelve. lia. auto.
  Qed.

  (** Σa + Σb = Σ(fun i => a.[i] + b.[i]) *)
  Lemma vsum_add : forall {n} (a b : @vec tA n),
      \sum a + \sum b = \sum (fun i => a.[i] + b.[i]).
  Proof.
    intros. unfold vsum. rewrite seqsum_add. apply seqsum_eq; intros.
    rewrite !nth_v2f with (H:=H). auto.
  Qed.
  
  (** `vsum` which only one item is nonzero, then got this item. *)
  Lemma vsum_unique : forall {n} (a : @vec tA n) (x : tA) i,
      a.[i] = x -> (forall j, i <> j -> a.[j] = Azero) -> \sum a = x.
  Proof.
    intros. unfold vsum. apply seqsum_unique with (i:=i); auto; fin.
    - rewrite <- H. rewrite nth_v2f with (H:=fin2nat_lt _); fin.
    - intros. unfold v2f. fin.
      specialize (H0 (nat2fin j E)). rewrite <- H0; auto.
      intro; destruct H2; subst. fin.
  Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      Σ[0,(m+n)] a = Σ[0,m](fun i=>a[i]) + Σ[m,m+n] (fun i=>a[m+i]) *)
  Lemma vsum_plusIdx : forall m n (a : @vec tA (m + n)),
      \sum a = \sum (fun i => a.[fAddRangeR i]) +
                 \sum (fun i => a.[fAddRangeAddL i]).
  Proof.
    intros. unfold vsum. rewrite seqsum_plusIdx. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
    - apply seqsum_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

  (** `vsum` of the m+n elements equal to plus of two parts.
      (i < m -> a.i = b.i) ->
      (i < n -> a.(m+i) = c.i) ->
      Σ[0,(m+n)] a = Σ[0,m] b + Σ[m,m+n] c. *)
  Lemma vsum_plusIdx_ext : forall m n (a : @vec tA (m + n)) (b : @vec tA m) (c : @vec tA n),
      (forall i : 'I_m, a.[fAddRangeR i] = b.[i]) ->
      (forall i : 'I_n, a.[fAddRangeAddL i] = c.[i]) ->
      \sum a = \sum b + \sum c.
  Proof.
    intros. unfold vsum. rewrite seqsum_plusIdx. f_equal.
    - apply seqsum_eq; intros. erewrite !nth_v2f. rewrite <- H. f_equal.
      apply fin_eq_iff; auto.
    - apply seqsum_eq; intros. erewrite !nth_v2f. rewrite <- H0. f_equal.
      apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

  (** The order of two nested summations can be exchanged.
      ∑[i,0,r](∑[j,0,c] a.ij) = 
      a00 + a01 + ... + a0c + 
      a10 + a11 + ... + a1c + 
      ...
      ar0 + ar1 + ... + arc = 
      ∑[j,0,c](∑[i,0,r] a.ij) *)
  Lemma vsum_vsum : forall r c (a : @vec (@vec tA c) r),
      \sum (fun i => \sum (fun j => a.[i].[j])) =
        \sum (fun j => \sum (fun i => a.[i].[j])).
  Proof.
    intros. unfold vsum. destruct r,c; auto.
    - rewrite seqsumS_tail. simpl. rewrite seqsum_eq0; auto.
      * amonoid. unfold v2f. fin.
      * intros. unfold v2f. fin.
    - rewrite seqsumS_tail. simpl. rewrite seqsum_eq0; auto.
      * amonoid. unfold v2f. fin.
      * intros. unfold v2f. fin.
    - pose proof (seqsum_seqsum (S r) (S c) (fun i j => a #i #j)).
      match goal with
      | H: ?a1 = ?b1 |- ?a2 = ?b2 => replace a2 with a1;[replace b2 with b1|]; auto
      end.
      + apply seqsum_eq; intros. rewrite nth_v2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_v2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
      + apply seqsum_eq; intros. rewrite nth_v2f with (H:=H0).
        apply seqsum_eq; intros. rewrite nth_v2f with (H:=H1).
        f_equal; apply nat2finS_eq; apply fin_eq_iff.
  Qed.

  (* ∑ (a ++ b) = ∑a + ∑b *)
  Lemma vsum_vapp : forall {m n} (a : @vec tA m) (b : @vec tA n),
      \sum (a ++ b) = \sum a + \sum b.
  Proof.
    intros. apply vsum_plusIdx_ext; intros.
    - erewrite vnth_vapp_l. f_equal. rewrite fAddRangeR'_fAddRangeR. auto.
    - erewrite vnth_vapp_r. f_equal.
      rewrite fAddRangeAddL'_fAddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fAddRangeR. apply fin2nat_lt.
      rewrite fin2nat_fAddRangeAddL. lia.
  Qed.

  (** ∑ (vconsT a x) = ∑ a + x *)
  Lemma vsum_vconsT : forall {n} (a : @vec tA n) (x : tA),
      \sum (vconsT a x) = \sum a + x.
  Proof.
    intros. rewrite vsumS_tail. f_equal.
    - apply vsum_eq; intros. erewrite vnth_vconsT_lt. fin.
    - rewrite vnth_vconsT_n; auto. fin.
      Unshelve. fin.
  Qed.
  
  (* If equip a `AGroup` *)
  Section AGroup.
    Context `{HAGroup : AGroup tA Aadd Azero Aopp}.
    Notation "- a" := (Aopp a) : A_scope.
    
    (** - Σa = Σ(fun i => -a.[i]) *)
    Lemma vsum_opp : forall {n} (a : @vec tA n),
        - \sum a = \sum (fun i => - a.[i]).
    Proof.
      intros. unfold vsum. rewrite seqsum_opp; auto. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
  End AGroup.

  (* If equip a `SRing` *)
  Section SRing.
    Context `{HSRing:SRing tA Aadd Azero Amul Aone}.
    Infix "*" := (Amul) : A_scope.

    (** x * Σa = Σ(fun i -> x * a.[i]) *)
    Lemma vsum_scal_l : forall {n} (a : @vec tA n) x,
        x * \sum a = \sum (fun i => x * a.[i]).
    Proof.
      intros. unfold vsum. rewrite seqsum_scal_l. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
    
    (** Σa * x = Σ(fun i -> a.[i] * x) *)
    Lemma vsum_scal_r : forall {n} (a : @vec tA n) x,
        \sum a * x = \sum (fun i => a.[i] * x).
    Proof.
      intros. unfold vsum. rewrite seqsum_scal_r. apply seqsum_eq; intros.
      unfold v2f. fin.
    Qed.
  End SRing.

  (* if equip a `OrderedARing` *)
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing tA Aadd Azero Aopp Amul Aone Alt Ale}.
    (* Check HOrderedARing : Order Alt Ale Altb Aleb. *)
    Infix "*" := (Amul) : A_scope.
    Infix "<" := Alt.
    Infix "<=" := Ale.

    (** (∀ i, 0 <= a.i) -> a.i <= ∑a *)
    Lemma vsum_ge_any : forall {n} (a : @vec tA n) i,
        (forall i, Azero <= a.[i]) -> a.[i] <= \sum a.
    Proof.
      intros. unfold vsum.
      replace (a i) with (v2f 0 a (i)).
      - apply seqsum_ge_any; fin. intros. unfold v2f. fin.
      - erewrite nth_v2f. f_equal. rewrite nat2fin_fin2nat; auto.
        Unshelve. apply fin2nat_lt.
    Qed.

    (** (∀ i, 0 <= a.i) -> 0 <= ∑a *)
    Lemma vsum_ge0 : forall {n} (a : @vec tA n), (forall i, Azero <= a.[i]) -> Azero <= \sum a.
    Proof.
      intros. pose proof (vsum_ge_any a). destruct n.
      - cbv. apply le_refl.
      - apply le_trans with (a.1); auto.
    Qed.
    
    (** (∀ i, 0 <= a.i) -> (∃ i, a.i <> 0) -> 0 < ∑a *)
    Lemma vsum_gt0 : forall {n} (a : @vec tA n),
        (forall i, Azero <= a.[i]) -> (exists i, a.[i] <> Azero) -> Azero < \sum a.
    Proof.
      intros. destruct H0 as [i H0].
      pose proof (vsum_ge0 a H). pose proof (vsum_ge_any a i H).
      assert (Azero < a.[i]). apply lt_if_le_and_neq; auto.
      apply lt_trans_lt_le with (a.[i]); auto.
    Qed.
    
    (** (∀i, a.i >= 0) -> ∑a = 0 -> (∀i, a.i = 0) *)
    Lemma vsum_eq0_rev : forall {n} (a : @vec tA n),
        (forall i, 0 <= a.[i]) -> \sum a = 0 -> (forall i, a.[i] = 0).
    Proof.
      intros. destruct (Aeqdec (a.[i]) 0); auto. exfalso.
      pose proof (vsum_ge_any a i H). rewrite H0 in H1.
      specialize (H i).
      assert (a.[i] = 0). apply le_antisym; auto. easy.
    Qed.
    
  End OrderedARing.

End vsum.

Arguments vsum {tA} Aadd Azero {n}.


(** vsum with vinsert and vremove  *)
Section vsum_vinsert_vremove.
  Context `{HAGroup : AGroup}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + - b).
  Infix "-" := Asub : A_scope.
  Notation vsum := (@vsum _ Aadd Azero).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation seqsum_plusIdx := (@seqsum_plusIdx _ Aadd Azero).

  (** ∑(insert a i x) = ∑a + x *)
  Lemma vsum_vinsert : forall {n} (a : @vec tA n) (x : tA) (i : 'I_(S n)),
      vsum (vinsert a i x) = vsum a + x.
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vinsert_eq_vinsert' _ (Azero:=Azero)).
    unfold vinsert'. unfold vsum.
    replace (S n) with (i + (S (n - i)))%nat at 1 by lia.
    replace n with (i + (n - i))%nat at 6 by lia.
    rewrite !seqsum_plusIdx. rewrite seqsumS_head.
    match goal with
    | |- ?a+(?b+?c) = _ => replace (a+(b+c)) with (a+c+b) by agroup end. f_equal.
    - f_equal.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
    - unfold v2f,f2v. fin.
  Qed.

  (** ∑(remove a i) = ∑a - a.i *)
  Lemma vsum_vremove : forall {n} (a : @vec tA (S n)) (i : 'I_(S n)),
      vsum (vremove a i) = vsum a - a.[i].
  Proof.
    intros. pose proof (fin2nat_lt i).
    rewrite (vremove_eq_vremove' (Azero:=Azero)).
    unfold vremove'. unfold vsum.
    replace n with (i + (n - i))%nat at 1 by lia.
    replace (S n) with (i + (S (n - i)))%nat at 3 by lia.
    rewrite !seqsum_plusIdx. rewrite seqsumS_head.
    match goal with
    | |- _ = ?d + (?e + ?f) - ?g => replace (d + (e + f) - g) with (d + f) end.
    - f_equal.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
      + apply seqsum_eq; intros. unfold v2f,f2v. fin.
    - agroup. unfold v2f.
      replace (i + O)%nat with (fin2nat i) by lia. fin. agroup.
  Qed.
  
End vsum_vinsert_vremove.

(** Extension for `vsum` *)
Section vsum_ext.
  
  Context `{HAMonoidA : AMonoid}.
  Context `{HAMonoidB : AMonoid tB Badd Bzero}.
  Context (scal : tA -> tB -> tB).
  Infix "+A" := Aadd (at level 50).
  Infix "+B" := Badd (at level 50).
  Infix "*" := scal.
  Notation vsumA := (@vsum _ Aadd Azero).
  Notation vsumB := (@vsum _ Badd Bzero).
  
  (** ∑(x*ai) = x * a1 + ... + x * ai = x * (a1 + ... + ai) = x * ∑(ai) *)
  Section form1.
    Context (scal_zero_keep : forall x : tA, x * Bzero = Bzero).
    Context (scal_badd : forall (x : tA) (y1 y2 : tB), x * (y1 +B y2) = (x * y1) +B (x * y2)).
    
    Lemma vsum_scal_l_ext : forall {n} (x : tA) (a : @vec tB n),
        x * vsumB a = vsumB (fun i => x * a.[i]).
    Proof.
      intros. unfold vsumB. rewrite seqsum_scal_l_ext; auto.
      apply seqsum_eq; intros. rewrite !nth_v2f with (H:=H). auto.
    Qed.
  End form1.
  
  (** ∑(ai*x) = a1 * x + ... + ai * x = (a1 + ... + ai) * b = ∑(ai) * x *)
  Section form2.
    Context (scal_zero_keep : forall x : tB, Azero * x = Bzero).
    Context (scal_aadd : forall (x1 x2 : tA) (y : tB), (x1 +A x2) * y = (x1 * y) +B (x2 * y)).

    Lemma vsum_scal_r_ext : forall {n} (x : tB) (a : @vec tA n),
        vsumA a * x = vsumB (fun i => a.[i] * x).
    Proof.
      intros. unfold vsumB. rewrite seqsum_scal_r_ext; auto.
      apply seqsum_eq; intros. rewrite !nth_v2f with (H:=H). auto.
    Qed.
  End form2.
  
End vsum_ext.


(* ======================================================================= *)
(** ** Product of a vector *)
Section vprod.
  Context `{HARing : ARing}.
  Infix "*" := Amul : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation seqprod := (@seqprod _ Amul 1).

  (** Πa = a.0 * a.1 * ... * a.(n-1) *)
  Definition vprod {n} (a : @vec tA n) := seqprod n (v2f 0 a).
  Notation "\prod a" := (vprod a) : vec_scope.

  (** (∀ i, a.i = b.i) -> Πa = Πb *)
  Lemma vprod_eq : forall {n} (a b : @vec tA n), (forall i, a.[i] = b.[i]) -> vprod a = vprod b.
  Proof.
    intros. unfold vprod. apply seqprod_eq; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.

  (** (∀ i, a.i = 1) -> Πa = 1 *)
  Lemma vprod_eq1: forall {n} (a : @vec tA n), (forall i, a.[i] = 1) -> vprod a = 1.
  Proof.
    intros. unfold vprod. apply seqprod_eq1; intros.
    rewrite !nth_v2f with (H:=H0). apply H.
  Qed.
  
  (** `vprod` of (S n) elements, equal to multiplication of Prod and tail *)
  Lemma vprodS_tail : forall {n} (a : @vec tA (S n)),
      vprod a = vprod (fun i => a.[fSuccRange i]) * a.[nat2finS n].
  Proof.
    intros. unfold vprod. rewrite seqprodS_tail. f_equal.
    - apply seqprod_eq; intros. erewrite !nth_v2f. f_equal.
      erewrite fSuccRange_nat2fin. auto.
    - erewrite nth_v2f. erewrite nat2finS_eq. auto.
      Unshelve. all: try lia.
  Qed.

  (** `vprod` of (S n) elements, equal to multiplication of head and Prod *)
  Lemma vprodS_head : forall {n} (a : @vec tA (S n)),
      vprod a = a.[nat2finS 0] * vprod (fun i => a.[fSuccRangeS i]).
  Proof.
    intros. unfold vprod. rewrite seqprodS_head; auto. f_equal.
    apply seqprod_eq; intros. erewrite !nth_v2f. f_equal.
    erewrite fSuccRangeS_nat2fin. auto.
    Unshelve. lia. auto.
  Qed.

  (** `vprod` which only one item is non-one, then got this item. *)
  Lemma vprod_unique : forall {n} (a : @vec tA n) (x : tA) i,
      a.[i] = x -> (forall j, i <> j -> a.[j] = 1) -> vprod a = x.
  Proof.
    intros. unfold vprod. apply seqprod_unique with (i:=i); auto; fin.
    - rewrite <- H. rewrite nth_v2f with (H:=fin2nat_lt _); fin.
    - intros. unfold v2f. fin.
      specialize (H0 (nat2fin j E)). rewrite <- H0; auto.
      intro; destruct H2; subst. fin.
  Qed.

  (** `vprod` of the m+n elements equal to multiplication of two parts.
      Π[0,(m+n)] a = Π[0,m](fun i=>a[i]) * Π[m,m+n] (fun i=>a[m+i]) *)
  Lemma vprod_plusIdx : forall m n (a : @vec tA (m + n)),
      vprod a = vprod (fun i => a.[fAddRangeR i]) *
                 vprod (fun i => a.[fAddRangeAddL i]).
  Proof.
    intros. unfold vprod. rewrite seqprod_plusIdx. f_equal.
    - apply seqprod_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
    - apply seqprod_eq; intros. erewrite !nth_v2f. f_equal. apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

  (** `vprod` of the m+n elements equal to multiplication of two parts.
      (i < m -> a.i = b.i) ->
      (i < n -> a.(m+i) = c.i) ->
      Π[0,(m+n)] a = Π[0,m] b * Π[m,m+n] c. *)
  Lemma vprod_plusIdx_ext : forall m n (a : @vec tA (m + n)) (b : @vec tA m) (c : @vec tA n),
      (forall i : 'I_m, a.[fAddRangeR i] = b.[i]) ->
      (forall i : 'I_n, a.[fAddRangeAddL i] = c.[i]) ->
      vprod a = vprod b * vprod c.
  Proof.
    intros. unfold vprod. rewrite seqprod_plusIdx. f_equal.
    - apply seqprod_eq; intros. erewrite !nth_v2f. rewrite <- H. f_equal.
      apply fin_eq_iff; auto.
    - apply seqprod_eq; intros. erewrite !nth_v2f. rewrite <- H0. f_equal.
      apply fin_eq_iff; auto.
      Unshelve. all: try lia.
  Qed.

End vprod.

Arguments vprod {tA} Azero Amul Aone {n}.


(* ======================================================================= *)
(** ** Vector addition *)
Section vadd.
  Context `{AMonoid}.
  Infix "+" := Aadd : A_scope.
  
  Notation vec := (@vec tA).
  Notation vzero := (vzero Azero).

  Definition vadd {n} (a b : vec n) : vec n := vmap2 Aadd a b.
  (* Definition vadd' {n} (a b : vec n) : vec n := fun i => Aadd (a.[i]) (b.[i]). *)

  Infix "+" := vadd : vec_scope.

  (** (a + b) + c = a + (b + c) *)
  Lemma vadd_assoc : forall {n} (a b c : vec n), (a + b) + c = a + (b + c).
  Proof. intros. apply vmap2_assoc. Qed.

  (** a + b = b + a *)
  Lemma vadd_comm : forall {n} (a b : vec n), a + b = b + a.
  Proof. intros. apply vmap2_comm. Qed.

  (** 0 + a = a *)
  Lemma vadd_0_l : forall {n} (a : vec n), vzero + a = a.
  Proof.
    intros. apply veq_iff_vnth; intros. unfold vadd. rewrite vnth_vmap2.
    rewrite vnth_vzero. amonoid.
  Qed.

  (** a + 0 = a *)
  Lemma vadd_0_r : forall {n} (a : vec n), a + vzero = a.
  Proof. intros. rewrite vadd_comm. apply vadd_0_l. Qed.

  (** <vadd,vzero> is an abelian monoid *)
  #[export] Instance vadd_AMonoid : forall n, AMonoid (@vadd n) vzero.
  Proof.
    intros. repeat constructor; intros;
      try apply vadd_assoc;
      try apply vadd_comm;
      try apply vadd_0_l;
      try apply vadd_0_r.
  Qed.

  (** (a + b).i = a.i + b.i *)
  Lemma vnth_vadd : forall {n} (a b : vec n) i, (a + b).[i] = (a.[i] + b.[i])%A.
  Proof. intros. unfold vadd. rewrite vnth_vmap2. auto. Qed.
  
  (** (a + b) + c = (a + c) + b *)
  Lemma vadd_perm : forall {n} (a b c : vec n), (a + b) + c = (a + c) + b.
  Proof. intros. rewrite !associative. f_equal. apply commutative. Qed.

  (** [∑_(j=0)^k {f(j)}].i = ∑_(j=0)^k {[f (j)].i} *)
  Lemma vnth_seqsum_vadd : forall (n : nat) (f : nat -> vec n) (k : nat) (i : 'I_n),
      (@seqsum _ vadd vzero k f) i = (@seqsum _ Aadd Azero k (fun x => f x i)).
  Proof.
    intros. induction k; simpl; auto. unfold seqsum in *.
    rewrite seqsumAux_rebase. symmetry. rewrite seqsumAux_rebase.
    rewrite !vnth_vadd. rewrite IHk. auto.
  Qed.

End vadd.

Section vadd_extra.
  Context `{AMonoid}.

  (* 所有向量相加后取第j个分量 = 取出向量的第j个分量后再相加 *)
  (** (∑a).j = ∑(a.j), which a is a vector of vector *)
  Lemma vnth_vsum : forall {r c} (a : @vec (@vec tA c) r) j,
      (@vsum _ (@vadd _ Aadd _) (vzero Azero) _ a).[j] =
        @vsum _ Aadd Azero _ (fun i => a.[i].[j]).
  Proof.
    induction r; intros; auto.
    rewrite !vsumS_tail. rewrite vnth_vadd. rewrite IHr. auto.
  Qed.
  
End vadd_extra.

(** ** Vector opposition *)
Section vopp.
  
  (* Let's have an Abelian-Group *)
  Context `{AGroup tA Aadd Azero}.
  Notation "- a" := (Aopp a) : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.

  Definition vopp {n} (a : vec n) : vec n := vmap Aopp a.
  (* Definition vopp' {n} (a : vec n) : vec n := fun i => Aopp a.[i]. *)
  Notation "- a" := (vopp a) : vec_scope.

  (** (- a).i = - (a.i) *)
  Lemma vnth_vopp : forall {n} (a : vec n) i, (- a).[i] = (- (a.[i]))%A.
  Proof. intros. cbv. auto. Qed.

  (** - a + a = 0 *)
  Lemma vadd_vopp_l : forall {n} (a : vec n), (- a) + a = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. agroup. Qed.
  
  (** a + - a = 0 *)
  Lemma vadd_vopp_r : forall {n} (a : vec n), a + (- a) = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. agroup. Qed.

  (** <vadd,vzero,vopp> is an abelian group *)
  #[export] Instance vadd_AGroup : forall n, @AGroup (vec n) vadd vzero vopp.
  Proof.
    intros. repeat constructor; intros; try apply vadd_AMonoid.
    apply vadd_vopp_l. apply vadd_vopp_r.
  Qed.

  (* Now, we ca use group theory on this instance *)

  (** - (- a) = a *)
  Lemma vopp_vopp : forall {n} (a : vec n), - (- a) = a.
  Proof.
    (* intros. apply group_opp_opp. *)
    intros. pose proof (vadd_AGroup n). agroup.
  Qed.

  (** a = - b <-> - a = b *)
  Lemma vopp_exchange : forall {n} (a b : vec n), a = - b <-> - a = b.
  Proof. intros. split; intros; subst; rewrite vopp_vopp; auto. Qed.

  (** - (vzero) = vzero *)
  Lemma vopp_vzero : forall {n:nat}, - (@Vector.vzero _ Azero n) = vzero.
  Proof. intros. apply group_opp_0. Qed.

  (** - a = vzero <-> a = vzero *)
  Lemma vopp_eq0_iff : forall {n} (a : vec n), - a = vzero <-> a = vzero.
  Proof.
    intros. split; intros; rewrite veq_iff_vnth in *; intros;
      specialize (H0 i); rewrite vnth_vzero, vnth_vopp in *.
    - apply group_opp_eq0_iff; auto.
    - apply group_opp_eq0_iff; auto.
  Qed.
  
  (** - (a + b) = (- a) + (- b) *)
  Lemma vopp_vadd : forall {n} (a b : vec n), - (a + b) = (- a) + (- b).
  Proof. intros. rewrite group_opp_distr. apply commutative. Qed.

  (** a + b = 0 -> - a = b *)
  Lemma vadd_eq0_imply_vopp_l : forall {n} (a b : vec n), a + b = vzero -> - a = b.
  Proof. intros. apply group_opp_uniq_l; auto. Qed.
    
  (** a + b = 0 -> - b = a *)
  Lemma vadd_eq0_imply_vopp_r : forall {n} (a b : vec n), a + b = vzero -> - b = a.
  Proof. intros. apply group_opp_uniq_r; auto. Qed.

End vopp.

(** ** Vector subtraction *)
Section vsub.
  (* Let's have an Abelian-Group *)
  Context `{AGroup tA Aadd Azero}.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.

  Notation "a - b" := ((a + -b)%V) : vec_scope.
  (* Definition vsub {n} (a b : vec n) : vec n := a + (- b). *)
  (* Infix "-" := vsub : vec_scope. *)

  (** (a - b).i = a.i - b.i *)
  Lemma vnth_vsub : forall {n} (a b : vec n) i, (a - b).[i] = (a.[i] - b.[i])%A.
  Proof. intros. cbv. auto. Qed.

  (** a - b = - (b - a) *)
  Lemma vsub_comm : forall {n} (a b : vec n), a - b = - (b - a).
  Proof.
    intros. rewrite group_opp_distr. rewrite group_opp_opp. auto.
  Qed.

  (** (a - b) - c = a - (b + c) *)
  Lemma vsub_assoc : forall {n} (a b c : vec n), (a - b) - c = a - (b + c).
  Proof.
    intros. rewrite associative.
    f_equal. rewrite group_opp_distr. apply commutative.
  Qed.

  (** (a + b) - c = a + (b - c) *)
  Lemma vsub_assoc1 : forall {n} (a b c : vec n), (a + b) - c = a + (b - c).
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.

  (** (a - b) - c = (a - c) - b *)
  Lemma vsub_assoc2 : forall {n} (a b c : vec n), (a - b) - c = (a - c) - b.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** 0 - a = - a *)
  Lemma vsub_0_l : forall {n} (a : vec n), vzero - a = - a.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** a - 0 = a *)
  Lemma vsub_0_r : forall {n} (a : vec n), a - vzero = a.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.
  
  (** a - a = 0 *)
  Lemma vsub_self : forall {n} (a : vec n), a - a = vzero.
  Proof. intros. pose proof (vadd_AGroup n). agroup. Qed.

  (** a - b = 0 <-> a = b *)
  Lemma vsub_eq0_iff_eq : forall {n} (a b : vec n), a - b = vzero <-> a = b.
  Proof. intros. apply group_sub_eq0_iff_eq. Qed.
End vsub.


(** ** Vector scalar multiplication *)
Section vscal.
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing tA Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + (-b))%V) : vec_scope.
  
  Definition vscal {n : nat} (x : tA) (a : vec n) : vec n := vmap (Amul x) a.
  Infix "s*" := vscal : vec_scope.

  (** (x s* a).i = x * a.i *)
  Lemma vnth_vscal : forall n (a : vec n) x i, (x s* a).[i] = x * (a.[i]).
  Proof. intros. cbv. auto. Qed.

  (** x s* (y s* a) = (x * y) s* a *)
  Lemma vscal_assoc : forall {n} (a : vec n) x y,
      x s* (y s* a) = (x * y)%A s* a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** x s* (vconsH a v) = vconsH (x * a) (x s* v) *)
  Lemma vscal_vconsH : forall {n} a (v : vec n) x,
      x s* (vconsH a v) = vconsH (x * a) (x s* v).
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_vscal. bdestruct (i =? 0).
    - rewrite !vnth_vconsH_0; auto. all: destruct i; fin.
    - erewrite !vnth_vconsH_gt0; auto. rewrite vnth_vscal. fin. Unshelve. fin.
  Qed.
  
  (** x s* (vconsT v a) = vconsT (x s* v) (x * a) *)
  Lemma vscal_vconsT : forall {n} (v : vec n) a x,
      x s* (vconsT v a) = vconsT (x s* v) (x * a).
  Proof.
    intros. apply veq_iff_vnth; intros. rewrite vnth_vscal. bdestruct (i =? n).
    - rewrite !vnth_vconsT_n; auto.
    - erewrite !vnth_vconsT_lt; auto. rewrite vnth_vscal. fin. Unshelve. fin.
  Qed.

  (** x s* (y s* a) = y s* (x s* a) *)
  Lemma vscal_perm : forall {n} (a : vec n) x y,
      x s* (y s* a) = y s* (x s* a).
  Proof. intros. rewrite !vscal_assoc. f_equal. ring. Qed.
  
  (** (x + y) s* a = (x s* a) + (y s* a) *)
  Lemma vscal_add : forall {n} x y (a : vec n),
      (x + y)%A s* a = (x s* a) + (y s* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** x s* (a + b) = (x s* a) + (x s* b) *)
  Lemma vscal_vadd : forall {n} x (a b : vec n),
      x s* (a + b) = (x s* a) + (x s* b).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (** 0 s* a = vzero *)
  Lemma vscal_0_l : forall n (a : vec n), Azero s* a = vzero.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  Hint Rewrite vscal_0_l : vec.

  (** a s* vzero = vzero *)
  Lemma vscal_0_r : forall n a, a s* vzero = (@Vector.vzero _ Azero n).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  Hint Rewrite vscal_0_r : vec.
  
  (** 1 s* a = a *)
  Lemma vscal_1_l : forall {n} (a : vec n), Aone s* a = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** - 1 s* a = - a *)
  Lemma vscal_neg1_l : forall {n} (a : vec n), (- Aone)%A s* a = - a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.
  
  (** (- x) s* a = - (x s* a) *)
  Lemma vscal_opp : forall {n} x (a : vec n), (- x)%A s* a = - (x s* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by computation, due to the Fin-Function 
     model. *)
  (** x s* (- a) = - (x s* a) *)
  Lemma vscal_vopp : forall {n} x (a : vec n), x s* (- a) = - (x s* a).
  Proof. intros. apply veq_iff_vnth; intros. cbv. ring. Qed.

  (* Tips: this proof shows a proof by derivation *)
  (** (- x) s* (- a) = x s* a *)
  Lemma vscal_opp_vopp : forall {n} x (a : vec n), (- x)%A s* (- a) = x s* a.
  Proof. intros. rewrite vscal_vopp, vscal_opp. rewrite vopp_vopp. auto. Qed.

  (** x s* (a - b) = (x s* a) - (x s* b) *)
  Lemma vscal_vsub : forall {n} x (a b : vec n), x s* (a - b) = (x s* a) - (x s* b).
  Proof. intros. rewrite vscal_vadd. rewrite vscal_vopp. auto. Qed.
  
  (* If equip a `Dec` *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq tA)}.

    (** a <> 0 -> b <> 0 -> x s* a = b -> x <> 0 *)
    Lemma vscal_eq_imply_x_neq0 : forall {n} x (a b : vec n),
        a <> vzero -> b <> vzero -> x s* a = b -> x <> Azero.
    Proof.
      intros. destruct (Aeqdec x Azero); auto. exfalso. subst.
      rewrite vscal_0_l in H0. easy.
    Qed.
  End AeqDec.

  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq tA)}.
    Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.
    
    (** x s* a = 0 -> (x = 0) \/ (a = 0) *)
    Lemma vscal_eq0_imply_x0_or_v0 : forall {n} x (a : vec n),
        x s* a = vzero -> (x = Azero) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Azero); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq0_iff in H; auto. tauto.
    Qed.

    (** x s* a = 0 -> a <> 0 -> x = 0 *)
    Corollary vscal_eq0_imply_x0 : forall {n} x (a : vec n),
        x s* a = vzero -> a <> vzero -> x = Azero.
    Proof. intros. apply (vscal_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x s* a = 0 -> x <> 0 -> a = 0 *)
    Corollary vscal_eq0_imply_v0 : forall {n} x (a : vec n),
        x s* a = vzero -> x <> Azero -> a = vzero.
    Proof. intros. apply (vscal_eq0_imply_x0_or_v0 x a) in H; tauto. Qed.

    (** x <> 0 -> a <> 0 -> x s* a <> 0 *)
    Corollary vscal_neq0_neq0_neq0 : forall {n} x (a : vec n),
        x <> Azero -> a <> vzero -> x s* a <> vzero.
    Proof. intros. intro. apply vscal_eq0_imply_x0_or_v0 in H1; tauto. Qed.
    
    (** x s* a = a -> x = 1 \/ a = 0 *)
    Lemma vscal_same_imply_x1_or_v0 : forall {n} x (a : vec n),
        x s* a = a -> (x = Aone) \/ (a = vzero).
    Proof.
      intros. destruct (Aeqdec x Aone); auto. right.
      apply veq_iff_vnth; intros. rewrite veq_iff_vnth in H. specialize (H i).
      cbv in H. cbv. apply field_mul_eq_imply_a1_or_b0 in H; auto. tauto.
    Qed.
    
    (** x = 1 \/ a = 0 -> x s* a = a *)
    Lemma vscal_same_if_x1_or_v0 : forall {n} x (a : vec n),
        (x = Aone \/ a = vzero) -> x s* a = a.
    Proof.
      intros. destruct H; subst. apply vscal_1_l; auto. apply vscal_0_r; auto.
    Qed.
    
    (** x s* a = a -> a <> 0 -> x = 1 *)
    Corollary vscal_same_imply_x1 : forall {n} x (a : vec n),
        x s* a = a -> a <> vzero -> x = Aone.
    Proof. intros. apply (vscal_same_imply_x1_or_v0 x a) in H; tauto. Qed.
    
    (** x s* a = a -> x <> 1 -> a = 0 *)
    Corollary vscal_same_imply_v0 : forall {n} x (a : vec n),
        x s* a = a -> x <> Aone -> a = vzero.
    Proof. intros. apply (vscal_same_imply_x1_or_v0 x a) in H; tauto. Qed.

    (** x s* a = y s* a -> (x = y \/ a = 0) *)
    Lemma vscal_sameV_imply_eqX_or_v0 : forall {n} x y (a : vec n), 
        x s* a = y s* a -> (x = y \/ a = vzero).
    Proof.
      intros. destruct (Aeqdec x y); auto. right. rewrite veq_iff_vnth in H.
      rewrite veq_iff_vnth. intros. specialize (H i). rewrite !vnth_vscal in H.
      destruct (Aeqdec (a i) Azero); auto. apply field_mul_cancel_r in H; tauto.
    Qed.

    (** x s* a  = y s* a -> x <> y -> a = 0 *)
    Corollary vscal_sameV_imply_v0 : forall {n} x y (a : vec n), 
        x s* a = y s* a -> x <> y -> a = vzero.
    Proof. intros. apply vscal_sameV_imply_eqX_or_v0 in H; tauto. Qed.

    (** x s* a = x s* b -> x <> 0 -> a = b *)
    Lemma vscal_eq_reg_l : forall {n} x (a b : vec n),
        x s* a = x s* b -> x <> Azero -> a = b.
    Proof.
      intros. rewrite veq_iff_vnth in *. intros i. specialize (H i).
      rewrite !vnth_vscal in H. apply field_mul_cancel_l in H; auto.
    Qed.
    
    (** x s* a = y * a -> a <> vzero -> x = y *)
    Lemma vscal_eq_reg_r : forall {n} x y (a : vec n), 
        x s* a = y s* a -> a <> vzero -> x = y.
    Proof. intros. apply vscal_sameV_imply_eqX_or_v0 in H; tauto. Qed.
  End Dec_Field.
End vscal.


(** ** Dot product *)
Section vdot.
  Context `{HSRing : SRing tA Aadd Azero Amul Aone}.
  
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone.
  Notation "a ²" := (a * a) : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vscal := (@vscal _ Amul).
  Notation seqsum := (@seqsum _ Aadd Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  Infix "+" := vadd : vec_scope.
  Infix "s*" := vscal : vec_scope.
  
  Definition vdot {n : nat} (a b : vec n) : tA := vsum (vmap2 Amul a b).
  Notation "< a , b >" := (vdot a b) : vec_scope.

  (** <vzero, a> = vzero *)
  Lemma vdot_0_l : forall {n} (a : vec n), <vzero, a> = Azero.
  Proof.
    intros. unfold vdot. apply vsum_eq0; intros.
    rewrite vnth_vmap2, vnth_vzero. sring.
  Qed.
  
  (** <a, vzero> = vzero *)
  Lemma vdot_0_r : forall {n} (a : vec n), <a, vzero> = Azero.
  Proof.
    intros. unfold vdot. apply vsum_eq0; intros.
    rewrite vnth_vmap2, vnth_vzero. sring.
  Qed.

  (** <a + b, c> = <a, c> + <b, c> *)
  Lemma vdot_vadd_l : forall {n} (a b c : vec n), <a + b, c> = (<a, c> + <b, c>)%A.
  Proof.
    intros. unfold vdot. rewrite vsum_add; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2.
    rewrite vnth_vadd. sring.
  Qed.

  (** <a, b + c> = <a, b> + <a, c> *)
  Lemma vdot_vadd_r : forall {n} (a b c : vec n), <a, b + c> = (<a, b> + <a, c>)%A.
  Proof.
    intros. unfold vdot. rewrite vsum_add; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2.
    rewrite vnth_vadd. sring.
  Qed.

  (** <x s* a, b> = x s* <a, b> *)
  Lemma vdot_vscal_l : forall {n} (a b : vec n) x, <x s* a, b> = x * <a, b>.
  Proof.
    intros. unfold vdot. rewrite vsum_scal_l; intros.
    apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vscal. sring.
  Qed.

  Section Amul_Comm.
    Context {HMulComm : Commutative Amul}.

    (** <a, b> = <b, a> *)
    Lemma vdot_comm : forall {n} (a b : vec n), <a, b> = <b, a>.
    Proof. intros. apply vsum_eq; intros. unfold vmap2. apply commutative. Qed.

    (** <a, x s* b> = x s* <a, b> *)
    Lemma vdot_vscal_r : forall {n} (a b : vec n) x, <a, x s* b> = x * <a, b>.
    Proof.
      intros. unfold vdot. rewrite vsum_scal_l; intros.
      apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vscal. sring.
      f_equal. apply commutative.
    Qed.
  End Amul_Comm.
  
  (** <a, veye i> = a i *)
  Lemma vdot_veye_r : forall {n} (a : vec n) i, <a, veye 0 1 i> = a i.
  Proof.
    intros. apply vsum_unique with (i:=i).
    - rewrite vnth_vmap2. rewrite vnth_veye_eq. rewrite identityRight; auto.
    - intros. rewrite vnth_vmap2. rewrite vnth_veye_neq; auto. sring.
  Qed.

  (** <veye i, a> = a i *)
  Lemma vdot_veye_l : forall {n} (a : vec n) i, <veye 0 1 i, a> = a i.
  Proof.
    intros. apply vsum_unique with (i:=i).
    - rewrite vnth_vmap2. rewrite vnth_veye_eq. rewrite identityLeft; auto.
    - intros. rewrite vnth_vmap2. rewrite vnth_veye_neq; auto. sring.
  Qed.

  (** <vconsT a x, vconsT b y> = <a, b> + x * y *)
  Lemma vdot_vconsT_vconsT : forall {n} (a b : vec n) (x y : tA),
      <vconsT a x, vconsT b y> = (<a, b> + x * y)%A.
  Proof.
    intros. unfold vdot.
    rewrite vmap2_vconsT_vconsT.
    rewrite vsum_vconsT. auto.
  Qed.

  (** <a, b> = <a1, b1> + <a2, b2> *)
  Lemma vdot_vheadN_vtailN : forall m n (v1 v2 : vec (m + n)),
      <v1, v2> = (<vheadN v1, vheadN v2> + <vtailN v1, vtailN v2>)%A.
  Proof. intros. unfold vdot. unfold vmap2. rewrite vsum_plusIdx. auto. Qed.

  (* Let's have an Abelian-ring *)
  Section ARing.

    Context `{HARing : ARing tA Aadd Azero Aopp Amul Aone}.
    Add Ring ring_inst : (make_ring_theory HARing).

    Notation "- a" := (Aopp a) : A_scope.
    Notation Asub a b := (a + (- b))%A.
    Infix "-" := Asub : A_scope.

    Notation vopp := (@vopp _ Aopp).
    Notation "- a" := (vopp a) : vec_scope.
    Notation "a - b" := ((a + -b)%V) : vec_scope.

    (** <- a, b> = - <a, b> *)
    Lemma vdot_vopp_l : forall {n} (a b : vec n), < - a, b> = (- <a, b>)%A.
    Proof.
      intros. unfold vdot. rewrite vsum_opp; intros.
      apply vsum_eq; intros. rewrite !vnth_vmap2. rewrite vnth_vopp. ring.
    Qed.

    (** <a, - b> = - <a, b> *)
    Lemma vdot_vopp_r : forall {n} (a b : vec n), <a, - b> = (- <a, b>)%A.
    Proof. intros. rewrite vdot_comm, vdot_vopp_l, vdot_comm. auto. Qed.

    (** <a - b, c> = <a, c> - <b, c> *)
    Lemma vdot_vsub_l : forall {n} (a b c : vec n), <a - b, c> = (<a, c> - <b, c>)%A.
    Proof. intros. rewrite vdot_vadd_l. f_equal. apply vdot_vopp_l. Qed.

    (** <a, b - c> = <a, b> - <a, c> *)
    Lemma vdot_vsub_r : forall {n} (a b c : vec n), <a, b - c> = (<a, b> - <a, c>)%A.
    Proof. intros. rewrite vdot_vadd_r. f_equal. apply vdot_vopp_r. Qed.
  End ARing.
    
  (* If (@eq tA) is decidable *)
  Section AeqDec.
    Context {AeqDec : Dec (@eq tA)}.

    (** <a, b> <> 0 -> a <> 0 *)
    Lemma vdot_neq0_imply_neq0_l : forall {n} (a b : vec n), <a, b> <> 0 -> a <> vzero.
    Proof.
      intros. destruct (Aeqdec a vzero); auto. subst. rewrite vdot_0_l in H. easy.
    Qed.
    
    (** <a, b> <> 0 -> b <> 0 *)
    Lemma vdot_neq0_imply_neq0_r : forall {n} (a b : vec n), <a, b> <> 0 -> b <> vzero.
    Proof.
      intros. destruct (Aeqdec b vzero); auto. subst. rewrite vdot_0_r in H. easy.
    Qed.
    
    (** (∀ c, <a, c> = <b, c>) -> a = b *)
    Lemma vdot_cancel_r : forall {n} (a b : vec n),
        (forall c : vec n, <a, c> = <b, c>) -> a = b.
    Proof.
      intros. destruct (Aeqdec a b) as [H1|H1]; auto. exfalso.
      apply vneq_iff_exist_vnth_neq in H1. destruct H1 as [i H1].
      specialize (H (veye 0 1 i)). rewrite !vdot_veye_r in H. easy.
    Qed.
    
    (** (∀ c, <c, a> = <c, b>) -> a = b *)
    Lemma vdot_cancel_l : forall {n} (a b : vec n),
        (forall c : vec n, <c, a> = <c, b>) -> a = b.
    Proof.
      intros. destruct (Aeqdec a b) as [H1|H1]; auto. exfalso.
      apply vneq_iff_exist_vnth_neq in H1. destruct H1 as [i H1].
      specialize (H (veye 0 1 i)). rewrite !vdot_veye_l in H. easy.
    Qed.
  End AeqDec.


  (* If equip an ordered-abelian-ring *)
  Section OrderedARing.
    Context `{HOrderedARing : OrderedARing tA Aadd Azero Aopp Amul Aone}.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** 0 <= <a, a> *)
    Lemma vdot_ge0 : forall {n} (a : vec n), 0 <= (<a, a>).
    Proof.
      intros. unfold vdot, vsum, vmap2, v2f. apply seqsum_ge0; intros.
      fin. apply sqr_ge0.
    Qed.

    (** <a, b> ² <= <a, a> * <b, b> *)
    Lemma vdot_sqr_le : forall {n} (a b : vec n), (<a, b> ²) <= <a, a> * <b, b>.
    Proof.
      intros. unfold vdot,vsum,vmap2. destruct n.
      - cbv. apply le_refl.
      - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction" *)
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>a i * b i)) (g:=fun i => a #i * b #i).
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>a i * a i)) (g:=fun i => a #i * a #i).
        rewrite seqsum_eq with (f:=v2f 0 (fun i=>b i * b i)) (g:=fun i => b #i * b #i).
        + apply seqsum_SqrMul_le_MulSqr.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
        + intros. erewrite nth_v2f. erewrite nat2finS_eq; auto.
          Unshelve. all: auto.
    Qed.

    (** (v i)² <= <a, a> *)
    Lemma vnth_sqr_le_vdot : forall {n} (a : vec n) (i : 'I_n), (a i) ² <= <a, a>.
    Proof.
      intros. unfold vdot.
      pose ((fun i => (a.[i]) * (a.[i])) : vec n) as u.
      replace (a i)² with (u i). replace (vmap2 Amul a a) with u.
      apply vsum_ge_any.
      - intros. unfold u. apply sqr_ge0.
      - unfold u. auto.
      - unfold u. auto.
    Qed.
    
  End OrderedARing.

  
  (* If equip an ordered-field and `Dec` *)
  Section OrderedField_Dec.
    Context {AeqDec : Dec (@eq tA)}.
    Context `{HOrderedField : OrderedField tA Aadd Azero Aopp Amul Aone}.
    Add Field field_inst : (make_field_theory HOrderedField).
    
    Notation "/ a" := (Ainv a).
    Notation Adiv x y := (x * / y).
    Infix "/" := Adiv.
    Infix "<" := Alt.
    Infix "<=" := Ale.
    
    (** a = 0 -> <a, a> = 0 *)
    Lemma vdot_same_eq0_if_vzero : forall {n} (a : vec n), a = vzero -> <a, a> = 0.
    Proof. intros. subst. rewrite vdot_0_l; auto. Qed.
    
    (** <a, a> = 0 -> a = 0 *)
    Lemma vdot_same_eq0_imply_eq0 : forall {n} (a : vec n), <a, a> = 0 -> a = vzero.
    Proof.
      intros. unfold vdot,vsum in H. apply veq_iff_vnth; intros.
      apply seqsum_eq0_imply_seq0 with (i:=i) in H; fin.
      - rewrite nth_v2f with (H:=fin2nat_lt _) in H.
        rewrite nat2fin_fin2nat in H. rewrite vnth_vmap2 in H.
        apply field_sqr_eq0_reg in H; auto.
      - intros. rewrite nth_v2f with (H:=H0). rewrite vnth_vmap2. apply sqr_ge0.
    Qed.
    
    (** a <> vzero -> <a, a> <> 0 *)
    Lemma vdot_same_neq0_if_neq0 : forall {n} (a : vec n), a <> vzero -> <a, a> <> 0.
    Proof. intros. intro. apply vdot_same_eq0_imply_eq0 in H0; auto. Qed.
    
    (** <a, a> <> 0 -> a <> vzero *)
    Lemma vdot_same_neq0_imply_neq0 : forall {n} (a : vec n), <a, a> <> 0 -> a <> vzero.
    Proof. intros. intro. apply vdot_same_eq0_if_vzero in H0; auto. Qed.
    
    (** 0 < <a, a> *)
    Lemma vdot_gt0 : forall {n} (a : vec n), a <> vzero -> Azero < (<a, a>).
    Proof.
      intros. apply vdot_same_neq0_if_neq0 in H. pose proof (vdot_ge0 a).
      apply lt_if_le_and_neq; auto.
    Qed.

    (** <a, b>² / (<a, a> * <b, b>) <= 1. *)
    Lemma vdot_sqr_le_form2 : forall {n} (a b : vec n),
        a <> vzero -> b <> vzero -> <a, b>² / (<a, a> * <b, b>) <= 1.
    Proof.
      intros.
      pose proof (vdot_gt0 a H). pose proof (vdot_gt0 b H0).
      pose proof (vdot_sqr_le a b).
      destruct (Aeqdec (<a, b>) 0) as [H4|H4].
      - rewrite H4. ring_simplify. apply le_0_1.
      - apply le_imply_div_le_1 in H3; auto. apply sqr_gt0. auto.
    Qed.

  End OrderedField_Dec.

End vdot.

Section vdot_extra.
  Context `{HSRing : SRing}.
  Infix "*" := Amul : A_scope.
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.
  
  (** < <a,D>, b> = <a, <D,b> > *)
  (* For example:
     (a1,a2,a3) [D11,D12] [b1]  记作 a*D*b，
                [D21,D22] [b2]
                [D31,D32]
     (a*D)*b = <a,col(D,1)> b1 + <a,col(D,2)> b2
             = (a1D11+a2D21+a3D31)b1 + (a1D12+a2D22+a3D32)b2
     a*(D*b) = a1 <row(D,1),b> + a2 <row(D,2),b> + a3 <row(D,3),b>
             = a1(D11b1+D12b2)+a2(D21b1+D22b2)+a3(D31b1+D32b2) *)
  Lemma vdot_assoc :
    forall {r c} (a : @vec tA c) (D : @vec (@vec tA r) c) (b : @vec tA r),
      vdot (fun j => vdot a (fun i => D i j)) b = vdot a (fun i => vdot (D i) b).
  Proof.
    intros. unfold vdot. unfold vmap2.
    pose proof (vsum_vsum c r (fun i j => a.[i] * D.[i].[j] * b.[j])).
    match goal with
    | H: ?a1 = ?a2 |- ?b1 = ?b2 => replace b1 with a2; [replace b2 with a1|]; auto
    end.
    - apply vsum_eq; intros. rewrite vsum_scal_l. apply vsum_eq; intros. sring.
    - apply vsum_eq; intros. rewrite vsum_scal_r. apply vsum_eq; intros. sring.
  Qed.

End vdot_extra.


(* ######################################################################### *)
(** * Geometric operations *)

(* ======================================================================= *)
(** ** Euclidean norm (i.e., L2 norm, length) *)
Section vlen.
  (* Euclidean norm == Euclidean length (distance) = L2 norm == L2 distance *)
  
  Context `{HARing : ARing tA Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Context `{HA2R
      : A2R tA Aadd Azero Aopp Amul Aone Ainv Alt Ale a2r}.

  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "*" := Amul : A_scope.
  (* Notation "a ²" := (a * a) : A_scope. *)
  Notation "1" := Aone : A_scope.
  Notation "| a |" := (Aabs a) : A_scope.
  
  Notation vzero := (@vzero _ Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.

  (** Length (magnitude) of a vector, is derived by inner-product *)
  Definition vlen {n} (a : vec n) : R := R_sqrt.sqrt (a2r (<a, a>)).
  Notation "|| a ||" := (vlen a) : vec_scope.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n:nat}, @vlen n vzero = 0%R.
  Proof. intros. unfold vlen. rewrite vdot_0_l. rewrite a2r_0 at 1. ra. Qed.
  
  Section OrderedARing.
    Context `{HOrderedARing
        : OrderedARing tA Aadd Azero Aopp Amul Aone Alt Ale}.
    Infix "<" := Alt : A_scope.
    Infix "<=" := Ale : A_scope.
    
    (** 0 <= ||a|| *)
    Lemma vlen_ge0 : forall {n} (a : vec n), (0 <= ||a||)%R.
    Proof. intros. unfold vlen. ra. Qed.
    
    (** ||a|| = ||b|| <-> <a, a> = <b, b> *)
    Lemma vlen_eq_iff_dot_eq : forall {n} (a b : vec n), ||a|| = ||b|| <-> <a, a> = <b, b>.
    Proof.
      intros. unfold vlen. split; intros H; try rewrite H; auto.
      apply sqrt_inj in H.
      rewrite a2r_eq_iff in H; auto.
      apply a2r_ge0_iff; apply vdot_ge0.
      apply a2r_ge0_iff; apply vdot_ge0.
    Qed.

    (** <a, a> = ||a||² *)
    Lemma vdot_same : forall {n} (a : vec n), a2r (<a, a>) = (||a||²)%R.
    Proof.
      intros. unfold vlen. rewrite Rsqr_sqrt; auto.
      apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** |a i| <= ||a|| *)
    Lemma vnth_le_vlen : forall {n} (a : vec n) (i : 'I_n),
        a <> vzero -> (a2r (|a i|%A) <= ||a||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      - rewrite <- vdot_same. unfold Rsqr. rewrite <- a2r_mul. apply a2r_le_iff.
        replace (|a i| * |a i|) with (a i * a i). apply vnth_sqr_le_vdot.
        rewrite <- Aabs_mul. rewrite Aabs_right; auto. apply sqr_ge0.
      - apply vlen_ge0.
    Qed.

    (** ||a|| = 1 <-> <a, a> = 1 *)
    Lemma vlen_eq1_iff_vdot1 : forall {n} (a : vec n), ||a|| = 1%R <-> <a, a> = 1.
    Proof.
      intros. unfold vlen. rewrite sqrt_eq1_iff. rewrite a2r_eq1_iff. easy.
    Qed.

    (** ||- a|| = ||a|| *)
    Lemma vlen_vopp : forall n (a : vec n), ||- a|| = ||a||.
    Proof.
      intros. unfold vlen. f_equal. f_equal. rewrite vdot_vopp_l,vdot_vopp_r. ring.
    Qed.

    (** ||x s* a|| = |x| * ||a|| *)
    Lemma vlen_vscal : forall n x (a : vec n), ||x s* a|| = ((a2r (|x|))%A * ||a||)%R.
    Proof.
      intros. unfold vlen.
      rewrite commutative.
      replace (a2r (|x|)%A) with (|(a2r x)|)%R.
      2:{ rewrite a2r_Aabs. auto. }
      rewrite <- sqrt_sqr_abs. rewrite <- sqrt_mult_alt.
      - f_equal. rewrite vdot_vscal_l, vdot_vscal_r, <- associative.
        rewrite a2r_mul. rewrite commutative. f_equal. rewrite a2r_mul. auto.
      - apply a2r_ge0_iff. apply vdot_ge0.
    Qed.

    (** ||a + b||² = ||a||² + ||a||² + 2 * <a, b> *)
    Lemma vlen_sqr_vadd : forall {n} (a b : vec n),
        ||(a + b)||² = (||a||² + ||b||² + 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same. rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite (vdot_comm b a). rewrite !a2r_add. ring.
    Qed.

    (** ||a - b||² = ||a||² + ||b||² - 2 * <a, b> *)
    Lemma vlen_sqr_vsub : forall {n} (a b : vec n),
        ||(a - b)||² = (||a||² + ||b||² - 2 * a2r (<a, b>))%R.
    Proof.
      intros. rewrite <- !vdot_same.
      rewrite !vdot_vadd_l, !vdot_vadd_r.
      rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm b a).
      rewrite !a2r_add, !a2r_opp at 1. ring.
    Qed.

    (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
    (** |<a, b>| <= ||a|| * ||b|| *)
    Lemma vdot_abs_le : forall {n} (a b : vec n), (|a2r (<a, b>)| <= ||a|| * ||b||)%R.
    Proof.
      intros. pose proof (vdot_sqr_le a b).
      apply a2r_le_iff in H. rewrite !a2r_mul in H.
      rewrite (vdot_same a) in H. rewrite (vdot_same b) in H.
      replace (||a||² * ||b||²)%R with ((||a|| * ||b||)²) in H; [| cbv;ring].
      apply Rsqr_le_abs_0 in H.
      replace (|(||a|| * ||b||)|)%R with (||a|| * ||b||)%R in H; auto.
      rewrite !Rabs_right; auto.
      pose proof (vlen_ge0 a). pose proof (vlen_ge0 b). ra.
    Qed.

    (** <a, b> <= ||a|| * ||b|| *)
    Lemma vdot_le_mul_vlen : forall {n} (a b : vec n), (a2r (<a, b>) <= ||a|| * ||b||)%R.
    Proof. intros. pose proof (vdot_abs_le a b). apply Rabs_le_rev in H. ra. Qed.

    (** - ||a|| * ||b|| <= <a, b> *)
    Lemma vdot_ge_mul_vlen_neg : forall {n} (a b : vec n),
        (- (||a|| * ||b||) <= a2r (<a, b>))%R.
    Proof. intros. pose proof (vdot_abs_le a b). apply Rabs_le_rev in H. ra. Qed.

    (* 任意维度“三角形”的任意一边的长度小于等于两边长度之和 *)
    (** ||a + b|| <= ||a|| + ||a|| *)
    Lemma vlen_le_add : forall {n} (a b : vec n), (||(a + b)%V|| <= ||a|| + ||b||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_plus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      rewrite !associative. apply Rmult_le_compat_l; ra.
      pose proof (vdot_abs_le a b). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

    (* 任意维度“三角形”的任意一边的长度大于等于两边长度之差 *)
    (** ||a|| - ||b|| <= ||a + b|| *)
    Lemma vlen_ge_sub : forall {n} (a b : vec n), ((||a|| - ||b||) <= ||(a + b)%V||)%R.
    Proof.
      intros. apply Rsqr_incr_0_var.
      2:{ unfold vlen; ra. }
      rewrite Rsqr_minus. rewrite <- !vdot_same.
      replace (a2r (<a + b, a + b>))
        with (a2r (<a, a>) + a2r (<b, b>) + (2 * a2r (<a, b>)))%R.
      2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
          rewrite (vdot_comm b a). rewrite !a2r_add at 1. ra. }
      apply Rplus_le_compat_l.
      pose proof (vdot_abs_le a b). unfold Rabs in H.
      destruct Rcase_abs; ra.
    Qed.

  End OrderedARing.

  Section OrderedField_Dec.
    Context `{HOrderedField
        : OrderedField tA Aadd Azero Aopp Amul Aone Ainv Alt Ale}.
    Context {AeqDec : Dec (@eq tA)}.
    Infix "<=" := Ale : A_scope.
    
    (** ||a|| = 0 <-> v = 0 *)
    Lemma vlen_eq0_iff_eq0 : forall {n} (a : vec n), ||a|| = 0%R <-> a = vzero.
    Proof.
      intros. unfold vlen. split; intros.
      - apply vdot_same_eq0_imply_eq0. apply sqrt_eq_0 in H; auto.
        apply a2r_eq0_iff; auto. apply a2r_ge0_iff; apply vdot_ge0.
      - rewrite H. rewrite vdot_0_l. rewrite a2r_0 at 1. ra.
    Qed.
    
    (** ||a|| <> 0 <-> a <> 0 *)
    Lemma vlen_neq0_iff_neq0 : forall {n} (a : vec n), ||a|| <> 0%R <-> a <> vzero.
    Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

    (** a <> vzero -> 0 < ||a|| *)
    Lemma vlen_gt0 : forall {n} (a : vec n), a <> vzero -> (0 < ||a||)%R.
    Proof. intros. pose proof (vlen_ge0 a). apply vlen_neq0_iff_neq0 in H; ra. Qed.
    
    (** 0 <= <a, a> *)
    Lemma vdot_same_ge0 : forall {n} (a : vec n), (Azero <= <a, a>)%A.
    Proof.
      intros. destruct (Aeqdec a vzero) as [H|H].
      - subst. rewrite vdot_0_l. apply le_refl.
      - apply le_if_lt. apply vdot_gt0; auto.
    Qed.
    
  End OrderedField_Dec.
  
End vlen.

#[export] Hint Resolve vlen_ge0 : vec.

(* ======================================================================= *)
(** ** Unit vector *)
Section vunit.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "1" := Aone.
  Notation vzero := (vzero Azero).
  Notation vopp := (@vopp _ Aopp).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation "< a , b >" := (vdot a b) : vec_scope.
  
  (** A unit vector `a` is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec. *)
  Definition vunit {n} (a : vec n) : Prop := <a, a> = 1.
  
  (** vunit a <-> vunit (vopp a). *)
  Lemma vopp_vunit : forall {n} (a : vec n), vunit (vopp a) <-> vunit a.
  Proof.
    intros. unfold vunit. rewrite vdot_vopp_l, vdot_vopp_r.
    rewrite group_opp_opp. easy.
  Qed.

  Section Field.
    Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.
    
    (** The unit vector cannot be zero vector *)
    Lemma vunit_neq0 : forall {n} (a : vec n), vunit a -> a <> vzero.
    Proof.
      intros. intro. rewrite H0 in H. unfold vunit in H.
      rewrite vdot_0_l in H. apply field_1_neq_0. easy.
    Qed.
    
  End Field.

  Section A2R.
    Context `{HA2R : A2R tA Aadd Azero Aopp Amul Aone Ainv Alt Ale}.

    Notation vlen := (@vlen _ Aadd Azero Amul a2r).
    Notation "|| a ||" := (vlen a) : vec_scope.

    (** Verify the definition is reasonable *)
    Lemma vunit_spec : forall {n} (a : vec n), vunit a <-> ||a|| = 1%R.
    Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.

    (** vunit a -> || a || = 1 *)
    Lemma vunit_imply_vlen_eq1 : forall {n} (a : vec n), vunit a -> ||a|| = 1%R.
    Proof. intros. apply vunit_spec; auto. Qed.

    (** vunit a -> || a || = 1 *)
    Lemma vlen_eq1_imply_vunit : forall {n} (a : vec n), ||a|| = 1%R -> vunit a.
    Proof. intros. apply vunit_spec; auto. Qed.
    
    Section OrderedARing.
      Context `{HOrderedARing : OrderedARing tA Aadd Azero Aopp Amul Aone Alt Ale}.

      (** vunit a -> <a, a> = 1 *)
      Lemma vunit_vdot : forall {n} (a : vec n), vunit a -> a2r (<a, a>) = 1%R.
      Proof.
        intros. rewrite vdot_same.
        apply vunit_spec in H. rewrite H. ra.
      Qed.

    End OrderedARing.

  End A2R.

(** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : vunit (mat2col a 0) *)
  (* a2 : vunit (mat2col a 1) *)
  (* a3 : vorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : vunit (mat2col b 0) *)
  (* b2 : vunit (mat2col b 1) *)
  (* b3 : vorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* vunit (mat2col (a * b) 0) *)
End vunit.

(* ======================================================================= *)
(** ** Two vectors are orthogonal *)
Section vorth.
  (* Two vectors, u and v, in an inner product space v, are orthogonal (also called 
     perpendicular) if their inner-product is zero. It can be denoted as `u ⟂ v` *)
  
  (* Let's have an Abelian-ring *)
  Context `{HARing : ARing tA Aadd Azero Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  
  Definition vorth {n} (a b : vec n) : Prop := <a, b> = Azero.
  Infix "_|_" := vorth : vec_scope.

  (** a _|_ b -> b _|_ a *)
  Lemma vorth_comm : forall {n} (a b : vec n), a _|_ b -> b _|_ a.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.

  (* If equip a `Dec` and a `Field` *)
  Section Dec_Field.
    Context {AeqDec : Dec (@eq tA)}.
    Context `{HField : Field tA Aadd Azero Aopp Amul Aone Ainv}.
    
    (** (x s* a) _|_ b <-> a _|_ b *)
    Lemma vorth_vscal_l : forall {n} x (a b : vec n),
        x <> Azero -> ((x s* a) _|_ b <-> a _|_ b).
    Proof.
      intros. unfold vorth in *. rewrite vdot_vscal_l. split; intros.
      - apply field_mul_eq0_iff in H0. destruct H0; auto. easy.
      - rewrite H0. ring.
    Qed.
    
    (** a _|_ (x s* b) <-> a _|_ b *)
    Lemma vorth_vscal_r : forall {n} x (a b : vec n),
        x <> Azero -> (a _|_ (x s* b) <-> a _|_ b).
    Proof.
      intros. split; intros.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vscal_l in H0; auto.
      - apply vorth_comm in H0. apply vorth_comm. apply vorth_vscal_l; auto.
    Qed.
  End Dec_Field.
End vorth.

(* ======================================================================= *)
(** ** Projection component of a vector onto another *)
Section vproj.
  (* Let's have an field *)
  Context `{F:Field tA Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vunit := (@vunit _ Aadd Azero Amul Aone).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The projection component of `a` onto `b` *)
  Definition vproj {n} (a b : vec n) : vec n := (<a, b> / <b, b>) s* b.

  (** a _|_ b -> vproj a b = vzero *)
  Lemma vorth_imply_vproj_eq0 : forall {n} (a b : vec n), a _|_ b -> vproj a b = vzero.
  Proof.
    intros. unfold vorth in H. unfold vproj. rewrite H.
    replace (Azero * / (<b, b>)) with Azero. apply vscal_0_l.
    rewrite ring_mul_0_l; auto.
  Qed.

  (** vunit b -> vproj a b = <a, b> s* b *)
  Lemma vproj_vunit : forall {n} (a b : vec n), vunit b -> vproj a b = <a, b> s* b.
  Proof. intros. unfold vproj. f_equal. rewrite H. field. apply field_1_neq_0. Qed.

  (* If equip a `Field` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField tA Aadd Azero Aopp Amul Aone Ainv}.
    
    (** vproj (a + b) c = vproj a c + vproj b c *)
    Lemma vproj_vadd : forall {n} (a b c : vec n),
        c <> vzero -> (vproj (a + b) c = vproj a c + vproj b c)%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vadd_l. rewrite <- vscal_add. f_equal.
      field. apply vdot_same_neq0_if_neq0; auto.
    Qed.
    
    (** vproj (x s* a) b = x s* (vproj a b) *)
    Lemma vproj_vscal : forall {n} (a b : vec n) x,
        b <> vzero -> (vproj (x s* a) b = x s* (vproj a b))%V.
    Proof.
      intros. unfold vproj. rewrite vdot_vscal_l. rewrite vscal_assoc. f_equal.
      field. apply vdot_same_neq0_if_neq0; auto.
    Qed.
    
    (** vproj a a = a *)
    Lemma vproj_same : forall {n} (a : vec n), a <> vzero -> vproj a a = a.
    Proof.
      intros. unfold vproj. replace (<a, a> / <a, a>) with Aone; try field.
      apply vscal_1_l. apply vdot_same_neq0_if_neq0; auto.
    Qed.
  End OrderedField.
End vproj.

(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.
  (* Let's have an field *)
  Context `{F:Field tA Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory F).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).
  Notation vdot := (@vdot _ Aadd Azero Amul).
  Notation vproj := (@vproj _ Aadd Azero Amul Ainv).
  Notation vorth := (@vorth _ Aadd Azero Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Notation "< a , b >" := (vdot a b) : vec_scope.
  Infix "_|_" := vorth : vec_scope.
  
  (** The perpendicular component of `a` respect to `b` *)
  Definition vperp {n} (a b : vec n) : vec n := a - vproj a b.

  (** vperp a b = a - vproj a b *)
  Lemma vperp_eq_minus_vproj : forall {n} (a b : vec n), vperp a b = a - vproj a b.
  Proof. auto. Qed.

  (** vproj a b = a - vperp a b *)
  Lemma vproj_eq_minus_vperp : forall {n} (a b : vec n), vproj a b = a - vperp a b.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (tA := tA) n). agroup.
  Qed.

  (** (vproj a b) + (vperp a b) = a *)
  Lemma vproj_plus_vperp : forall {n} (a b : vec n), vproj a b + vperp a b = a.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (tA := tA) n). agroup.
  Qed.
  
  (** a _|_ b -> vperp a b = a *)
  Lemma vorth_imply_vperp_eq_l : forall {n} (a b : vec n), a _|_ b -> vperp a b = a.
  Proof.
    intros. unfold vperp. pose proof (vadd_AGroup (tA := tA) n). agroup.
    rewrite vorth_imply_vproj_eq0; auto.
  Qed.
  
  (* If equip a `OrderedField` *)
  Section OrderedField.
    Context `{HOrderedField : OrderedField tA Aadd Azero Aopp Amul Aone Ainv}.

    (** (vproj a b) _|_ (vperp a b) *)
    Lemma vorth_vproj_vperp : forall {n} (a b : vec n),
        b <> vzero -> vproj a b _|_ vperp a b.
    Proof.
      intros. unfold vorth, vperp, vproj.
      rewrite !vdot_vscal_l. rewrite vdot_vsub_r. rewrite !vdot_vscal_r.
      rewrite (vdot_comm b a). field_simplify. rewrite ring_mul_0_l; auto.
      apply vdot_same_neq0_if_neq0; auto.
    Qed.
    
    (** vperp (a + b) c = vperp a c + vperp b c *)
    Lemma vperp_vadd : forall {n} (a b c : vec n),
        c <> vzero -> (vperp (a + b) c = vperp a c + vperp b c)%V.
    Proof.
      intros. unfold vperp. pose proof (vadd_AGroup (tA := tA) n). agroup.
      rewrite vproj_vadd; auto. agroup.
    Qed.

    (** vperp (x s* a) b = x s* (vperp a b) *)
    Lemma vperp_vscal : forall {n} (x : tA) (a b : vec n),
        b <> vzero -> (vperp (x s* a) b = x s* (vperp a b))%V.
    Proof.
      intros. unfold vperp. rewrite vproj_vscal; auto. rewrite vscal_vsub. auto.
    Qed.

    (** vperp a a = vzero *)
    Lemma vperp_self : forall {n} (a : vec n), a <> vzero -> vperp a a = vzero.
    Proof.
      intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
    Qed.
  End OrderedField.
  
End vperp.


(* ======================================================================= *)
(** ** Two vectors are collinear, parallel or antiparallel. *)
(* https://en.wikipedia.org/wiki/Euclidean_vector
   Two vectors are parallel if they have the same direction but not
   necessarily the same magnitude, or antiparallel if they have opposite
   direction but not necessarily the same magnitude *)

(* 关于零向量的平行和垂直问题
  1. 来自《高等数学》的理论：
  (1) 零向量的起点和终点重合，它的方向可看做是任意的。
  (2) 如果∠a,b = 0 or π，则称它们平行，记做 a//b。
      当两向量平行时，若将起点放在同一点，则终点和公共起点应在同一条直线，故
      两向量平行也称两向量共线。
  (3) 如果∠a,b = π/2，称它们垂直，记做 a⟂b。
  (4) 由于零向量与另一向量的夹角可以是[0,π]中的任意值，可认为零向量与任何向量
      都平行，也可认为零向量与任何向量都垂直。
  2. 网络上的观点
  (1) There are two choices to handling zero-vector
      a. The mainstream approach is that the zero vector is parallel and
         perpendicular to any vector.
      b. Only consider the non-zero vector, one reason of it is that the 
         transitivity is broken after including zero-vector.
         (因为包含了零向量以后，平行的传递性被破坏了）
  (2) https://www.zhihu.com/question/489006373
      a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
         识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
         零向量的关系上的。
      b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
         的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  3. 使用向量运算的做法
  (1) 使用向量的运算来定义平行和垂直，这样无须三角函数就能判定。
      两向量点乘为零，则它们垂直；两向量叉乘为零向量，则它们平行。
  (2) 在严格证明中，都加上非零向量这一假设条件。
  4. 本文的做法
  (1) 只在非零向量上定义平行、垂直、角度等。换言之，零向量上未定义几何关系。
 *)
Section vcoll_vpara_vapara.

  (* 
     1. we need order relation to distinguish "x > 0 or x < 0" to define parallel
        and antiparallel
     2. we need a coefficent x and 1/x to prove the symmetric of collinear, so we 
        need a field.
     2. we need to prove the reflexivity of collinear, so need a nonzero coefficient
        x, such as use 1 to prove 1 <> 0, thus need a field.
   *)
  Context `{HOrderedField
      : OrderedField tA Aadd Azero Aopp Amul Aone Ainv Alt Ale}.
  Add Field field_inst : (make_field_theory HOrderedField).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + (- b))%A.
  Infix "-" := Asub : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a * (/ b))%A.
  Infix "/" := Adiv : A_scope.

  Notation vzero := (vzero 0).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vscal := (@vscal _ Amul).
  Notation vorth := (@vorth _ Aadd 0 Amul _).
  Infix "+" := vadd : vec_scope.
  Notation "- a" := (vopp a) : vec_scope.
  Notation "a - b" := ((a + -b)%V) : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Infix "_|_" := vorth : vec_scope.


  (** *** Colinear *)
  Section vcoll.
    
    (** Two non-zero vectors are collinear, if the components are proportional *)
    (* Note, x <> 0 could be removed, but it need a prove *)
    Definition vcoll {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : tA, x <> 0 /\ x s* a = b.
    Infix "//" := vcoll : vec_scope.
    
    (** a // a *)
    Lemma vcoll_refl : forall {n} (a : vec n), a <> vzero -> a // a.
    Proof.
      intros. hnf. repeat split; auto. exists 1. split.
      apply field_1_neq_0. apply vscal_1_l.
    Qed.
    
    (** a // b -> b // a *)
    Lemma vcoll_sym : forall {n} (a b : vec n), a // b -> b // a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto.
      apply field_inv_neq0_iff; auto.
      rewrite <- H14. rewrite vscal_assoc. rewrite field_mulInvL; auto.
      apply vscal_1_l.
    Qed.

    (** a // b -> b // c -> a // c *)
    Lemma vcoll_trans : forall {n} (a b c : vec n), a // b -> b // c -> a // c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1).
      split. apply field_mul_neq0_iff; auto.
      rewrite <- H24, <- H14. rewrite vscal_assoc. auto.
    Qed.

    (** a // b => ∃! x, x <> 0 /\ x s* a = b *)
    Lemma vcoll_imply_uniqueX : forall {n} (a b : vec n),
        a // b -> (exists ! x, x <> 0 /\ x s* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vscal_eq_reg_r in H6; auto.
    Qed.

    (** a // b -> (x s* a) // b *)
    Lemma vcoll_vscal_l : forall {n} x (a b : vec n),
        x <> 0 -> a // b -> x s* a // b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vscal_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
      - exists (x1/x); simpl. split.
        apply field_mul_neq0_iff. split; auto. apply field_inv_neq0_iff; auto.
        rewrite <- H4. rewrite vscal_assoc. f_equal. field. auto.
    Qed.

    (** a // b -> a // (x s* b) *)
    Lemma vcoll_vscal_r : forall {n} x (a b : vec n),
        x <> 0 -> a // b -> a // (x s* b).
    Proof.
      intros. apply vcoll_sym in H0. apply vcoll_sym. apply vcoll_vscal_l; auto.
    Qed.
    
  End vcoll.
  

  (** *** Properties about //+ *)
  Section vpara.
    
    (** Two non-zero vectors are parallel, if positive proportional *)
    Definition vpara {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : tA, 0 < x /\ x s* a = b.
    Infix "//+" := vpara : vec_scope.
    
    (** a //+ a *)
    Lemma vpara_refl : forall {n} (a : vec n), a <> vzero -> a //+ a.
    Proof.
      intros. hnf. repeat split; auto. exists 1. split. apply lt_0_1. apply vscal_1_l.
    Qed.
    
    (** a //+ b -> b //+ a *)
    Lemma vpara_sym : forall {n} (a b : vec n), a //+ b -> b //+ a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto. apply inv_gt0; auto.
      rewrite <- H14. rewrite vscal_assoc. rewrite field_mulInvL; auto.
      apply vscal_1_l. symmetry. apply lt_not_eq; auto.
    Qed.

    (** a //+ b -> b //+ c -> a //+ c *)
    Lemma vpara_trans : forall {n} (a b c: vec n), a //+ b -> b //+ c -> a //+ c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1). split. apply mul_gt0_if_gt0_gt0; auto.
      rewrite <- H24, <- H14. rewrite vscal_assoc. auto.
    Qed.

    (** a //+ b => ∃! x, 0 < x /\ x s* a = b *)
    Lemma vpara_imply_uniqueX : forall {n} (a b : vec n),
        a //+ b -> (exists ! x, 0 < x /\ x s* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vscal_eq_reg_r in H6; auto.
    Qed.

    (** a //+ b -> (x s* a) //+ b *)
    Lemma vpara_vscal_l : forall {n} x (a b : vec n),
        0 < x -> a //+ b -> x s* a //+ b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vscal_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
        apply lt_not_eq in H. rewrite H0 in H. easy.
      - exists (x1/x); simpl. split.
        + apply mul_gt0_if_gt0_gt0; auto. apply inv_gt0; auto.
        + rewrite <- H4. rewrite vscal_assoc. f_equal. field.
          symmetry. apply lt_not_eq. auto.
    Qed.

    (** a //+ b -> a //+ (x s* b) *)
    Lemma vpara_vscal_r : forall {n} x (a b : vec n),
        0 < x -> a //+ b -> a //+ (x s* b).
    Proof.
      intros. apply vpara_sym in H0. apply vpara_sym. apply vpara_vscal_l; auto.
    Qed.
    
  End vpara.


  (** *** Properties about //- *)
  Section vapara.
    
    (** Two non-zero vectors are antiparallel, if negative proportional *)
    Definition vapara {n} (a b : vec n) : Prop :=
      a <> vzero /\ b <> vzero /\ exists x : tA, x < 0 /\ x s* a = b.
    Infix "//-" := vapara : vec_scope.
    
    (** a //- a *)
    Lemma vapara_refl : forall {n} (a : vec n), a <> vzero -> a //- a.
    Proof.
      intros. hnf. repeat split; auto. exists (-(1))%A. split.
      apply gt0_iff_neg. apply lt_0_1.
      (* Note that, this is not true *)
    Abort.
    
    (** a //- b -> b //- a *)
    Lemma vapara_sym : forall {n} (a b : vec n), a //- b -> b //- a.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists (/x). split; auto.
      apply inv_lt0; auto.
      rewrite <- H14. rewrite vscal_assoc. rewrite field_mulInvL; auto.
      apply vscal_1_l. apply lt_not_eq; auto.
    Qed.

    (** a //- b -> b //- c -> a //- c *)
    Lemma vapara_trans : forall {n} (a b c: vec n), a //- b -> b //- c -> a //- c.
    Proof.
      intros. hnf in *.
      destruct H as [H11 [H12 [x1 [H13 H14]]]].
      destruct H0 as [H21 [H22 [x2 [H23 H24]]]].
      repeat split; auto. exists (x2 * x1). split.
      2:{ rewrite <- H24, <- H14. rewrite vscal_assoc. auto. }
      (* Note that, this is not true *)
    Abort.

    (** a //- b => ∃! x, x < 0 /\ x s* a = b *)
    Lemma vapara_imply_uniqueX : forall {n} (a b : vec n),
        a //- b -> (exists ! x, x < 0 /\ x s* a = b).
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]]. exists x. split; auto.
      intros j [H5 H6]. rewrite <- H4 in H6.
      apply vscal_eq_reg_r in H6; auto.
    Qed.

    (** a //- b -> (x s* a) //- b *)
    Lemma vapara_vscal_l : forall {n} x (a b : vec n),
        0 < x -> a //- b -> x s* a //- b.
    Proof.
      intros. hnf in *. destruct H0 as [H1 [H2 [x1 [H3 H4]]]].
      repeat split; auto.
      - intro. apply vscal_eq0_imply_x0_or_v0 in H0. destruct H0; auto.
        apply lt_not_eq in H. rewrite H0 in H. easy.
      - exists (x1/x); simpl. split.
        + apply mul_lt0_if_lt0_gt0; auto. apply inv_gt0; auto.
        + rewrite <- H4. rewrite vscal_assoc. f_equal. field.
          symmetry. apply lt_not_eq. auto.
    Qed.

    (** a //- b -> a //- (x s* b) *)
    Lemma vapara_vscal_r : forall {n} x (a b : vec n),
        0 < x -> a //- b -> a //- (x s* b).
    Proof.
      intros. apply vapara_sym in H0. apply vapara_sym.
      apply vapara_vscal_l; auto.
    Qed.
    
  End vapara.
  
  Infix "//" := vcoll : vec_scope.
  Infix "//+" := vpara : vec_scope.
  Infix "//-" := vapara : vec_scope.

  
  (** *** Convert between //, //+, and //-  *)
  Section convert.
    
    (** a //+ b -> a // b *)
    Lemma vpara_imply_vcoll : forall {n} (a b : vec n), a //+ b -> a // b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists x. split; auto. symmetry. apply lt_imply_neq; auto.
    Qed.
    
    (** a //- b -> a // b *)
    Lemma vapara_imply_vcoll : forall {n} (a b : vec n), a //- b -> a // b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. exists x. split; auto. apply lt_imply_neq; auto.
    Qed.
    
    (** a //+ b -> (-a) //- b *)
    Lemma vpara_imply_vapara_opp_l : forall {n} (a b : vec n), a //+ b -> (-a) //- b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. apply group_opp_neq0_iff; auto.
      exists (- x)%A. split. apply gt0_iff_neg; auto.
      rewrite vscal_opp, vscal_vopp, <- H14. rewrite vopp_vopp. auto.
    Qed.
    
    (** a //+ b -> a //- (-b)*)
    Lemma vpara_imply_vapara_opp_r : forall {n} (a b : vec n), a //+ b -> a //- (-b).
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      repeat split; auto. apply group_opp_neq0_iff; auto.
      exists (- x)%A. split. apply gt0_iff_neg; auto.
      rewrite vscal_opp. rewrite H14. auto.
    Qed.
    
    (** a // b -> (a //+ b) \/ (a //- b) *)
    Lemma vcoll_imply_vpara_or_vapara : forall {n} (a b : vec n),
        a // b -> a //+ b \/ a //- b.
    Proof.
      intros. hnf in *. destruct H as [H11 [H12 [x [H13 H14]]]].
      destruct (lt_cases x 0) as [[Hlt|Hgt]|Heq0].
      - right. hnf. repeat split; auto. exists x; auto.
      - left. hnf. repeat split; auto. exists x; auto.
      - easy.
    Qed.
    
  End convert.

  (** *** Extra properties for //, //+, //-  *)
  Section extra_props.

    (* 与两个不共线的向量都垂直的向量是共线的 *)
    Lemma vcoll_if_vorth_both : forall {n} (a b c d : vec n),
        ~(a // b) -> a _|_ c -> b _|_ c -> a _|_ d -> b _|_ d -> c // d.
    Proof.
    Abort.

    Context `{HA2R : A2R _ Aadd 0 Aopp Amul 1 Ainv Alt Ale}.
    Notation vlen := (@vlen _ Aadd 0 Amul a2r _).
    Notation "|| a ||" := (vlen a) : vec_scope.

    (** 两个平行向量 a 和 b 若长度相等，则 a = b *)
    Lemma vpara_vlen_eq_imply : forall {n} (a b : vec n),
        a //+ b -> ||a|| = ||b|| -> a = b.
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]].
      destruct (Aeqdec a vzero), (Aeqdec b vzero); try easy.
      assert (x = 1).
      { rewrite <- H4 in H0. rewrite vlen_vscal in H0.
        symmetry in H0. apply Rmult_eq_r_reg in H0.
        { (* x = 1 *)
          apply a2r_Aabs_eq1 in H0; auto. }
        { (* ||a|| <> 0 *)
          intro. apply vlen_eq0_iff_eq0 in H. easy. } }
      rewrite H in H4. rewrite vscal_1_l in H4; auto.
    Qed.

    (** 两个反平行向量 a 和 b 若长度相等，则 a = - b *)
    Lemma vapara_vlen_eq_imply : forall {n} (a b : vec n),
        a //- b -> ||a|| = ||b|| -> a = -b.
    Proof.
      intros. destruct H as [H1 [H2 [x [H3 H4]]]].
      destruct (Aeqdec a vzero), (Aeqdec b vzero); try easy.
      assert (x = - (1))%A.
      { rewrite <- H4 in H0. rewrite vlen_vscal in H0.
        symmetry in H0. apply Rmult_eq_r_reg in H0; auto.
        { (* x = - 1 *)
          apply a2r_Aabs_eq_n1 in H0; auto. }
        { (* ||a|| <> 0 *)
          intro. apply vlen_eq0_iff_eq0 in H. easy. } }
      rewrite H in H4. rewrite vscal_neg1_l in H4. rewrite <- H4, vopp_vopp. auto.
    Qed.

    (** 两个共线向量 a 和 b 若长度相等，则 a = ± b *)
    Lemma vcoll_vlen_eq_imply : forall {n} (a b : vec n),
        a // b -> ||a|| = ||b|| -> a = b \/ a = -b.
    Proof.
      intros. destruct (vcoll_imply_vpara_or_vapara a b H).
      - left. apply vpara_vlen_eq_imply; auto.
      - right. apply vapara_vlen_eq_imply; auto.
    Qed.
    
  End extra_props.

End vcoll_vpara_vapara.
