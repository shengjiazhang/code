(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Basic configuration (Libraries, Notations, Warning, etc.)
  author    : Zhengpu Shi
  date      : 2022.06
  
  remark    :
  0. Naming style
     tA,tB,tC  --- type
     M,N,O  --- matrix
     u,v,w  --- vector
     a,b,c,k  -- scalar

  1. Basic libraries in whole project
  3. Reserved notations for consistence.
     https://coq.inria.fr/distrib/V8.13.2/refman/language/coq-library.html 
  3. Eliminate some warning.  
     https://coq.inria.fr/distrib/V8.13.2/refman/user-extensions/
     syntax-extensions.html?highlight=warning
  4. Customized tactics.
*)


(* ######################################################################### *)
(** * Basic libraries *) 

Require Export Coq.Setoids.Setoid.        (*  *)
Require Export Coq.Classes.Morphisms.     (* respectful, ==> *)
Require Export Coq.Classes.SetoidTactics. (* add_morphism_tactic *)
Require Export Coq.Relations.Relations.   (* equivalence *)
Require Export Coq.Bool.Sumbool.          (* sumbool_not *)
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import FinMatrix.CoqExt.MyExtrOCamlR.
Require Export FinMatrix.CoqExt.LogicExt.
Require Export FinMatrix.CoqExt.BoolExt.
Require Export FinMatrix.CoqExt.StrExt.
Require Export List.
Require Export Ring Field.



(* ######################################################################### *)
(** * Reserved Notations *)

(* Reserved Notations, to keep same precedence and associativity *)

(* ======================================================================= *)
(* The precedence ∈ [60,100) are logic operations *)

(* These are truely boolean value, but not friendly for "computation". 
   That means, the computation result is a complex expression instead of a value *)
Reserved Infix    "=?"     (at level 70).           (* bool compare for "=" *)
Reserved Infix    "<?"     (at level 70).           (* bool compare for "<" *)
Reserved Infix    ">?"     (at level 70).           (* bool compare for ">" *)
Reserved Infix    "<=?"    (at level 70).           (* bool compare for "<=" *)
Reserved Infix    ">=?"    (at level 70).           (* bool compare for ">=" *)

(* The decidable procedure is friendly for "computation", and also could obtain a 
   proof for this property. But not a truely boolean value *)
Reserved Infix    "??="    (at level 70).           (* decidable procedure for "=" *)
Reserved Infix    "??<"    (at level 70).           (* decidable procedure for "<" *)
Reserved Infix    "??>"    (at level 70).           (* decidable procedure for ">" *)
Reserved Infix    "??<="   (at level 70).           (* decidable procedure for "<=" *)
Reserved Infix    "??>="   (at level 70).           (* decidable procedure for ">=" *)

(* Reserved Infix    "=="      (at level 70, no associativity).      (* equiv *) *)
(* Reserved Notation "a != b"  (at level 70, no associativity).      (* not equiv *) *)

(* ======================================================================= *)
(* The precedence ∈ [30,60) are vector/matrix operations *)
Reserved Infix    "+"       (at level 50, left associativity).   (* add *)
Reserved Infix    "-"       (at level 50, left associativity).   (* sub *)
Reserved Infix    "*"       (at level 40, left associativity).   (* mul *)
Reserved Infix    "/"       (at level 40, left associativity).   (* div *)
Reserved Notation "a ²"     (at level 1).                        (* sqr *)
Reserved Infix    "s*"     (at level 40, left associativity).    (* scal left mul *)
Reserved Infix    "*s"     (at level 38, right associativity).   (* scal right mul *)
Reserved Infix    "*v"      (at level 30, right associativity).  (* mat * vec *)
Reserved Infix    "v*"      (at level 28, left associativity).   (* vec * mat *)
Reserved Infix    "⦿"      (at level 40, left associativity).   (* hardmard prod *)
Reserved Infix    "\o"      (at level 50, no associativity).
Reserved Notation "< a , b >" (at level 60, a, b at level 55, format "< a , b >"). (* dot prod *)
Reserved Notation "|| v ||"   (at level 60, v at level 45, format "|| v ||").  (* vlen *)
Reserved Infix    "\x"      (at level 40, no associativity).     (* cross prod *)
Reserved Infix    "∘"       (at level 40, left associativity).   (* compose *)
Reserved Notation "- a"     (at level 35, right associativity).  (* opp *)
Reserved Notation "/ a"     (at level 35, right associativity).  (* inv *)
Reserved Notation "M \T"    (at level 32, left associativity, format "M \T"). (* transpose *)
Reserved Notation "M \A"    (at level 15, left associativity, format "M \A"). (* adjoin matrix *)
Reserved Notation "M \-1"   (at level 20, format "M \-1").        (* minv *)
Reserved Notation "M @ N"   (at level 30, no associativity).      (* cons by col *)
Reserved Notation "'tr' M"  (at level 33, no associativity).

Reserved Notation "'\sum' f" (at level 10).      (* sum of a vector *)
Reserved Notation "'\prod' f" (at level 10).     (* product of a vector *)

Reserved Infix "/_"         (at level 60).       (* angle of two vectors *)
Reserved Infix "/2_"        (at level 60).       (* angle of two vectors in 2D *)

Reserved Infix "_|_"        (at level 50).       (* Two vectors are orthogonal *)
Reserved Infix "//"         (at level 50).       (* Two vectors are collinear *)
Reserved Infix "//+"        (at level 50).       (* Two vectors are parallel *)
Reserved Infix "//-"        (at level 50).       (* Two vectors are antiparallel *)

Reserved Infix "+f"         (at level 50, left associativity).    (* fadd *)
Reserved Infix "-f"         (at level 50, left associativity).    (* fsub *)
Reserved Infix "*f"         (at level 40, left associativity).    (* fmul *)
Reserved Infix "/f"         (at level 40, left associativity).    (* fdiv *)
Reserved Notation "-f g"    (at level 35, right associativity).   (* fopp *)
Reserved Notation "/f g"    (at level 35, right associativity).   (* finv *)


(* ======================================================================= *)
(* The precedence ∈ [1,30) are element operations *)

Reserved Notation "| r |"   (at level 30, r at level 25, format "| r |").  (* Rabs *)

(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)

(* Get element of a nat-function by index *)
(* Reserved Notation "f ! i" *)
(*   (at level 25, i at next level, format "f ! i" ). *)
(* Reserved Notation "f ! i ! j" *)
(*   (at level 25, i, j at next level, format "f ! i ! j" ). *)

(* Get element of vector/matrix by index. *)

(* keep same with "mathcomp/ssrreflect/ssrnotation.v"  *)
Reserved Notation "v .[ i ]"
  (* (at level 2, i at next level, left associativity, format "v .[ i ]"). *)
  (at level 2, left associativity, format "v .[ i ]").
(* Reserved Notation "v .[ i <- a ]" *)
(*   (at level 2, i at next level, left associativity, format "v .[ i <- a ]"). *)
Reserved Notation "M &[ i ]"
  (at level 2, left associativity, format "M &[ i ]").
  (* (at level 2, i at next level, left associativity, format "M &[ i ]"). *)


(* Get element of finite vector/matrix by index.
   Note, there are two style of start number to count index, 0 or 1.
   Many programming language use 0, but MATLAB and many mathematical textbook use 1.
   Maybe it is a convention problem, we choose 1. *)

(* keep same with "p .1" in Coq/ssr/ssrfun.v *)
Reserved Notation "V .1"       (at level 2, left associativity, format "V .1"). (* v[1] *)
Reserved Notation "V .2"       (at level 2, left associativity, format "V .2").
Reserved Notation "V .3"       (at level 2, left associativity, format "V .3").
Reserved Notation "V .4"       (at level 2, left associativity, format "V .4").

(* For 2-/3-/4-D vector *)
(* Reserved Notation "V .x"       (at level 25, format "V .x").      (* v[1] *) *)
(* Reserved Notation "V .y"       (at level 25, format "V .y"). *)
(* Reserved Notation "V .z"       (at level 25, format "V .z"). *)
(* the "w" component has two conventions, we won't use it *)
(* Reserved Notation "V .w"       (at level 25, format "V .w"). *)

(* Note, the above notations are convenients and friendly, but there has a problem:
   If we have module and any identifier is "x/y/z", then an error will occur 
   when accessing this identifier. For example:
   << 
Module A.
  Definition x := 1.
End A.
Check A.x.
   >>
   Thus, we disabled the global reservation. Instead, we use then locally. *)

Reserved Notation "M .11"      (at level 25, format "M .11").     (* m[1,1] *)
Reserved Notation "M .12"      (at level 25, format "M .12").
Reserved Notation "M .13"      (at level 25, format "M .13").
Reserved Notation "M .14"      (at level 25, format "M .14").
Reserved Notation "M .21"      (at level 25, format "M .21").
Reserved Notation "M .22"      (at level 25, format "M .22").
Reserved Notation "M .23"      (at level 25, format "M .23").
Reserved Notation "M .24"      (at level 25, format "M .24").
Reserved Notation "M .31"      (at level 25, format "M .31").
Reserved Notation "M .32"      (at level 25, format "M .32").
Reserved Notation "M .33"      (at level 25, format "M .33").
Reserved Notation "M .34"      (at level 25, format "M .34").
Reserved Notation "M .41"      (at level 25, format "M .41").
Reserved Notation "M .42"      (at level 25, format "M .42").
Reserved Notation "M .43"      (at level 25, format "M .43").
Reserved Notation "M .44"      (at level 25, format "M .44").

Reserved Notation "M &1"       (at level 25, format "M &1").      (* mcol M 1 *)
Reserved Notation "M &2"       (at level 25, format "M &2").
Reserved Notation "M &3"       (at level 25, format "M &3").
Reserved Notation "M &4"       (at level 25, format "M &4").

(* this level is consistent with coq.ssr.ssrbool.v *)
(* Notation "~~ b" := (negb b) (at level 35, right associativity) : bool_scope. *)

(* fix Bellet behavior, caused by Mathcomp.ssreflect.ssreflect.v *)
#[export] Set Bullet Behavior "Strict Subproofs".


(* ######################################################################### *)
(** * Eliminate Warning. *)

(* Export Set Warnings "-notation-overridden". *)


(* ######################################################################### *)
(** * Customized tactics *)

(* copy a hypothesis *)
Ltac copy H :=
  let HC := fresh "HC" in
  let HCeq := fresh "HCeq" in
  remember H as HC eqn: HCeq;
  clear HCeq.

(* simplify the equality of two list *)
Ltac list_eq :=
  repeat match goal with
    | |- cons ?h1 ?t1 = cons ?h2 ?t2 => f_equal
    | [H: cons _ _ = cons _ _ |- _] => inversion H; clear H
    end.

(* repeat split *)
Ltac ssplit := 
  repeat 
  match goal with
  | |- _ /\ _ => split
  end.

(** inversion and subst *)
Ltac inv H := inversion H; clear H; subst.

(** first step of the proof of Proper *)
Ltac simp_proper :=
  unfold Proper; unfold respectful.

(** destruct by sumbool comparison procedure. Note that we should register 
    the reflect reflection to "bdestruct" database first. *)

(* (* original version, which has additional support for natural number *) *)
(* Ltac bdestruct X := *)
(*   let H := fresh in let e := fresh "e" in *)
(*    evar (e: Prop); *)
(*    assert (H: reflect e X); subst e; *)
(*     [eauto with bdestruct *)
(*     | destruct H as [H|H]; *)
(*       [ | try first [apply not_lt in H | apply not_le in H]]]. *)

(* modified version, support any data type which registered a reflection relation *)
#[global] Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [ try eauto with bdestruct
  | destruct H as [H|H]].


(** simplify the logic expressions *)
Ltac logic :=
  repeat
    (match goal with
     (* solve it *)
     | [H : ?P |- ?P] => exact H
     | [|- True] => constructor
     | [H : False |- _] => destruct H

     (* simplify it *)
     | [|- _ /\ _ ] => constructor
     | [|- _ -> _] => intro
     (* | [|- not _ ] => intro *)
     | [|- _ <-> _ ] => split; intros
     | [H : _ /\ _ |- _] => destruct H
     | [H : _ \/ _ |- _] => destruct H

     (* rewriting *)
     (* | [H1 : ?P -> ?Q, H2 : ?P |- _] => pose proof (H1 H2) *)
     (* | [H : ?a = ?b |- _ ]  => try progress (rewrite H) *)
     | [H : ?a <> ?b |- False]   => destruct H
     end;
     try congruence).

(** Solve simple logic about "bool" *)
Ltac autoBool :=
  repeat
    let H := fresh "H" in 
    match goal with
    (* b = false <-> b <> true *)
    | |- ?b = false <-> ?b <> true => split
    (* b = true <-> b <> false *)
    | |- ?b = false <-> ?b <> true => split
    (* b = false -> b <> true *)
    | H: ?b = false |- ?b <> true => rewrite H
    (* b <> true -> b = false *)
    | H: ?b <> true |- ?b = false => apply not_true_is_false
    (* a && b = true |- _ ==> a = true, b = true |- _ *)
    | H: ?a && ?b = true |- _ => apply andb_prop in H
    end;
    logic.


(* ######################################################################### *)
(** * Repeat executing an unary function *)

(** execute an unary function multiply times with the initial value. 
    Similiar to fold.
    nexec a0 f n := f (f ... (f x) ...) *)
Fixpoint nexec {A:Type} (a0:A) (f:A->A) (n:nat) : A :=
  match n with
  | O => a0
  | S n' => nexec (f a0) f n'
  end.

(* Compute nexec 0 S 3. *)

(** nexec rewriting *)
Lemma nexec_rw : forall (A:Type) (a:A) (f:A->A) (n:nat),
  nexec (f a) f n = f (nexec a f n).
Proof.
  intros. revert a. induction n; intros; simpl; auto. 
Qed.

(** Linear property of nexec *)
Lemma nexec_linear : forall (A:Type) (a:A) (f:A->A) (g:A->A) (n:nat)
  (H: forall x:A, f (g x) = g (f x)),
  nexec (g a) f n = g (nexec a f n).
Proof.
  intros. revert a. induction n; intros; simpl; auto. rewrite H,IHn. auto.
Qed.

(** map f (seq 0 (S n)) = map f (seq 0 n) + f n
    So, a0 + f 0 + f 1 + ... + f n = (a0 + f 0 + ... + f (n-1)) + f n *)
Lemma fold_map_seq : forall (A:Type) (f:nat->A) (g:A->A->A) (a0:A) (n:nat),
  fold_left g (map f (seq 0 (S n))) a0 = g (fold_left g (map f (seq 0 n)) a0) (f n).
Proof.
  intros.
  rewrite seq_S.  (* seq start (S len) = (seq start len ++ [(start + len)]) *)
  rewrite map_app. (* map f (l ++ l') = (map f l ++ map f l') *)
  rewrite fold_left_app. (* 
    fold_left f (l ++ l') i = fold_left f l' (fold_left f l i) *)
  simpl. auto.
Qed.


(* ######################################################################### *)
(** * Extension for option type *)

(** Convert option type to base type  *)
Definition option_get {tA} (o : option tA) (def : tA) : tA :=
  match o with
  | Some a => a
  | _ => def
  end.


(* ######################################################################### *)
(** * Extension for sig type *)

(* (** projection for sig *) *)
Notation "x '.val'" := (proj1_sig x) (at level 1, format "x '.val'").
Notation "x '.prf'" := (proj2_sig x) (at level 1, format "x '.prf'").

(** {a | P a} = {b | P b} <-> a = b *)
Lemma sig_eq_iff : forall {tA} {P : tA -> Prop} a b (Ha : P a) (Hb : P b),
    (exist _ a Ha = exist _ b Hb) <-> a = b.
Proof.
  intros. split; intros.
  - inversion H. auto.
  - subst. f_equal. apply proof_irrelevance.
Qed.

(** {a | P a}.val = a *)
Lemma sig_val : forall {tA} {P : tA -> Prop} a (Ha : P a), (exist _ a Ha).val = a.
Proof. intros. simpl. auto. Qed.

(** {a.val | P (a.val)} = a *)
Lemma val_sig_eq : forall {tA} {P : tA -> Prop} (a : {x | P x}) (H : P (a.val)),
    exist _ (a.val) H = a.
Proof. intros. destruct a. simpl. apply sig_eq_iff; auto. Qed.


(* ######################################################################### *)
(** * Usually used scopes *)

(** Scope for element type of matrix/vector/list *)
Declare Scope A_scope.
Delimit Scope A_scope with A.
Open Scope A.

(** Scope for vector type *)
Declare Scope vec_scope.
Delimit Scope vec_scope with V.
Open Scope vec_scope.

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with M.
Open Scope mat_scope.
