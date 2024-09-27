From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
  -
    rewrite Hs_eq.
    split.
    +
      reflexivity.
    +
      reflexivity.
  -
    split.
    +
      intros H_ctro.
      discriminate H_ctro.
    +
      intros H.
      rewrite H in Hs_not_eq.
      destruct Hs_not_eq.
      reflexivity.
Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.

 
Compute examplemap "foo".
(*      = true
     : bool *)
Compute examplemap "bar".
(*      = true
     : bool *)
Compute examplemap "jiajia".
(*      = false
     : bool *)

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  unfold eqb_string. 
  destruct (string_dec x x) as [H | H'].
  -
    reflexivity.
  -
    contradiction H'.
    reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  unfold eqb_string.
  destruct (string_dec x1 x2) as [H' | H''].
  -
    contradiction H'.
  -
    reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).











