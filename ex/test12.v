From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
(* Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) =>
    match H1 with
    | conj HP HQ =>
      match H2 with
      | conj HQ' HR => conj HP HR
      end
    end.

(* Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q. *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl HP => or_intror HP
    | or_intror HQ => or_introl HQ
    end.

(* Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P. *)

Inductive ev : nat -> Prop :=
  | ev_O : ev O
  | ev_SS : forall n , ev n -> ev (S (S n)).

Theorem test : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_O.
Qed.


Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
    ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_O).
  
(* Inductive True : Prop :=
  | I : True.

Inductive False : Prop := . *)

Module MyEquality.
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
  intros.
(* H : x == y *)
  induction H.
  apply H0.
Qed.























