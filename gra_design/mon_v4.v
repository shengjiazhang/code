From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.

Parameter time : nat.
Parameter len : nat.

Inductive level : Type :=
  | Hi
  | Lo.

Definition eqb_string (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Definition total_map (A : Type) := string -> A.

Definition bus_value := list level.
Definition bus := nat -> bus_value.

Definition state := total_map bus.

Definition null : bus := fun _ => [].

Definition t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity) : mon_scope.

Open Scope mon_scope.

Definition empty_st := (_ !-> null).

Notation "x '!->' v" := (t_update empty_st x v) (at level 100) : mon_scope.

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity) : mon_scope.

Definition Not l : level :=
  match l with
  | Hi => Lo
  | Lo => Hi
  end.

Definition And (l1 l2 : level) : level :=
  match l1 with
  | Hi => l2
  | Lo => Lo
  end.

Definition Or (l1 l2 : level) : level :=
  match l1 with
  | Hi => Hi
  | Lo => l2
  end.

Definition Xor (l1 l2 : level) : level :=
  match l1 with
  | Hi => Not l2
  | Lo => l2
  end.

Definition equal (l1 l2 : level) : level :=
  match l1, l2 with
  | Hi, Hi | Lo, Lo => Hi
  | _, _ => Lo
  end.

Fixpoint reverse (l : bus_value) : bus_value :=
  match l with 
  | [] => []
  | h :: t => reverse t ++ [ h ]
  end.

Fixpoint length (l : bus_value) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint pad' (l : bus_value) (size : nat) : bus_value :=
  match size with
  |O => l
  |S n => match l with
          | nil => Lo :: pad' nil n
          | h::t => pad' t n ++ [ h ]
          end
  end.
Definition pad (l : bus_value) (size : nat) : bus_value :=
  pad' (reverse l) size.

Definition strcut (l : bus_value) (left right : nat) : bus_value :=
  firstn (left - right + 1) 
  (skipn ((length (pad l (left + 1))) - left - 1) (pad l (left + 1))).

(* Compute ([Hi;Hi;Lo] 【4 ： 0】).
(*      = [Lo; Lo; Hi; Hi; Lo]
     : bus_value *)
Compute ([Hi;Hi;Lo] 【2 ： 0】).
(*      = [Hi; Hi; Lo]
     : bus_value *)
Compute ([Hi;Hi;Lo] 【1 ： 0】).
(*      = [Hi; Lo]
     : bus_value *) *)

(* 与运算 *)
Fixpoint BAnd (l1 l2 : bus_value) : bus_value :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | b1 :: rest1, b2 :: rest2 => (And b1 b2) :: (BAnd rest1 rest2)
  end.

(* 非运算 *)
Fixpoint BNot (l : bus_value) : bus_value :=
  match l with
  | [] => []
  | b :: rest => Not b :: BNot rest
  end.

(* 或运算 *)
Fixpoint BOr (l1 l2 : bus_value) : bus_value :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | b1 :: rest1, b2 :: rest2 => (Or b1 b2) :: (BOr rest1 rest2)
  end.

(* 异或运算 *)
Fixpoint BXor (l1 l2 : bus_value) : bus_value :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | b1 :: rest1, b2 :: rest2 => Xor b1 b2 :: (BXor rest1 rest2)
  end.

(* 一位全加器 *)
Definition full_adder (a b cin : level) : level * level :=
  let sum := Xor a (Xor b cin) in
  let cout := Or (And a cin) (Or (And a b) (And b cin)) in
  (sum, cout).

(* 需要保证等位长 *)
Fixpoint BPlus' (xs ys : bus_value) (cin : level) : (bus_value) * level :=
  match xs, ys with
  | [], [] => ([], cin)
  | x::xt, y::yt =>
      let (sum, cout) := full_adder x y cin in
      let (rest, carry) := BPlus' xt yt cout in
      (sum::rest, carry)
  | _, [] => (xs, cin)
  | [], _ => (ys, cin)
  end.
Definition trans (res : bus_value * level) : bus_value := 
  match res with
  |(nil , _)=> nil
  |(l , Hi) => [ Hi ] ++ (reverse l)
  |(l , Lo) => reverse l 
  end.
(* 进位加法器 *)
Definition BPlus (l1 l2 : bus_value) (cin : level) : bus_value :=
  trans (BPlus' (reverse l1) (reverse l2 ) cin).

Fixpoint shift (l : bus_value) (n : nat) : bus_value :=
  match n with 
  | O => l
  | S n' => match l with 
            | nil => nil
            | h :: t => shift t n'
            end
  end.
(* 右移位 *)
Definition r_shift (l : bus_value) (n : nat) : bus_value :=
  reverse (shift (reverse l) n). 
(* 左移位 *)
Definition l_shift (l : bus_value) (n : nat) : bus_value :=
  shift l n.

(* 把bool列表转化为nat，空列表则设为缺省值0 *)
Fixpoint b_to_nat' (l : bus_value) : nat :=
  match l with
  |nil => O
  |[ Hi ]=> 1
  |h::t=>match h with
        |Hi => S (2 * (b_to_nat' t))
        |Lo => 2 * (b_to_nat' t)
        end
  end.
Definition b_to_nat (l : bus_value) : nat :=
  b_to_nat' (reverse l).
Fixpoint index_At (l : bus_value) (n : nat) : bus_value :=
  match l with
  |nil => [ Lo ]
  |h :: tl => match n with
              |O => [ h ]
              |S n' => index_At tl n'
              end
   end.
(* 取一位 *)
Definition Index_At (l : bus_value) (cnt : bus_value) : bus_value :=
  index_At (reverse l) (b_to_nat cnt).

(* 判等 *)
Fixpoint Equal (b1 b2 : bus_value) : bool :=
  match b1, b2 with
  | [], [] => true
  | _ , [] => false
  | [], _ => false
  | h1 :: tl1, h2 :: tl2 => 
    match h1, h2 with
    | Hi, Hi => Equal tl1 tl2
    | Lo, Lo => Equal tl1 tl2
    | _, _ => false
    end
  end.
Definition Equal' (b1 b2 : bus_value) : bus_value :=
  if Equal b1 b2 then [Hi] else [Lo].

(* 自增 *)
Fixpoint incr (l : bus_value) : bus_value :=
  match l with
  | [] => []
  | [ Lo ] => [ Hi ]
  | [ Hi ] => [Lo; Hi]
  | h :: tl => match h with
               | Lo => [ Hi ] ++ tl
               | Hi => [ Lo ] ++ (incr tl)
               end
  end.
Definition Incr (l : bus_value) : bus_value :=
  reverse (incr (reverse l)).

(* 连接两个bus_value *)
Definition combine (l1 l2 : bus_value) : bus_value :=
  l1 ++ l2.

Inductive expr : Type :=
  | econv (b : bus_value)
  | econb (b : bus)
  | Reg (e : expr) (l : nat)
  | EId (x : string)
  | Expr_And (a1 a2 : expr)
  | Expr_Not (a : expr)
  | Expr_Or (a1 a2 : expr)
  | Expr_Xor (a1 a2 : expr)
  | Expr_Plus (a1 a2 : expr)
  | Expr_r_shift (a: expr) (n : nat)
  | Expr_l_shift (a : expr) (n : nat)
  | Expr_Index_At (a : expr) (n : expr)
  | Expr_Incr (a : expr)
  | Expr_Equal (a1 a2 : expr)
  | Expr_Combine (a1 a2 : expr)
  | Expr_Strcut (a : expr) (r l : nat).

Coercion econv : bus_value >-> expr.
Coercion econb : bus >-> expr.
Coercion EId : string >-> expr.
Bind Scope mon_scope with expr.
Notation "x '&&' y" := (Expr_And x y) (at level 40, left associativity) : mon_scope.
Notation "x '||' y" := (Expr_Or x y) (at level 50, left associativity) : mon_scope.
Notation "x '^' y" := (Expr_Xor x y) (at level 30, right associativity) : mon_scope.
Notation "'!' x" := (Expr_Not x) (at level 75, right associativity) : mon_scope.
Notation "x '+' y" := (Expr_Plus x y) (at level 50, left associativity) : mon_scope.
Notation "x '<<' n" := (Expr_l_shift x n) (at level 30, right associativity) : mon_scope.
Notation "x '>>' n" := (Expr_r_shift x n) (at level 30, right associativity) : mon_scope.
Notation "x 'at' n" := (Expr_Index_At x n) (at level 30, right associativity) : mon_scope.
Notation "x '==' y" := (Expr_Equal x y) (at level 70, no associativity) : mon_scope.
Notation "x '++'" := (Expr_Incr x) (at level 50, left associativity) : mon_scope.
Notation "'{' x ',' y '}'" := (Expr_Combine x y) : mon_scope.
Notation "a '【' r '：' l '】'" := (Expr_Strcut a r l) 
(at level 50, left associativity) : mon_scope.

Fixpoint Eval_expr (st : state) (e : expr) : bus :=
  match e with
  | econv b => fun time => b
  | econb b => b
  | Reg e l => fun time => strcut ((Eval_expr st e) time) (l - 1) 0
  | EId x => st x
  | Expr_And a1 a2 => fun time  => BAnd ((Eval_expr st a1) time) ((Eval_expr st a2) time)
  | Expr_Not a => fun time => BNot ((Eval_expr st a) time)
  | Expr_Or a1 a2 => fun time => BOr ((Eval_expr st a1) time) ((Eval_expr st a2) time)
  | Expr_Xor a1 a2 => fun time => BXor ((Eval_expr st a1) time) ((Eval_expr st a2) time)
  | Expr_Plus a1 a2 => fun time => BPlus ((Eval_expr st a1) time) ((Eval_expr st a2) time) Lo
  | Expr_r_shift a n => fun time => r_shift ((Eval_expr st a) time) n
  | Expr_l_shift a n => fun time => l_shift ((Eval_expr st a) time) n
  | Expr_Index_At a n => fun time => Index_At ((Eval_expr st a) time) ((Eval_expr st n) time)
  | Expr_Incr a => fun time => Incr ((Eval_expr st a) time)
  | Expr_Equal a1 a2 => fun time => Equal' ((Eval_expr st a1) time) ((Eval_expr st a2) time)
  | Expr_Combine a1 a2 => fun time => combine ((Eval_expr st a1) time) ((Eval_expr st a2) time)
  | Expr_Strcut a r l => fun time => strcut ((Eval_expr st a) time) r l
end.

Definition list : bus := fun time => [Hi; Hi; Lo; Hi].
Definition list' : bus := fun time => [Hi; Lo; Hi; Hi].
Definition Null : bus := fun time => [].

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition two : bus_value := [Hi; Lo].
Definition zero : bus_value := [Lo].

Compute Eval_expr (X !-> list) (X >> 1).
(*       = fun _ : nat => [Hi; Hi; Lo]
      : nat -> bus_value  *)
Compute Eval_expr (X !-> list; Y !->list') (X + Y).
(*       = fun _ : nat => [Hi; Hi; Lo; Lo; Lo]
     : nat -> bus_value  *)
Compute Eval_expr (X !-> list) (X at two).
(*       = fun _ : nat => [Hi]
     : nat -> bus_value *)
Compute Eval_expr (X !-> list) (X ++).
(*      = fun _ : nat => [Hi; Hi; Hi; Lo]
     : bus *)
Compute Eval_expr (X !-> list; Y !->list') (X == Y).
(*      = fun _ : nat => [Lo]
     : bus *)
Compute Eval_expr (X !-> list; Y !-> list') ({X , Y}).
(*      = [Hi; Hi; Lo; Hi; Hi; Lo; Hi; Hi]
     : bus_value *)
Compute Eval_expr (X !-> list) (! X).
(*      = [Lo; Lo; Hi; Lo]
     : bus_value *)
Compute Eval_expr (X !-> list) (X 【3 ：0】).
(*      = fun _ : nat => [Hi; Lo; Hi]
     : bus *)
Compute Eval_expr (X !-> Null) (Reg X 3).
(*      = fun _ : nat => [Lo; Lo; Lo]
     : bus *)

Inductive com : Type :=
  | Skip
  | Assign (x : string) (a : expr)
  | Seq (c1 c2 : com)
  | If (b : expr) (c1 c2 : com)
  | If'(b : expr) (c : com)
  | While (b : expr) (c : com).

Bind Scope mon_scope with expr.
Notation "'SKIP'" := Skip : mon_scope.
Notation "x '::=' a" := (Assign x a) (at level 60) : mon_scope.
Notation "c1 ;; c2" := (Seq c1 c2) (at level 80, right associativity) : mon_scope.
Notation "'WHILE' b 'DO' c 'END'" := (While b c) 
  (at level 80, right associativity) : mon_scope.
Notation "'IF' c1 'THEN' c2 'ELSE' c3 'FI'" := (If c1 c2 c3) 
  (at level 80, right associativity) : mon_scope.
Notation "'If' c1 'THEN' c2 'fI'" := (If' c1 c2)
  (at level 80, right associativity) : mon_scope.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x, 
            Eval_expr st a1 = n ->
            st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
            st =[ c1 ]=> st' ->
            st' =[ c2 ]=> st'' ->
            st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2, 
            Eval_expr st b = (fun _ => [Hi]) ->
            st =[ c1 ]=> st' ->
            st =[ IF b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2, 
            Eval_expr st b = (fun _ => [Lo]) ->
            st =[ c2 ]=> st' ->
            st =[ IF b THEN c1 ELSE c2 FI ]=> st'
  | E_ifTrue : forall st st' b c,
            Eval_expr st b = (fun _ => [Hi]) ->
            st =[ c ]=> st' ->
            st =[ If b THEN c fI ]=> st'
  | E_ifFalse : forall st b c,
            Eval_expr st b = (fun _ => [Lo]) ->
            st =[ If b THEN c fI]=> st
  | E_WhileFalse : forall b st c,
            Eval_expr st b = (fun _ => [Lo]) ->
            st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
            Eval_expr st b = (fun _ => [Hi]) ->
            st =[ c ]=> st' ->
            st' =[ WHILE b DO c END ]=> st'' ->
            st =[ WHILE b DO c END ]=> st''
  
  where "st =[ c ]=> st'" := (ceval c st st').




Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
Definition Aexp : Type := state -> bus.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_bus (b : bus) : Aexp := fun _ => b.
Definition Aexp_of_expr (a : expr) : Aexp := fun st => Eval_expr st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_bus : bus >-> Aexp.
Coercion Aexp_of_expr : expr >-> Aexp.
Arguments assert_of_Prop /.
Arguments Aexp_of_bus /.
Arguments Aexp_of_expr /.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) 
(at level 90, c at next level)
  : hoare_spec_scope.

(* 肯后 *)
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' H1 H2.
  apply H.
Qed.

(* 否前 *)
Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' H1 H2.
  unfold not in H.
  apply H in H2.
  inversion H2.
Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> Eval_expr st a ; st).
Notation "P [[ X |-> a ]]" := (assn_sub X a P)
  (at level 10, X at next level).

(* 赋值 *)
Theorem hoare_asgn : forall Q X a,
  {{Q [[X |-> a]]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' H H1.
  inversion H. subst.
  unfold assn_sub in H1. assumption.
Qed.

(* 增强前条件 *)
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. 
  apply (Hhoare st st').
  assumption. apply Himp. assumption. 
Qed.

(* 削弱后条件 *)
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c H1 H2.
  intros st st' HC HP.
  apply H2.
  apply (H1 st st').
  assumption.
  assumption.
Qed.

(* 缩放集合 *)
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption. 
Qed.

(* 跳过 *)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.
Qed.

(* 顺序 *)
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. 
Qed.

Definition bassn b : Assertion :=
  fun st => (Eval_expr st b = fun _ => [Hi]).
Coercion bassn : expr >-> Assertion.
Arguments bassn /.

Lemma bexp_eval_true : forall b st,
  Eval_expr st b = (fun _ => [Hi]) -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption. 
Qed.

Axiom Bequal : forall (b1 b2 : bus),
  b1 time <> b2 time -> b1 = b2 -> False.

Lemma bexp_eval_false : forall b st,
  Eval_expr st b = (fun time => [Lo]) -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe.
  apply (Bequal (fun _ : nat => [Hi]) (fun _ : nat => [Lo])).
  - unfold "<>". intros. inversion H.
  - apply Hbe.
Qed.

Theorem hoare_if : forall P Q (b : expr) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} IF b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b 是 true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b 是 false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. 
Qed.

Theorem hoare_while : forall P (b:expr) c,
  {{P /\ b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(* 霍尔逻辑公理系统 *)
Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (Q [[V|-> a]]) (V ::= a) Q
  | H_Seq : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (IF b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  intros.
  induction X0.
  - apply hoare_skip.
  - apply hoare_asgn. 
  - eapply hoare_seq. apply IHX0_2. apply IHX0_1.
  - eapply hoare_if; assumption.
  - eapply hoare_while. assumption.
  - eapply hoare_consequence. 
    + apply IHX0.
    + unfold "->>". apply p.
    + unfold "->>". apply q.
Qed.











Definition H : bus := fun _ => [Hi].
Definition L : bus := fun _ => [Lo].

Definition as1 : Assertion := (Z = H) /\ (X = H).

Definition as2 : Assertion := X = (X ++).

Definition test : com :=
If Z == H THEN X ::= X ++ fI.

(* 单边条件测试 *)
Theorem test1 : 
(X !-> H; Z !-> H)
=[test]=>
(X !-> fun _ => [Hi; Lo]; X !-> H; Z !-> H).
Proof.
  eapply E_ifTrue.
  - reflexivity.
  - eapply E_Ass. reflexivity.
Qed.

Definition test2 : 
(X !-> H; Z !-> L) 
=[test]=>
(X !-> H; Z !-> L).
Proof.
  eapply E_ifFalse. reflexivity.
Qed.

Definition WIDTH : string := "WIDTH".
Definition add_A : string := "add_A".
Definition add_B : string := "add_B".
Definition add_start : string := "start".
Definition restn : string := "restn".
Definition add_done : string := "done".
Definition add_res : string :="add_res".
Definition in_a : string := "in_a".
Definition in_b : string := "in_b".
Definition in_m : string := "in_m".
Definition reg_A : string := "reg_A".
Definition reg_B : string := "reg_B".
Definition reg_M : string := "reg_M".
Definition start : string := "start".
Definition done : string := "done".
Definition cnt : string := "cnt".
Definition reg_result : string := "reg_result".
Definition C : string := "C".
Definition T : string := "T".
(* 状态机中状态定义 *)
Definition IDLE : bus := fun _ => [Lo; Lo; Lo].
Definition START : bus := fun _ => [Lo; Lo; Hi].
Definition WAIT1 : bus := fun _ => [Lo; Hi; Lo].
Definition CHECK : bus := fun _ => [Lo; Hi; Hi].
Definition WAIT2 : bus := fun _ =>[Hi; Lo; Lo].
Definition DONE : bus := fun _ => [Hi; Lo; Hi].

Definition State : string := "State". 
Definition next_State : string := "next_State".

Definition reg_C_0 : string := "reg_C_0".

Definition result : string := "result".
Definition done_flag : string := "done_falg".

Definition input_And_output : com :=
in_a ::= Reg Null (len-1);;
in_b ::= Reg Null (len-1);;
in_m ::= Reg Null (len-1);;
result ::= Reg Null (len-1).

Definition define_reg : com :=
reg_A ::= Reg Null (len+1);;
reg_B ::= Reg Null (len+1);;
reg_M ::= Reg Null (len+1);;
add_A ::= Reg Null (len+2);;
add_B ::= Reg Null (len+2);;
reg_result ::= Reg Null (len+2);;
C ::= Reg Null (len+2);;
T ::= Reg Null (len+2);;
add_res ::= Reg Null (len+2).

(* 加法器 *)
Definition ADDER : com :=
IF restn == H THEN
  add_res ::= L;;
  add_done ::= L
ELSE
  IF add_start == H THEN
    add_res ::= add_A + add_B;;
    add_done ::= H
  ELSE 
    add_res ::= add_res;;
    add_done ::= L
  FI
FI.

Theorem adder_correct : forall (x y : bus),
  (add_A !-> x; add_B !-> y; add_start !-> H; restn !-> L) 
  =[ ADDER ]=>
  (add_done !-> H; add_res !-> (fun time => (BPlus (x time) (y time) Lo)); 
  add_A !-> x; add_B !-> y; add_start !-> H; restn !-> L).
Proof.
  intros.
  apply E_IfFalse.
  + reflexivity.
  + apply E_IfTrue.
    * reflexivity.
    * eapply E_Seq.
      - eapply E_Ass. reflexivity.
      - eapply E_Ass. reflexivity.
Qed.

Theorem adder_restn : forall res : bus,
  (add_res !-> res; restn !-> H) 
  =[ ADDER ]=>
  (add_done !-> L; add_res !-> L;
  add_res !-> res; restn !-> H).
Proof.
  intros.
  apply E_IfTrue.
  + reflexivity.
  + eapply E_Seq. 
    * eapply E_Ass. reflexivity. 
    * eapply E_Ass. reflexivity.
Qed.

Theorem adder_keep : forall res : bus,
  (add_start !-> L; add_res !-> res; restn !-> L) 
  =[ ADDER ]=>
  (add_done !-> L; add_res !-> res; add_start !-> L; add_res !-> res; restn !-> L).
Proof.
  intros.
  apply E_IfFalse.
  + reflexivity.
  + apply E_IfFalse.
    * reflexivity.
    * eapply E_Seq.
      - eapply E_Ass. reflexivity.
      - eapply E_Ass. reflexivity. 
Qed.

(* 初始补零 *)
Definition init : com :=
  IF restn == L THEN
    reg_A ::= L;;
    reg_B ::= L;;
    reg_M ::= L
  ELSE 
    IF start == L THEN
      reg_A ::= {(econv [Lo; Lo]) , in_a};;
      reg_B ::= {(econv [Lo; Lo]) , in_b};;
      reg_M ::= in_m
    ELSE
      reg_A ::= reg_A;;
      reg_B ::= reg_B;;
      reg_M ::= reg_M
    FI
  FI.

Theorem init_restn : forall A B M : bus,
  (reg_A !-> A; reg_B !-> B; reg_M !-> M; restn !-> L) 
  =[ init ]=>
  (reg_M !-> L; reg_B !-> L; reg_A !-> L;
  reg_A !-> A; reg_B !-> B; reg_M !-> M; restn !-> L).
Proof.
  intros.
  apply E_IfTrue.
  + reflexivity.
  + eapply E_Seq. 
    * eapply E_Ass. reflexivity. 
    * eapply E_Seq. 
      - eapply E_Ass; reflexivity.
      - eapply E_Ass; reflexivity.
Qed.

(* cnt_controller *)
Definition cnt_control : com :=
IF restn == L THEN
  cnt ::= L
ELSE 
  IF (State == IDLE) || (State == DONE) THEN
    cnt ::= L
   ELSE
     If State == CHECK THEN
       cnt ::= cnt ++
     fI
  FI
FI.

Theorem cnt_incr : forall c : bus,
  (cnt !-> c; State !-> CHECK; restn !-> H) 
  =[ cnt_control ]=>
  (cnt !-> fun time => (Incr (c time)); 
  cnt !-> c; State !-> CHECK; restn !-> H).
Proof.
  intros.
  eapply E_IfFalse.
  * reflexivity.
  * eapply E_IfFalse.
    - reflexivity.
    - eapply E_ifTrue.
      + reflexivity.
      + eapply E_Ass. reflexivity.
Qed.

Theorem cnt_rest : forall c s : bus,
  (State !-> s; cnt !-> c; restn !-> L) 
  =[ cnt_control ]=> 
  (cnt !-> L; State !-> s; cnt !-> c; restn !-> L).
Proof.
  intros.
  eapply E_IfTrue.
  - reflexivity.
  - eapply E_Ass. reflexivity.
Qed.

Theorem cnt_set_L : forall c s : bus,
  (s = IDLE \/ s = DONE) ->
  (State !-> s; cnt !-> c; restn !-> H) 
  =[ cnt_control ]=>
  (cnt !-> L; State !-> s; cnt !-> c; restn !-> H).
Proof.
  intros.
  destruct H0.
  - rewrite H0. eapply E_IfFalse.
    + reflexivity.
    + eapply E_IfTrue.
      * reflexivity.
      * eapply E_Ass. reflexivity.
  - rewrite H0. eapply E_IfFalse.
    + reflexivity.
    + eapply E_IfTrue.
      * reflexivity.
      * eapply E_Ass. reflexivity.
Qed.

Theorem cnt_keep : forall c s : bus,
  (s = START \/ s = WAIT1 \/ s = WAIT2) ->
  (State !-> s; cnt !-> c; restn !-> H) 
  =[ cnt_control ]=>
  (State !-> s; cnt !-> c; restn !-> H).
Proof.
  intros. destruct H0.
  - rewrite H0. eapply E_IfFalse.
    + reflexivity.
    + eapply E_IfFalse. 
      * reflexivity.
      * eapply E_ifFalse. reflexivity.
  - destruct H0.
    + rewrite H0. eapply E_IfFalse.
      reflexivity. eapply E_IfFalse. reflexivity.
      eapply E_ifFalse. reflexivity.
    + rewrite H0. eapply E_IfFalse.
      reflexivity. eapply E_IfFalse. reflexivity.
      eapply E_ifFalse. reflexivity.
Qed.

(* 计算qi *)
Definition qi_compute : com :=
  reg_C_0 ::= (C at L) ^ ((reg_A at cnt) && (reg_B at L)).

(* fsm_controller *)
Definition fsm_control : com :=
IF restn == L THEN
  State ::= IDLE
ELSE 
  State ::= next_State
FI.

Theorem fsm_control_reset : forall x,
  (restn !-> L; State !-> x)
  =[ fsm_control ]=>
  (State !-> IDLE; restn !-> L; State !-> x).
Proof.
  intros x.
  eapply E_IfTrue.
  - reflexivity.
  - eapply E_Ass. reflexivity.
Qed.

(* fsm *)
Definition fsm : com :=
If State == IDLE THEN
  IF start == H THEN
    next_State ::= START
  ELSE
    next_State ::= IDLE
  FI
fI;;

If State == START THEN
  IF cnt == WIDTH + two THEN
    next_State ::= DONE
  ELSE
    IF (reg_A at cnt) == H THEN
      next_State ::= WAIT1
    ELSE
      next_State ::= CHECK
    FI
  FI
fI;;

If State == WAIT1 THEN
  IF add_done == H THEN
    next_State ::= CHECK
  ELSE
    next_State ::= WAIT1
  FI
fI;;

If State == CHECK THEN
  IF reg_C_0 == L THEN
    next_State ::= START
  ELSE
    next_State ::= WAIT2
  FI
fI;;

If State == WAIT2 THEN
  IF add_done == H THEN
    next_State ::= START
  ELSE
    next_State ::= WAIT2
  FI
fI;;

If State == DONE THEN
  next_State ::= IDLE
fI.

(* C_controller *)
Definition C_controller : com :=
IF restn == L THEN
  T ::= L;;
  C ::= L
ELSE 
  IF State == IDLE THEN
    T ::= L;;
    C ::= L
  ELSE
    IF (State == WAIT1 && add_done == H) THEN
      T ::= add_res
    ELSE
      IF (State == CHECK && reg_C_0 == L) THEN
        IF (reg_A at cnt) == H THEN
          C ::= T >> 1
        ELSE
          C ::= C >> 1
        FI
      ELSE
        If (State == WAIT2 && add_done == H) THEN
          C ::= add_res >> 1
        fI
      FI
    FI
  FI
FI.

(* add_controller *)
Definition add_controller : com :=
IF restn == L THEN
  add_start ::= L;; add_A ::= L;; add_B ::= L
ELSE
  IF (State == START && (reg_A at cnt) == H) THEN
    add_start ::= H;; add_A ::= C;; add_B ::= reg_B 【len ：0】
  ELSE
    IF (State == CHECK && reg_C_0 == H) THEN
      add_start ::= H;;
      IF (reg_A at cnt) == H THEN
        add_A ::= T
      ELSE
        add_A ::= C
      FI;;
      add_B ::= reg_M
    ELSE
      If (State == DONE || State == WAIT1 || State == WAIT2) THEN
        add_start ::= L
      fI
    FI
  FI
FI.

(* done_controller *)
Definition done_controller : com :=
IF restn == L THEN
  done ::= L;; reg_result ::= L
ELSE
  IF next_State == START THEN
    done ::= L
  ELSE 
    If State == DONE THEN
      done ::= H;; reg_result ::= C
    fI
  FI
FI.

Theorem mon_done : forall res : bus,
  (State !-> DONE; C !-> res; restn !-> H)
  =[ done_controller ]=>
  (reg_result !-> res; done !-> H; 
  State !-> DONE; C!-> res; restn !-> H).
Proof.
  intros.
  eapply E_IfFalse.
  - reflexivity.
  - eapply E_IfFalse.
    + reflexivity.
    + eapply E_ifTrue.
      * reflexivity.
      * eapply E_Seq.
        { eapply E_Ass. reflexivity.
        } eapply E_Ass. reflexivity.
Qed.

Definition fini : com :=
result ::= reg_result 【len-1 ：0】;;
done_flag ::= done.

Check sig.
Print sig.















