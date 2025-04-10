(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Fin-fun model
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
  1. What is a matrix with zero rows and zero columns?
     * https://fr.wikipedia.org/wiki/Matrice_vide
       维度为0的矩阵称为空矩阵(empty matrix)，即r*0,0*c,0*0等形式；
       空矩阵的行列式为1，即空积
       
     * 在 matlab, scilab, R, python 等软件中都有支持。

     * 一个实际的问题
       用矩阵A表示学生各科的成绩，行数是学生数量，列数是科目数，
       A(i,j)表示第i个学生第j科目的成绩。
       那么，初始时是一个 0x0 的矩阵，或者 0×c的矩阵（c是科目数）

  2. 变换矩阵，基变换，
     https://en.wikipedia.org/wiki/Change_of_basis
     change-of-basis matrix (also called transition matrix)
 *)


Require Export FinMatrix.CoqExt.Hierarchy.
Require Export FinMatrix.CoqExt.ListExt.
Require Export FinMatrix.Matrix.Vector.
Require Reals.


Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.

(** Control the scope *)
(* Open Scope nat_scope. *)
(* Open Scope fin_scope. *)
(* Open Scope A_scope. *)
(* Open Scope vec_scope. *)
Open Scope mat_scope.


(* ######################################################################### *)
(** * Matrix type and basic operations *)

(* ======================================================================= *)
(** ** Definition of matrix type *)

(* Note: we use notation to enabling the automation by vector automatically *)

(** An r*c matrix over tA type  *)
Notation mat tA r c := (@vec (@vec tA c) r).

(** An n-dimensional square matrix over tA type *)
Notation smat tA n := (mat tA n n).

(* Actually, mat tA r c = forall tA r c, 'I_r -> 'I_c -> tA  *)
(* Eval cbv in forall tA r c, mat tA r c. *)

(** Make a mat type explicitly *)
Definition mmake {tA : Type} {r c : nat} (f : 'I_r -> 'I_c -> tA) : @mat tA r c := f.


(* ======================================================================= *)
(** ** Get element of a matrix *)

(* Note that: these notatiosn are dangerous.
   The reason can be found in the definition of `V.1` in file `Vector.v`
 *)
Notation "M .11" := (M.1.1) : mat_scope.
Notation "M .12" := (M.1.2) : mat_scope.
Notation "M .13" := (M.1.3) : mat_scope.
Notation "M .14" := (M.1.4) : mat_scope.
Notation "M .21" := (M.2.1) : mat_scope.
Notation "M .22" := (M.2.2) : mat_scope.
Notation "M .23" := (M.2.3) : mat_scope.
Notation "M .24" := (M.2.4) : mat_scope.
Notation "M .31" := (M.3.1) : mat_scope.
Notation "M .32" := (M.3.2) : mat_scope.
Notation "M .33" := (M.3.3) : mat_scope.
Notation "M .34" := (M.3.4) : mat_scope.
Notation "M .41" := (M.4.1) : mat_scope.
Notation "M .42" := (M.4.2) : mat_scope.
Notation "M .43" := (M.4.3) : mat_scope.
Notation "M .44" := (M.4.4) : mat_scope.

(** i1 = i2 -> j1 = j2 -> = M (nat2fin i1) (nat2fin j1) = M (nat2fin i2) (nat2fin j2) *)
Lemma mnth_eq :
  forall {tA r c} (M : @mat tA r c) i1 j1 i2 j2
    (Hi1: i1 < r) (Hi2: i2 < r) (Hj1: j1 < c) (Hj2: j2 < c),
    i1 = i2 -> j1 = j2 ->
    M.[nat2fin i1 Hi1].[nat2fin j1 Hj1] = M.[nat2fin i2 Hi2].[nat2fin j2 Hj2].
Proof. intros. subst. f_equal; apply fin_eq_iff; auto. Qed.

Lemma meq_iff_mnth : forall {tA r c} (M N : mat tA r c),
    M = N <-> (forall i j, M.[i].[j] = N.[i].[j]).
Proof.
  intros. split; intros; subst; auto.
  apply veq_iff_vnth. intros i.
  apply veq_iff_vnth. intros j. auto.
Qed.

Lemma mneq_iff_exist_mnth_neq : forall {tA r c} (M N : mat tA r c),
    M <> N <-> (exists i j, M.[i].[j] <> N.[i].[j]).
Proof.
  intros. rewrite meq_iff_mnth. split; intros.
  - apply not_all_ex_not in H. destruct H as [i H].
    apply not_all_ex_not in H. destruct H as [j H]. exists i, j; auto.
  - destruct H as [i [j H]].
    apply ex_not_not_all; auto. exists i.
    apply ex_not_not_all; auto. exists j. auto.
Qed.


(* ======================================================================= *)
(** ** Cast between two [mat] type that are actually of equal dimensions *)

(** Cast from [mat r1 c1] type to [mat r1 c2] type if [r1 = r2 /\ c1 = c2] *)
Definition mcast {tA r1 c1 r2 c2} (A : mat tA r1 c1) (H1 : r1 = r2)
  (H2 : c1 = c2) : @mat tA r2 c2.
  subst. apply A.
Defined.

Definition mcastS2Add {tA r c} (A : mat tA (S r) (S c))
  : mat tA (r + 1) (c + 1).
  refine (mcast A _ _). all: rewrite Nat.add_1_r; auto.
Defined.

Definition mcastAdd2S {tA r c} (A : mat tA (r + 1) (c + 1))
  : mat tA (S r) (S c).
  refine (mcast A _ _). all: rewrite Nat.add_1_r; auto.
Defined.


(* ======================================================================= *)
(** ** Convert between [dlist] and [mat] *)
Section l2m_m2l.
  Context {tA} (Azero : tA).

  (** matrix to dlist *)
  Definition m2l {r c} (M : mat tA r c) : dlist tA := map v2l (v2l M).
  (** dlist to matrix *)
  Definition l2m {r c} (d : dlist tA) : mat tA r c :=
    l2v (vzero Azero) (map (l2v Azero) d).
  (* Definition l2m' {r c} (d : dlist tA) : mat tA r c :=
    @l2v (vec c) (vzero Azero) r (map (@l2v tA Azero c) d). *)

  Lemma m2l_length : forall {r c} (M : mat tA r c), length (m2l M) = r.
  Proof. intros. unfold m2l. rewrite map_length. rewrite v2l_length; auto. Qed.

  Lemma m2l_width : forall {r c} (M : mat tA r c), width (m2l M) c.
  Proof.
    intros. unfold width,m2l. apply Forall_map_forall.
    intros. apply v2l_length.
  Qed.

  Lemma nth_m2l_length : forall {r c} (M : mat tA r c) i,
      i < r -> length (nth i (m2l M) []) = c.
  Proof.
    intros. unfold m2l.
    rewrite nth_map with (n:=r)(Azero:=vzero Azero); auto; rewrite v2l_length; auto.
  Qed.

  Lemma m2l_inj : forall {r c} (M N : mat tA r c), m2l M = m2l N -> M = N.
  Proof.
    intros. unfold m2l in H.  apply map_inj in H; auto. apply v2l_inj; auto.
    intros. apply v2l_inj; auto.
  Qed.

  Lemma nth_m2l : forall {r c} (M : @mat tA r c) i j (Hi : i < r) (Hj : j < c),
      nth j (nth i (m2l M) []) Azero = M.[nat2fin i Hi].[nat2fin j Hj].
  Proof.
    intros. unfold m2l. erewrite nth_map with (n:=r)(Azero:=vzero Azero); auto.
    - rewrite nth_v2l with (E:=Hi). rewrite nth_v2l with (E:=Hj). auto.
    - apply v2l_length.
  Qed.

  Lemma mnth_l2m : forall {r c} (d : dlist tA) i j,
      length d = r -> width d c ->
      (@l2m r c d).[i].[j] = nth j (nth i d []) Azero.
  Proof.
    intros. unfold l2m. rewrite vnth_l2v.
    rewrite nth_map with (n:=r)(Azero:=[]); auto; fin.
  Qed.

  Lemma l2m_inj : forall {r c} (d1 d2 : dlist tA),
      length d1 = r -> width d1 c ->
      length d2 = r -> width d2 c ->
      @l2m r c d1 = @l2m r c d2 -> d1 = d2.
  Proof.
    intros. unfold l2m in H3. apply l2v_inj in H3; try rewrite map_length; auto.
    apply map_inj in H3; auto.
    intros. apply l2v_inj in H6; auto.
    apply (width_imply_in_length a d1); auto.
    apply (width_imply_in_length b d2); auto.
  Qed.

  Lemma l2m_m2l : forall {r c} (M : mat tA r c), (@l2m r c (m2l M)) = M.
  Proof.
    intros. unfold l2m,m2l.
    apply veq_iff_vnth; intros i.
    apply veq_iff_vnth; intros j.
    rewrite !vnth_l2v.
    rewrite nth_map with (n:=r)(Azero:=[]); fin.
    - rewrite nth_map with (n:=r)(Azero:=vzero Azero); fin.
      + rewrite l2v_v2l.
        rewrite nth_v2l with (E:=fin2nat_lt _); fin.
      + apply v2l_length.
    - rewrite map_length. apply v2l_length.
  Qed.

  Lemma m2l_l2m : forall {r c} (d : dlist tA),
      length d = r -> width d c -> m2l (@l2m r c d) = d.
  Proof.
    intros. unfold l2m,m2l; simpl. rewrite v2l_l2v.
    - rewrite map_map. apply map_id_In; intros. apply v2l_l2v.
      apply (width_imply_in_length a d); auto.
    - rewrite map_length; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (M : mat tA r c), (exists d, @l2m r c d = M).
  Proof. intros. exists (m2l M). apply l2m_m2l. Qed.

  Lemma m2l_surj : forall {r c} (d : dlist tA),
      length d = r -> width d c -> (exists M : mat tA r c, m2l M = d).
  Proof. intros. exists (@l2m r c d). apply m2l_l2m; auto. Qed.

End l2m_m2l.



(* ======================================================================= *)
(** ** Automation for matrix operations *)

(** Proof matrix equality with point-wise element equalities over list *)
Ltac meq :=
  (* convert matrix equality to list equality *)
  apply m2l_inj; cbv;
  (* convert list equality to point-wise element equalities *)
  list_eq.



(* ======================================================================= *)
(** ** matrix transpose *)

Definition mtrans {tA r c} (M : mat tA r c) : mat tA c r := fun i j => M.[j].[i].
Notation "M \T" := (mtrans M) : mat_scope.

(** Transpose twice return back *)
Lemma mtrans_mtrans : forall tA r c (M : mat tA r c), (M\T)\T = M.
Proof. intros. auto. Qed.
#[export] Hint Rewrite mtrans_mtrans : vec.

(** (M\T)[i,j] = M[j,i] *)
Lemma mnth_mtrans : forall tA r c (M : mat tA r c) i j, (M\T).[i].[j] = M.[j].[i].
Proof. intros. auto. Qed.
#[export] Hint Rewrite mnth_mtrans : vec.

(** (M\T)[i,*] = M[*,i] *)
Lemma vnth_mtrans : forall tA r c (M : mat tA r c) i, (M\T).[i] = fun j => M.[j].[i].
Proof. intros. auto. Qed.
#[export] Hint Rewrite vnth_mtrans : vec.

(** matrix transpose is injective *)
Lemma mtrans_inj : forall tA r c (M1 M2 : mat tA r c), mtrans M1 = mtrans M2 -> M1 = M2.
Proof.
  intros. rewrite meq_iff_mnth in H. rewrite meq_iff_mnth; intros.
  specialize (H j i). auto.
Qed.


(* ======================================================================= *)
(** ** Get row and column of a matrix *)

Definition mrow {tA r c} (M : mat tA r c) (i : 'I_r) : @vec tA c := M i.
#[export] Hint Unfold mrow : vec.

Definition mcol {tA r c} (M : mat tA r c) (j : 'I_c) : @vec tA r := fun i => M i j.
#[export] Hint Unfold mcol : vec.
Notation "M &[ i ]" := (mcol M i) : mat_scope.
Notation "M &1" := (mcol M #0) : mat_scope.
Notation "M &2" := (mcol M #1) : mat_scope.
Notation "M &3" := (mcol M #2) : mat_scope.
Notation "M &4" := (mcol M #3) : mat_scope.

Lemma vnth_mrow : forall tA r c (M : mat tA r c) (i : 'I_r) (j : 'I_c),
    (mrow M i).[j] = M.[i].[j].
Proof. intros. auto. Qed.
#[export] Hint Rewrite vnth_mrow : vec.

Lemma vnth_mcol : forall tA r c (M : mat tA r c) (i : 'I_r) (j : 'I_c),
    M&[j].[i] = M.[i].[j].
Proof. intros. auto. Qed.
#[export] Hint Rewrite vnth_mcol : vec.


(* ======================================================================= *)
(** ** Get head or tail row *)

(** Get head row *)
Definition mheadr {tA r c} (M : mat tA (S r) c) : vec c := vhead M.
#[export] Hint Unfold mheadr : vec.

(** Get tail row *)
Definition mtailr {tA r c} (M : mat tA (S r) c) : vec c := vtail M.
#[export] Hint Unfold mtailr : vec.


(* ======================================================================= *)
(** ** Get head or tail column *)

(** Get head column *)
Definition mheadc {tA r c} (M : @mat tA r (S c)) : @vec tA r := fun i => vhead (M.[i]).
#[export] Hint Unfold mheadc : vec.

(** Get tail column *)
Definition mtailc {tA r c} (M : @mat tA r (S c)) : @vec tA r := fun i => vtail (M.[i]).
#[export] Hint Unfold mtailc : vec.

(** (mheadc M).i = M.i.0 *)
Lemma vnth_mheadc : forall tA r c (M : @mat tA r (S c)) i, (mheadc M).[i] = M.[i].[fin0].
Proof. auto. Qed.
#[export] Hint Rewrite vnth_mheadc : vec.

(** (mtailc M).i = M.i.(n-1) *)
Lemma vnth_mtailc : forall tA r c (M : @mat tA r (S c)) i, (mtailc M).[i] = M.[i].[#c].
Proof. auto. Qed.
#[export] Hint Rewrite vnth_mtailc : vec.

(** mtailc A = mcol A c *)
Lemma mtailc_eq_mcol : forall tA r c (A : mat tA r (S c)), mtailc A = mcol A #c.
Proof. auto. Qed.



(* ######################################################################### *)
(** * Row vector and column vector *)
  
(* ======================================================================= *)
(** ** Definition of row/column vector type *)

Notation rvec tA n := (mat tA 1 n).
Notation cvec tA n := (mat tA n 1).

(* ======================================================================= *)
(** ** Convert between [cvec] and [vec] *)
Section cv2v_v2cv.
  Context {tA : Type}.
  Notation cvec n := (cvec tA n).
  
  Definition cv2v {n} (M : cvec n) : vec n := fun i => M.[i].[fin0].
  Definition v2cv {n} (a : vec n) : cvec n := fun i j => a.[i].
  
  Lemma cv2v_spec : forall {n} (M : cvec n) i, M.[i].[fin0] = (cv2v M).[i].
  Proof. auto. Qed.
  Lemma v2cv_spec : forall {n} (a : vec n) i, a.[i] = (v2cv a).[i].[fin0].
  Proof. auto. Qed.

  Lemma cv2v_v2cv : forall {n} (a : vec n), cv2v (v2cv a) = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.
  
  Lemma v2cv_cv2v : forall {n} (M : cvec n), v2cv (cv2v M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros. cbv. f_equal.
    rewrite (fin1_uniq j). apply fin_eq_iff; auto.
  Qed.

  Lemma cv2v_inj : forall {n} (M N : cvec n), cv2v M = cv2v N -> M = N.
  Proof.
    intros. rewrite veq_iff_vnth in H. rewrite meq_iff_mnth.
    unfold cv2v in H. intros. rewrite (fin1_uniq j). auto.
  Qed.
  
  Lemma v2cv_inj : forall {n} (a b : vec n), v2cv a = v2cv b -> a = b.
  Proof.
    intros. rewrite meq_iff_mnth in H. rewrite veq_iff_vnth.
    unfold v2cv in H. intros. apply (H i fin0).
  Qed.
  
  Lemma vnth_v2cv : forall {n} (a : vec n) i j, (v2cv a).[i].[j] = a.[i].
  Proof. intros. unfold v2cv. auto. Qed.

  Lemma vnth_cv2v : forall {n} (M : cvec n) i j, (cv2v M).[i] = M.[i].[j].
  Proof. intros. unfold cv2v. f_equal. rewrite (fin1_uniq j); auto. Qed.
  
End cv2v_v2cv.

(* ======================================================================= *)
(** ** Convert between [rvec] and [vec] *)
Section rv2v_v2rv.
  Context {tA : Type}.
  Notation rvec n := (rvec tA n).
  
  Definition rv2v {n} (M : rvec n) : vec n := fun i => M.[fin0].[i].
  Definition v2rv {n} (a : vec n) : rvec n := fun i j => a.[j].
  
  Lemma rv2v_spec : forall {n} (M : rvec n) i, M.[fin0].[i] = (rv2v M).[i].
  Proof. auto. Qed.
  Lemma v2rv_spec : forall {n} (a : vec n) i, a.[i] = (v2rv a).[fin0].[i].
  Proof. auto. Qed.

  Lemma rv2v_v2rv : forall {n} (a : vec n), rv2v (v2rv a) = a.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.

  Lemma v2rv_rv2v : forall {n} (M : rvec n), v2rv (rv2v M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros. cbv. f_equal. rewrite (fin1_uniq i).
    apply fin_eq_iff; auto.
  Qed.
  
  Lemma vnth_v2rv : forall {n} (a : vec n) i, (v2rv a).[i]  = a.
  Proof. intros. unfold v2rv. auto. Qed.
  
End rv2v_v2rv.

(* ======================================================================= *)
(** ** Convert between [cvec] and [rvec] *)
  
Lemma v2rv_cv2v : forall {tA n} (M : cvec tA n), v2rv (cv2v M) = fun i j => M.[j].[i].
Proof.
  intros. apply meq_iff_mnth; intros. cbv. f_equal.
  rewrite (fin1_uniq i). apply fin_eq_iff; auto.
Qed.


(* ######################################################################### *)
(** * Make a matrix *)

(* ======================================================================= *)
(** ** Zero matrix *)
Section mat0.
  Context {tA} {Azero : tA}.
  Definition mat0 {r c} : mat tA r c := fun _ _ => Azero.
  
  (** mat0[i,j] = 0 *)
  Lemma mnth_mat0 : forall {r c} i j, (@mat0 r c).[i].[j] = Azero.
  Proof. intros. auto. Qed.

  (** row mat0 i = vzero *)
  Lemma mrow_mat0 : forall {r c} i, (@mat0 r c).[i] = vzero Azero.
  Proof. intros. auto. Qed.

  (* col mat0 i = vzero *)
  Lemma mcol_mat0 : forall {r c} j, (@mat0 r c)&[j] = vzero Azero.
  Proof. intros. auto. Qed.

  (** mat0\T = mat0 *)
  Lemma mtrans_mat0 : forall {r c : nat}, (@mat0 r c)\T = mat0.
  Proof. intros. auto. Qed.

  (** v2rv vzero = mat0 *)
  Lemma v2rv_vzero : forall n, v2rv (@vzero _ Azero n) = @mat0 1 n.
  Proof. intros. auto. Qed.

  (** v2cv vzero = mat0 *)
  Lemma v2cv_vzero : forall n, v2cv (@vzero _ Azero n) = @mat0 n 1.
  Proof. intros. auto. Qed.
  
End mat0.

(* ======================================================================= *)
(** ** Convert between list of [rvec] and [mat] *)
Section rvl2m_m2rvl.
  Context {tA} (Azero : tA).
  Notation mat r c := (mat tA r c).

  (** mat to `list of row vectors` *)
  Definition m2rvl {r c} (M : mat r c) : list (@vec tA c) :=
    map (fun i => M.[i]) (finseq r).

  (** `list of row vectors` to mat *)
  Definition rvl2m {r c} (l : list (@vec tA c)) : mat r c :=
    fun i => nth i l (vzero Azero).

  Lemma m2rvl_rvl2m : forall {r c} (l : list (@vec tA c)),
      length l = r -> @m2rvl r c (rvl2m l) = l.
  Proof.
    intros. unfold m2rvl, rvl2m.
    apply (list_eq_ext (vzero Azero) r); auto.
    - intros. rewrite nth_map_finseq with (E:=H0). f_equal.
    - rewrite map_length, finseq_length. auto.
  Qed.
  
  Lemma rvl2m_m2rvl : forall {r c} (M : mat r c), rvl2m (m2rvl M) = M.
  Proof.
    intros. unfold rvl2m, m2rvl. apply meq_iff_mnth; intros.
    rewrite nth_map_finseq with (E:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.
End rvl2m_m2rvl.

(* ======================================================================= *)
(** ** Convert between list of [cvec] and [mat] *)
Section cvl2m_m2cvl.
  Context {tA} (Azero : tA).
  Notation mat r c := (mat tA r c).
  (** mat to `list of column vectors` *)
  Definition m2cvl {r c} (M : mat r c) : list (@vec tA r) :=
    map (fun i j => M j i) (finseq c).
  
  (** `list of column vectors` to mat *)
  Definition cvl2m {r c} (l : list (@vec tA r)) : mat r c :=
    fun i j  => (nth j l (vzero Azero)).[i].
  
  Lemma m2cvl_cvl2m : forall {r c} (l : list (@vec tA r)),
      length l = c -> @m2cvl r c (cvl2m l) = l.
  Proof.
    intros. unfold m2cvl, cvl2m.
    apply (list_eq_ext (vzero Azero) c); auto.
    - intros. rewrite nth_map_finseq with (E:=H0).
      apply veq_iff_vnth; intros j. f_equal.
    - rewrite map_length, finseq_length. auto.
  Qed.
  
  Lemma cvl2m_m2cvl : forall {r c} (M : mat r c), cvl2m (m2cvl M) = M.
  Proof.
    intros. unfold cvl2m, m2cvl. apply meq_iff_mnth; intros.
    rewrite nth_map_finseq with (E:=fin2nat_lt _). f_equal. apply fin_fin2nat.
  Qed.

End cvl2m_m2cvl.
  
(* ======================================================================= *)
(** ** Convert between function and [mat] *)
Section f2m_m2f.
  Context {tA} (Azero : tA).

  Definition f2m {r c} (f : nat -> nat -> tA) : mat tA r c :=
    @f2v _ r (fun i => @f2v tA c (f i)).

  Lemma f2m_inj : forall {r c} (f g : nat -> nat -> tA),
      @f2m r c f = @f2m r c g -> (forall i j, i < r -> j < c -> f i j = g i j).
  Proof.
    intros. unfold f2m in H.
    apply f2v_inj with (i:=i) in H; auto.
    apply f2v_inj with (i:=j) in H; auto.
  Qed.

  (** (f2m f).[i].[j] = f i j *)
  Lemma mnth_f2m : forall {r c} (f : nat -> nat -> tA) i j,
      (@f2m r c f) i j = f i j.
  Proof. auto. Qed.
    
  (** (f2m f).[i] = f2v (f i) *)
  Lemma vnth_f2m : forall {r c} (f : nat -> nat -> tA) i,
      (@f2m r c f).[i] = f2v (f i).
  Proof. auto. Qed.


  Definition m2f {r c} (M : mat tA r c) : (nat -> nat -> tA) :=
    fun i => @v2f _ Azero c (@v2f _ (vzero Azero) r M i).

  (** (m2f M) i j = M[nat2fin i].[nat2fin j] *)
  Lemma nth_m2f : forall {r c} (M : @mat tA r c) (i j : nat) (Hi : i < r)(Hj : j < c),
      (m2f M) i j = M.[nat2fin i Hi].[nat2fin j Hj].
  Proof. intros. unfold m2f,v2f. fin. f_equal; fin. Qed.
  
  (** (m2f M) i j = M[#i,#j] *)
  Lemma nth_m2f_nat2finS : forall {r c} (M : @mat tA (S r) (S c)) i j,
      i < S r -> j < S c -> (m2f M) i j = M.[#i].[#j].
  Proof.
    intros. rewrite nth_m2f with (Hi:=H)(Hj:=H0).
    rewrite nat2finS_eq with (E:=H). rewrite nat2finS_eq with (E:=H0). auto.
  Qed.

  Lemma m2f_inj : forall {r c} (M1 M2 : @mat tA r c),
      (forall i j, i < r -> j < c -> (m2f M1) i j = (m2f M2) i j) -> M1 = M2.
  Proof.
    intros. apply meq_iff_mnth; intros.
    specialize (H i j (fin2nat_lt _) (fin2nat_lt _)).
    rewrite !nth_m2f with (Hi:=fin2nat_lt _)(Hj:=fin2nat_lt _) in H.
    fin.
  Qed.

  Lemma f2m_m2f : forall {r c} (M : @mat tA r c), f2m (m2f M) = M.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_f2m.
    rewrite nth_m2f with (Hi:=fin2nat_lt _)(Hj:=fin2nat_lt _).
    fin.
  Qed.

  Lemma m2f_f2m : forall {r c} (f : nat -> nat -> tA),
    forall i j, i < r -> j < c -> m2f (@f2m r c f) i j = f i j.
  Proof.
    intros. rewrite nth_m2f with (Hi:=H)(Hj:=H0).
    rewrite mnth_f2m. fin.
  Qed.
End f2m_m2f.

  
(* ======================================================================= *)
(** ** Construct matrix with two matrices *)
Section mapp.
  Context {tA} {Azero : tA}.
  Notation m2f := (m2f Azero).
  
  (** Append matrix by row *)
  Definition mappr {r1 r2 c} (M : mat tA r1 c) (N : mat tA r2 c)
    : mat tA (r1 + r2) c :=
    f2m (fun i j => if (i ??< r1)%nat then m2f M i j else m2f N (i - r1) j).

  (** Append matrix by column *)
  Definition mappc {r c1 c2} (M : mat tA r c1) (N : mat tA r c2)
    : mat tA r (c1 + c2) :=
    f2m (fun i j => if (j ??< c1)%nat then m2f M i j else m2f N i (j - c1)).
End mapp.

Section test.
  Let M := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let N :=  @l2m _ 9 2 2 [[11;12];[13;14]].
  (* Compute m2l (mappr M N). *)
  (* Compute m2l (mappc M N). *)
End test.

(* ======================================================================= *)
(** ** matrix with specific size *)

Section mat_specific.
  Context {tA} {Azero : tA}.
  Notation l2m := (l2m Azero).
  Variable r c : nat.
  Variable a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 : tA.

  (** *** Create matrix *)
  Definition mkmat_0_c : mat tA 0 c := vzero (vzero Azero). (* anything is ok *)
  Definition mkmat_r_0 : mat tA r 0 := vzero (vzero Azero). (* anything is ok *)

  Definition mkmat_1_c (a : @vec tA c) : mat tA 1 c := fun i j => a j.
  Definition mkmat_r_1 (a : @vec tA r) : mat tA r 1 := fun i j => a i.

  Definition mkmat_1_1 : mat tA 1 1 := l2m [[a11]].
  Definition mkmat_1_2 : mat tA 1 2 := l2m [[a11;a12]].
  Definition mkmat_2_1 : mat tA 2 1 := l2m [[a11];[a21]].
  Definition mkmat_2_2 : mat tA 2 2 := l2m [[a11;a12];[a21;a22]].
  Definition mkmat_1_3 : mat tA 1 3 := l2m [[a11;a12;a13]].
  Definition mkmat_2_3 : mat tA 2 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
  Definition mkmat_3_1 : mat tA 3 1 := l2m [[a11];[a21];[a31]].
  Definition mkmat_3_2 : mat tA 3 2 := l2m [[a11;a12];[a21;a22];[a31;a32]].
  Definition mkmat_3_3 : mat tA 3 3 :=
    l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Definition mkmat_1_4 : mat tA 1 4 := l2m [[a11;a12;a13;a14]].
  Definition mkmat_4_1 : mat tA 4 1 := l2m [[a11];[a21];[a31];[a41]].
  Definition mkmat_4_4 : mat tA 4 4 :=
    l2m [[a11;a12;a13;a14];[a21;a22;a23;a24];[a31;a32;a33;a34];[a41;a42;a43;a44]].
End mat_specific.

(* ======================================================================= *)
(** ** Make a diagonal matrix *)
Section mdiag.
  Context {tA} (Azero : tA).

  (** A matrix is a diagonal matrix *)
  Definition mdiag {n} (M : smat tA n) : Prop :=
    forall i j, i <> j -> M.[i].[j] = Azero.

  (** Transpose of a diagonal matrix keep unchanged *)
  Lemma mtrans_diag : forall {n} (M : smat tA n), mdiag M -> M\T = M.
  Proof.
    intros. hnf in H. apply meq_iff_mnth; intros i j.
    rewrite mnth_mtrans. destruct (i ??= j) as [E|E].
    - apply fin2nat_eq_iff in E; rewrite E. auto.
    - apply fin2nat_neq_iff in E. rewrite !H; auto.
  Qed.

  (** Construct a diagonal matrix *)
  Definition mdiagMk {n} (a : @vec tA n) : @smat tA n :=
    fun i j => if i ??= j then a.[i] else Azero.

  (** mdiagMk is correct *)
  Lemma mdiagMk_spec : forall {n} (a : @vec tA n), mdiag (mdiagMk a).
  Proof. intros. hnf. intros. unfold mdiagMk. fin. Qed.

  (** (mdiagMk l)[i,i] = l[i] *)
  Lemma mnth_mdiagMk_same : forall {n} (a : @vec tA n) i, (mdiagMk a).[i].[i] = a.[i].
  Proof. intros. unfold mdiagMk. fin. Qed.

  (** (mdiagMk l)[i,j] = 0 *)
  Lemma mnth_mdiagMk_diff : forall {n} (a : @vec tA n) i j,
      i <> j -> (mdiagMk a).[i].[j] = Azero.
  Proof. intros. unfold mdiagMk. fin. Qed.

End mdiag.

(* ======================================================================= *)
(** ** Matrix by mapping one matrix *)
Notation mmap f M := (vmap (vmap f) M).

Lemma mnth_mmap : forall {tA tB} {r c} (M : mat tA r c) (f : tA -> tB) i j,
    (mmap f M).[i].[j] = f (M.[i].[j]).
Proof. intros. unfold mmap. auto. Qed.

(* ======================================================================= *)
(** ** Matrix by mapping two matrices *)
Notation mmap2 f M N := (vmap2 (vmap2 f) M N).

Lemma mnth_mmap2 : forall {tA tB tC} {r c} (M : mat tA r c) (N : mat tB r c)
                     (f : tA -> tB -> tC) i j,
    (mmap2 f M N).[i].[j] = f (M.[i].[j]) (N.[i].[j]).
Proof. intros. unfold mmap2. auto. Qed.

Lemma mmap2_comm `{Commutative tA Aadd} : forall {r c} (M N : mat tA r c),
    mmap2 Aadd M N = mmap2 Aadd N M.
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply commutative. Qed.

Lemma mmap2_assoc `{Associative tA Aadd} : forall {r c} (M N O : mat tA r c),
    mmap2 Aadd (mmap2 Aadd M N) O = mmap2 Aadd M (mmap2 Aadd N O).
Proof. intros. apply meq_iff_mnth; intros. unfold mmap2. apply associative. Qed.


(* ######################################################################### *)
(** * Update a matrix *)

(* ======================================================================= *)
(** ** Set row or column of a matrix *)
Section mset.
  Context {tA} (Azero : tA).

  (** set element of a matrix *)
  Definition mset {r c} (M : mat tA r c) (a : tA) (i0 : 'I_r) (j0 : 'I_c) : mat tA r c :=
    fun i j => if (i =? i0) && (j =? j0) then a else M.[i].[j].

  Lemma mnth_mset_same : forall {r c} (M : mat tA r c) (a : tA) i j,
      (mset M a i j).[i].[j] = a.
  Proof.
  Admitted.
                             
  Lemma mnth_mset_diff : forall {r c} (M : mat tA r c) (a : tA) i0 j0 i j,
      i <> i0 \/ j <> j0 -> (mset M a i0 j0).[i].[j] = M.[i].[j].
  Proof.
  Admitted.


  (** set row *)
  Definition msetr {r c} (M : mat tA r c) (a : @vec tA c) (i0 : 'I_r) : mat tA r c :=
    fun i j => if i ??= i0 then a.[j] else M.[i].[j].

  Lemma mnth_msetr_same : forall {r c} (M : mat tA r c) (a : @vec tA c) (i0 : 'I_r) i j,
      i = i0 -> (msetr M a i0).[i].[j] = a.[j].
  Proof. intros. unfold msetr. fin. Qed.

  Lemma mnth_msetr_diff : forall {r c} (M : mat tA r c) (a : @vec tA c) (i0 : 'I_r) i j,
      i <> i0 -> (msetr M a i0).[i].[j] = M.[i].[j].
  Proof. intros. unfold msetr. fin. Qed.

  (** set column *)
  Definition msetc {r c} (M : mat tA r c) (a : @vec tA r) (j0 : 'I_c) : mat tA r c :=
    fun i j => if j ??= j0 then a.[i] else M.[i].[j].

  Lemma mnth_msetc_same : forall {r c} (M : mat tA r c) (a : @vec tA r) (j0 : 'I_c) i j,
      j = j0 -> (msetc M a j0).[i].[j] = a.[i].
  Proof. intros. unfold msetc. fin. Qed.

  Lemma mnth_msetc_diff : forall {r c} (M : mat tA r c) (a : @vec tA r) (j0 : 'I_c) i j,
      j <> j0 -> (msetc M a j0).[i].[j] = M.[i].[j].
  Proof. intros. unfold msetc. fin. Qed.

End mset.

(* ======================================================================= *)
(** ** Construct matrix from vector and matrix *)

(** Construct matrix by row with a vector and a matrix *)
Definition mconsrH {tA r c} (a : @vec tA c) (A : mat tA r c) : mat tA (S r) c :=
  vconsH a A.
#[export] Hint Unfold mconsrH : vec.

(** Construct matrix by row with a matrix and a vector *)
Definition mconsrT {tA r c} (A : mat tA r c) (a : @vec tA c) : mat tA (S r) c :=
  vconsT A a.
#[export] Hint Unfold mconsrT : vec.

(** Construct a matrix by column with a vector and a matrix *)
Definition mconscH {tA r c} (a : @vec tA r) (M : mat tA r c) : mat tA r (S c) :=
  @vmap2 tA (vec c) (vec (S c)) r vconsH a M.
#[export] Hint Unfold mconscH : vec.

(** Construct a matrix by column with a matrix and a vector *)
Definition mconscT {tA r c} (M : mat tA r c) (a : @vec tA r) : mat tA r (S c) :=
  @vmap2 (vec c) tA (vec (S c)) r vconsT M a.
#[export] Hint Unfold mconscT : vec.

Lemma vnth_mconscH : forall tA r c (M : mat tA r c) (a : vec r) (i : 'I_r),
    (mconscH a M).[i] = vconsH (a.[i]) (M.[i]).
Proof. auto. Qed.
#[export] Hint Rewrite vnth_mconscH : vec.

Lemma vnth_mconscT : forall tA r c (M : mat tA r c) (a : @vec tA r) i,
    (mconscT M a).[i] = vconsT M.[i] a.[i].
Proof. auto. Qed.
#[export] Hint Rewrite vnth_mconscT : vec.

(** mcol [A | v] i = v, if i = last-column-index *)
Lemma mcol_mconscT_n : forall tA r c (A : mat tA r c) v i,
    fin2nat i = c -> mcol (mconscT A v) i = v.
Proof.
  intros. apply veq_iff_vnth; intros. unfold mcol, mconscT. auto_vec.
  rewrite vnth_vconsT_n; auto.
Qed.

(**      [A]
    mcol --  i = vconsT A&[i] v[i]
         [v] *)
Lemma mcol_mconsrT : forall tA r c (A : mat tA r c) v i,
    mcol (mconsrT A v) i = vconsT (mcol A i) (v.[i]).
Proof.
  intros. apply veq_iff_vnth; intros. unfold mcol, mconsrT.
  unfold vconsT. fin.
Qed.

(** mcol [A | v] i = mcol A, if i <> last-column- index *)
Lemma mcol_mconscT_lt : forall tA r c (A : mat tA r c) v i (H : fin2nat i < c),
    mcol (mconscT A v) i = mcol A (fPredRange i H).
Proof.
  intros. apply veq_iff_vnth; intros. unfold mcol, mconscT. auto_vec.
  erewrite vnth_vconsT_lt; auto.
Qed.


(**       [a11 a12 | v1]
          [a21 a22 | v2]
   mtailr  ------- | --  =  [u1 u2 x]
          [ u1  u2 |  x]  *)
Lemma mtailr_mconscT_mconsrT_vconsT :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mtailr (mconscT (mconsrT A u) (vconsT v x)) = vconsT u x.
Proof.
  intros. apply veq_iff_vnth; intros. auto_vec. f_equal.
  all: rewrite vnth_vconsT_n; fin.
Qed.

(**       [a11 a12 | v1]    [v1]
          [a21 a22 | v2]    [v2]
   mtailc  ------------  =  [x]
          [ u1  u2 |  x]  *)
Lemma mtailc_mconsrT_mconscT_vconsT :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mtailc (mconsrT (mconscT A v) (vconsT u x)) = vconsT v x.
Proof.
  intros. apply veq_iff_vnth; intros. auto_vec. destruct (i ??= r).
  - rewrite vnth_vconsT_n; auto. rewrite !vnth_vconsT_n; auto. fin.
  - erewrite vnth_vconsT_lt. auto_vec. rewrite vnth_vconsT_n; fin.
    erewrite vnth_vconsT_lt; auto. Unshelve. fin.
Qed.

(**       [v1 | a11 a12]
          [v2 | a21 a22]
   mtailr  -- | -------  = [ x u1 u2]
          [ x |  u1  u2]  *)
Lemma mtailr_mconscH_vconsT_mconsrT :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mtailr (mconscH (vconsT v x) (mconsrT A u)) = vconsH x u.
Proof.
  intros. apply veq_iff_vnth; intros. auto_vec. rewrite !vnth_vconsT_n; fin.
Qed.

(**       [v1 | a11 a12]   [v1]
          [v2 | a21 a22]   [v2]
   mheadc  ------------  = [ x]
          [ x |  u1  u2]  *)
Lemma mheadc_mconsrT_mconscH_vconsH :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mheadc (mconsrT (mconscH v A) (vconsH x u)) = vconsT v x.
Proof.
  intros. apply veq_iff_vnth; intros. auto_vec. destruct (i ??= r).
  - rewrite !vnth_vconsT_n; fin.
  - erewrite !vnth_vconsT_lt; auto_vec. rewrite vnth_vconsH_0; auto.
    Unshelve. fin.
Qed.

(**       [ u1  u2 |  x]
   mheadr  ------- | --  = [u1 u2 x]
          [a11 a12 | v1]
          [a21 a22 | v2]  *)
Lemma mheadr_mconscT_mconsrH_vconsH :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mheadr (mconscT (mconsrH u A) (vconsH x v)) = vconsT u x.
Proof. intros. apply veq_iff_vnth; intros. auto_vec. Qed.

(**       [ u1  u2 |  x]   [ x]
   mtailc  ------------  = [v1]
          [a11 a12 | v1]   [v2]
          [a21 a22 | v2]  *)
Lemma mtailc_mconsrH_vconsT_mconscT :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mtailc (mconsrH (vconsT u x) (mconscT A v)) = vconsH x v.
Proof.
  intros. apply veq_iff_vnth; intros. auto_vec. destruct (i ??= 0).
  - rewrite vnth_vconsH_0. rewrite vnth_vconsT_n; fin. rewrite vnth_vconsH_0; auto.
    all: destruct i; fin.
  - erewrite vnth_vconsH_gt0. auto_vec. rewrite vnth_vconsT_n; fin.
    erewrite vnth_vconsH_gt0. auto. Unshelve. fin.
Qed.

(**       [ x |  u1  u2]
   mheadr  -- | -------  = [x u1 u2]
          [v1 | a11 a12]
          [v2 | a21 a22]  *)
Lemma mheadr_mconscH_vconsH_mconsrH :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mheadr (mconscH (vconsH x v) (mconsrH u A)) = vconsH x u.
Proof. intros. apply veq_iff_vnth; intros. auto_vec. Qed.

(**       [ x |  u1  u2]   [ x]
   mheadc  ------------  = [v1]
          [v1 | a11 a12]   [v2]
          [v2 | a21 a22]  *)
Lemma mheadc_mconsrH_vconsH_mconsrH :
  forall tA r c (A : mat tA r c) (u : @vec tA c) (v : @vec tA r) (x : tA),
    mheadc (mconsrH (vconsH x u) (mconscH v A)) = vconsH x v.
Proof. intros. apply veq_iff_vnth; intros. auto_vec. unfold vconsH. fin. Qed.

Section test.
  Let a : @vec nat 2 := l2v 9 [1;2].
  Let M : @mat nat 2 2 := l2m 9 [[3;4];[5;6]].
  (* Compute m2l (mconsrH a M). *)
  (* Compute m2l (mconsrT M a). *)
  (* Compute m2l (mconscH a M). *)
  (* Compute m2l (mconscT M a). *)
End test.


(* ======================================================================= *)
(** ** Remove one row at head or tail *)

(** Remove head row *)
Definition mremoverH {tA r c} (M : @mat tA (S r) c) : @mat tA r c := vremoveH M.
#[export] Hint Unfold mremoverH : vec.

(** Remove tail row *)
Definition mremoverT {tA r c} (M : @mat tA (S r) c) : @mat tA r c := vremoveT M.
#[export] Hint Unfold mremoverT : vec.

(** mremoverH (mconsrH A v) = A *)
Lemma mremoverH_mconsrH : forall tA r c (A : @mat tA r c) (v : vec c),
    mremoverH (mconsrH v A) = A.
Proof. intros. unfold mremoverH, mconsrH. rewrite vremoveH_vconsH; auto. Qed.

(** mremoverT (mconsrT A v) = A *)
Lemma mremoverT_mconsrT : forall tA r c (A : @mat tA r c) (v : vec c),
    mremoverT (mconsrT A v) = A.
Proof. intros. unfold mremoverT, mconsrT. rewrite vremoveT_vconsT; auto. Qed.


(* ======================================================================= *)
(** ** Remove one column at head or tail *)

(** Remove head column *)
Definition mremovecH {tA r c} (M : @mat tA r (S c)) : @mat tA r c := vmap vremoveH M.
#[export] Hint Unfold mremovecH : vec.

(** Remove tail column *)
Definition mremovecT {tA r c} (M : @mat tA r (S c)) : @mat tA r c := vmap vremoveT M.
#[export] Hint Unfold mremovecT : vec.

(** mremovecH (mconscH A v) = A *)
Lemma mremovecH_mconscH : forall tA r c (A : @mat tA r c) (v : vec r),
    mremovecH (mconscH v A) = A.
Proof.
  intros. unfold mremovecH, mconscH. apply meq_iff_mnth; intros.
  auto_vec. rewrite vnth_vremoveH. erewrite vnth_vconsH_gt0; auto. fin.
  Unshelve. fin.
Qed.

(** mremovecT (mconscT A v) = A *)
Lemma mremovecT_mconscT : forall tA r c (A : @mat tA r c) (v : vec r),
    mremovecT (mconscT A v) = A.
Proof.
  intros. unfold mremovecT, mconscT. apply meq_iff_mnth; intros.
  auto_vec. rewrite vnth_vremoveT. erewrite vnth_vconsT_lt; auto. fin.
  Unshelve. fin.
Qed.

(** mremoverT (mremovecT A) = mremovecT (mremoverT A) *)
Lemma mremoverT_mremovecT_eq_mremovecT_mremoverT : forall tA r c (A : mat tA (S r) (S c)),
    mremoverT (mremovecT A) = mremovecT (mremoverT A).
Proof. intros. apply meq_iff_mnth; intros. auto_vec. Qed.


(* ======================================================================= *)
(** ** Equality of the matrices created by mcons{r|c}{H|T} and vcons{H|T} *)
Section equality_mcons_vcons.
  Context {tA : Type}.
  Notation mat r c := (mat tA r c).

  (**     [a11 a12 a13]
      A = ------------
          [a21 a22 a23]
          [a31 a32 a33] *)
  Lemma meq_mconsrH_mheadr_mremoverH : forall {r c} (A : mat (S r) c),
      A = mconsrH (mheadr A) (mremoverH A).
  Proof.
    intros. apply meq_iff_mnth; intros i j. destruct (fin2nat i ??= 0).
    - replace i with (@fin0 r); auto. destruct i; fin.
    - auto_vec. erewrite vnth_vconsH_gt0. rewrite vnth_vremoveH. fin.
      Unshelve. fin.
  Qed.

  (**     [a11 a12 a13]
      A = [a21 a22 a23]
          ------------
          [a31 a32 a33] *)
  Lemma meq_mconsrT_mremoverT_mtailr : forall {r c} (A : mat (S r) c),
      A = mconsrT (mremoverT A) (mtailr A).
  Proof.
    intros. apply meq_iff_mnth; intros i j. auto_vec. destruct (fin2nat i ??= r).
    - rewrite vnth_vconsT_n; auto. unfold vtail. f_equal. fin.
    - erewrite vnth_vconsT_lt; auto. rewrite vnth_vremoveT. fin.
      Unshelve. pose proof (fin2nat_lt i). fin.
  Qed.

  (**     [a11 | a12 a13]
      A = [a21 | a22 a23]
          [a31 | a32 a33] *)
  Lemma meq_mconscH_mheadc_mremovecH : forall {r c} (A : mat r (S c)),
      A = mconscH (mheadc A) (mremovecH A).
  Proof.
    intros. apply meq_iff_mnth; intros i j.
    auto_vec. destruct (fin2nat j ??= 0).
    - rewrite vnth_vconsH_0; fin. unfold vhead. f_equal. all: destruct j; fin.
    - erewrite vnth_vconsH_gt0. rewrite vnth_vremoveH. fin.
      Unshelve. fin.
  Qed.

  (**     [a11 a12 | a13]
      A = [a21 a22 | a23]
          [a31 a32 | a33] *)
  Lemma meq_mconscT_mremovecT_mtailc : forall {r c} (A : mat r (S c)),
      A = mconscT (mremovecT A) (mtailc A).
  Proof.
    intros. apply meq_iff_mnth; intros i j. auto_vec. destruct (fin2nat j ??= c).
    - rewrite vnth_vconsT_n; auto. f_equal. fin.
    - erewrite vnth_vconsT_lt. rewrite vnth_vremoveT. fin.
      Unshelve. pose proof (fin2nat_lt j). fin.
  Qed.


  (** [A11 A12 | u1]   [A11 A12 | u1]
      [A21 A22 | u2] = [A21 A22 | u2]
      [------- | --]   [------------]
      [ v1  v2 |  x]   [ v1  v2 |  x] *)
  Lemma mconscT_mconsrT_vconsT_eq_mconsrT_mconscT_vconsT :
    forall {r c} (A : mat r c) (u : vec r) (v : vec c) (x : tA),
      mconscT (mconsrT A v) (vconsT u x) = mconsrT (mconscT A u) (vconsT v x).
  Proof.
    intros. auto_vec.
    apply meq_iff_mnth; intros. auto_vec.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat i ??= r), (fin2nat j ??= c).
    - rewrite !vnth_vconsT_n; auto.
    - rewrite (vnth_vconsT_n _ _ i); auto.
      assert (j < c) by fin. rewrite !vnth_vconsT_lt with (H:=H1).
      rewrite vnth_vconsT_n; auto. rewrite vnth_vconsT_lt with (H:=H1). auto.
    - rewrite (vnth_vconsT_n _ _ j); auto.
      assert (i < r) by fin. rewrite !vnth_vconsT_lt with (H:=H1).
      rewrite vnth_vmap2. rewrite vnth_vconsT_n; auto.
    - assert (i < r) by fin. assert (j < c) by fin.
      rewrite !vnth_vconsT_lt with (H:=H1). rewrite vnth_vmap2. auto.
  Qed.

  (** [u1 | A11 A12]   [u1 | A11 A12]
      [u2 | A21 A22] = [u2 | A21 A22]
      [-- | -------]   [------------]
      [ x |  v1  v2]   [ x |  v1  v2] *)
  Lemma mconscH_vconsT_mconsrT_eq_mconsrT_mconscH_vconsH :
    forall {r c} (A : mat r c) (u : vec r) (v : vec c) (x : tA),
      mconscH (vconsT u x) (mconsrT A v) = mconsrT (mconscH u A) (vconsH x v).
  Proof.
    intros. apply meq_iff_mnth; intros. auto_vec.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat i ??= r), (fin2nat j ??= 0).
    - rewrite !vnth_vconsH_0. rewrite !vnth_vconsT_n; auto.
      rewrite vnth_vconsH_0; auto. all: destruct j; fin.
    - rewrite !vnth_vconsT_n; auto.
    - rewrite !vnth_vconsH_0; auto.
      assert (i < r) by fin. rewrite !vnth_vconsT_lt with (H:=H1).
      replace j with (@fin0 c); fin. all: destruct j; fin.
    - assert (i < r) by fin. assert (0 < j) by fin.
      rewrite vnth_vconsH_gt0 with (H:=H2). rewrite !vnth_vconsT_lt with (H:=H1).
      rewrite vnth_vmap2. erewrite vnth_vconsH_gt0. auto.
  Qed.

  (** [ v1  v2 |  x]   [ v1  v2 |  x] 
      [------- | --] = [------------]
      [A11 A12 | u1]   [A11 A12 | u1]
      [A21 A22 | u2]   [A21 A22 | u2] *)
  Lemma mconscT_mconsrH_vconsH_eq_mconsrH_vconsT_mconscT :
    forall {r c} (A : mat r c) (u : vec r) (v : vec c) (x : tA),
      mconscT (mconsrH v A) (vconsH x u) = mconsrH (vconsT v x) (mconscT A u).
  Proof.
    intros. apply meq_iff_mnth; intros. auto_vec.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat i ??= 0), (fin2nat j ??= c).
    - rewrite !vnth_vconsH_0. rewrite !vnth_vconsT_n; auto.
      all: destruct i; fin.
    - assert (j < c) by fin. rewrite !vnth_vconsT_lt with (H:=H1).
      replace i with (@fin0 r); fin. rewrite !vnth_vconsH_0; auto.
      rewrite vnth_vconsT_lt with (H:=H1); auto. destruct i; fin.
    - rewrite !vnth_vconsT_n; auto.
      assert (0 < i) by fin. rewrite !vnth_vconsH_gt0 with (H:=H1).
      rewrite vnth_vmap2; auto. rewrite vnth_vconsT_n; auto.
    - assert (j < c) by fin. rewrite !vnth_vconsT_lt with (H:=H1).
      assert (0 < i) by fin. rewrite !vnth_vconsH_gt0 with (H:=H2).
      rewrite vnth_vmap2. erewrite vnth_vconsT_lt. auto.
  Qed.

  (** [ x |  v1  v2]   [ x |  v1  v2]
      [-- | -------] = [------------]
      [u1 | A11 A12]   [u1 | A11 A12]
      [u2 | A21 A22]   [u2 | A21 A22] *)
  Lemma mconscH_vconsH_mconsrH_eq_mconsrH_vconsH_mconscH :
    forall {r c} (A : mat r c) (u : vec r) (v : vec c) (x : tA),
      mconscH (vconsH x u) (mconsrH v A) = mconsrH (vconsH x v) (mconscH u A).
  Proof.
    intros. apply meq_iff_mnth; intros. auto_vec.
    pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
    destruct (fin2nat i ??= 0), (fin2nat j ??= 0).
    - rewrite !vnth_vconsH_0; auto. all: try destruct i,j; fin.
    - assert (0 < j) by fin. rewrite !vnth_vconsH_gt0 with (H:=H1).
      replace i with (@fin0 r); fin. rewrite vnth_vconsH_0; auto.
      rewrite vnth_vconsH_0; auto. rewrite vnth_vconsH_gt0 with (H:=H1); auto.
      destruct i; fin.
    - replace j with (@fin0 c); fin. rewrite vnth_vconsH_0; auto.
      assert (0 < i) by fin. rewrite !vnth_vconsH_gt0 with (H:=H1).
      rewrite vnth_vmap2. rewrite vnth_vconsH_0; auto. destruct j; fin.
    - assert (0 < i) by fin. assert (0 < j) by fin.
      rewrite !vnth_vconsH_gt0 with (H:=H1).
      rewrite !vnth_vconsH_gt0 with (H:=H2).
      rewrite vnth_vmap2. erewrite vnth_vconsH_gt0; auto.
  Qed.

End equality_mcons_vcons.


(* ======================================================================= *)
(** ** matrix column shift *)
Section mcsh.
  Context {tA} (Azero : tA).

  (** left shift column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;0];[5;6;0];[8;9;0] *)
  Definition mcshl {r c} (M : mat tA r c) (k : 'I_c) : mat tA r c :=
    fun i j =>
      if (fin2nat j + fin2nat k ??< c)%nat
      then M.[i].[fSameRangeAdd j k]
      else Azero.

  (** right shift column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[0;1;2];[0;4;5];[0;7;8] *)
  Definition mcshr {r c} (M : mat tA r c) (k : 'I_c) : mat tA r c :=
    fun i j =>
      if (fin2nat k ??<= fin2nat j)%nat
      then M.[i].[fSameRangeSub j k]
      else Azero.

  (** loop shift left of column. *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[2;3;1];[5;6;4];[8;9;7] *)
  Definition mclsl {r c} (M : @mat tA r c) (k : 'I_c) : @mat tA r c :=
    fun i j => M.[i].[fSameRangeLSL j k].

  (** loop shift right of column *)
  (* [[1;2;3];[4;5;6];[7;8;9] ==1==> [[3;1;2];[6;4;5];[9;7;8] *)
  Definition mclsr {r c} (M : @mat tA r c) (k : 'I_c) : @mat tA r c :=
    fun i j => M.[i].[fSameRangeLSR j k].

End mcsh.

Section test.
  Let M := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute @nat2finS 2 3. *)
  (* Compute m2l (mcshl 0 M (nat2finS 0)). *)
  (* Compute m2l (mcshl 0 M (nat2finS 1)). *)
  (* 移动次数最大是 c - 1 次，若需要更多，则可以多次进行 *)
  (* Compute m2l (mcshl 0 (mcshl 0 M (nat2finS 2)) (nat2finS 1)). *)
  
  (* Compute m2l (mcshr 0 M (nat2finS 1)). *)
  
  (* Compute m2l (mclsl M (nat2finS 1)). *)
  (* Compute m2l (mclsr M (nat2finS 1)). *)
End test.


(* ######################################################################### *)
(** * Algebraic operations *)

(* ======================================================================= *)
(** ** Matrix Addition *)
Section madd.
  Context `{AMonoid}.
  Notation mat r c := (mat tA r c).
  Infix "+" := Aadd : A_scope.
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope. 
  Notation mat0 := (@mat0 _ Azero).
  
  Definition madd {r c} (M N : mat r c) : mat r c := mmap2 Aadd M N.
  (* Definition madd' {r c} (M N : mat r c) : mat r c := vmap2 vadd M N. *)
  Infix "+" := madd : mat_scope.
  
  (** (M+N)[i,j] = M[i,j] + N[i,j] *)
  Lemma mnth_madd : forall {r c} (M N : mat r c) i j,
      (M + N).[i].[j] = (M.[i].[j] + N.[i].[j])%A.
  Proof. intros. auto. Qed.
  
  (** (M+N)[i] = M[i] + N[i] *)
  Lemma vnth_madd : forall {r c} (M N : mat r c) i,
      (M + N).[i] = (M.[i] + N.[i])%V.
  Proof. intros. auto. Qed.

  (** (M+N)&i = M&i + N&i *)
  Lemma mcol_madd : forall {r c} (M N : mat r c) i,
      (M + N)&[i] = (M&[i] + N&[i])%V.
  Proof. intros. auto. Qed.

  Lemma cv2v_madd : forall {n} (a b : cvec tA n),
      cv2v (a + b) = (cv2v a + cv2v b)%V.
  Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.
  
  Lemma madd_assoc : forall {r c} (M N O : mat r c),
      (M + N) + O = M + (N + O).
  Proof. intros. apply mmap2_assoc. Qed.

  Lemma madd_comm : forall {r c} (M N : mat r c), M + N = N + M.
  Proof. intros. apply mmap2_comm. Qed.

  (** 0 + M = M *)
  Lemma madd_0_l : forall {r c} (M : mat r c), mat0 + M = M.
  Proof.
    intros. unfold madd. apply meq_iff_mnth; intros.
    rewrite mnth_mmap2. rewrite mnth_mat0. amonoid.
  Qed.

  (** M + 0 = M *)
  Lemma madd_0_r : forall {r c} (M : mat r c), M + mat0 = M.
  Proof. intros. rewrite madd_comm, madd_0_l; auto. Qed.
  
  Instance madd_Associative : forall r c, @Associative (mat r c) madd.
  Proof. intros. constructor. apply madd_assoc. Qed.

  Instance madd_Commutative : forall r c, @Commutative (mat r c) madd.
  Proof. intros. constructor. apply madd_comm. Qed.

  Instance madd_IdentityLeft : forall r c, @IdentityLeft (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_l. Qed.

  Instance madd_IdentityRight : forall r c, @IdentityRight (mat r c) madd mat0.
  Proof. intros. constructor. apply madd_0_r. Qed.

  Instance madd_AMonoid : forall r c, AMonoid (@madd r c) mat0.
  Proof.
    intros. repeat constructor; intros;
      try apply associative;
      try apply commutative;
      try apply identityLeft;
      try apply identityRight.
  Qed.
  
  (** (M + N) + O = (M + O) + N *)
  Lemma madd_perm : forall {r c} (M N O : mat r c), (M + N) + O = (M + O) + N.
  Proof. intros. pose proof(madd_AMonoid r c). amonoid. Qed.

  (** (M + N)\T = M\T + N\T *)
  Lemma mtrans_madd : forall {r c} (M N : mat r c), (M + N)\T = M\T + N\T.
  Proof.
    (* intros. unfold madd. apply meq_iff_mnth; intros. *)
    (* rewrite ?mnth_mtrans, ?mnth_mmap2, ?mnth_mtrans. auto. *)
    auto.
  Qed.
End madd.


(* ======================================================================= *)
(** ** Matrix Trace *)
Section mtrace.
  Context `{AMonoid}.
  Notation smat n := (smat tA n).
  Notation vsum := (@vsum _ Aadd Azero).
  Infix "+" := Aadd : A_scope.
  Notation madd := (@madd _ Aadd).
  Infix "+" := madd : mat_scope.
  
  Definition mtrace {n : nat} (M : smat n) : tA := vsum (fun i => M.[i].[i]).
  Notation "'tr' M" := (mtrace M).

  (** tr(M\T) = tr(M) *)
  Lemma mtrace_mtrans : forall {n} (M : smat n), tr (M\T) = tr M.
  Proof. intros. apply vsum_eq; intros. apply mnth_mtrans. Qed.

  (** tr(M + N) = tr(M) + tr(N) *)
  Lemma mtrace_madd : forall {n} (M N : smat n), tr (M + N) = (tr M + tr N)%A.
  Proof.
    intros. unfold madd, mtrace. rewrite vsum_add; intros.
    apply vsum_eq; intros. rewrite mnth_mmap2. auto.
  Qed.
End mtrace.


(* addition,opposition,subtraction, scalar multiplication, multiplication *)
Section malg.

  Context `{HAGroup : AGroup}.
  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b)).
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vsum := (@vsum _ Aadd Azero).
  Notation vadd := (@vadd _ Aadd).
  Infix "+" := vadd : vec_scope.
  
  Notation mat r c := (mat tA r c).
  Notation smat n := (smat tA n).
  Notation mat0 := (@mat0 _ Azero).
  Notation madd := (@madd _ Aadd).
  Notation mtrace := (@mtrace _ Aadd 0 _).
  Infix "+" := madd : mat_scope.
  Notation "'tr' M" := (mtrace M).
  
  (* ======================================================================= *)
  (** ** Matrix Opposition *)
  Section mopp.
    Notation vopp := (@vopp _ Aopp).
    Notation "- v" := (vopp v) : vec_scope.
    
    Definition mopp {r c} (M : mat r c) : mat r c := mmap Aopp M.
    Notation "- M" := (mopp M) : mat_scope.
    
    (** (- M)[i] = - M[i] *)
    Lemma vnth_mopp : forall {r c} (M : mat r c) i, (- M).[i] = (- (M.[i]))%V.
    Proof. intros. auto. Qed.

    (** (- M)&i = - (M&i) *)
    Lemma mcol_mopp : forall {r c} (M : mat r c) i, (- M)&[i] = (- M&[i])%V.
    Proof. intros. auto. Qed.
    
    (** (- M)[i, j] = - M[i, j] *)
    Lemma mnth_mopp : forall {r c} (M : mat r c) i j, (- M).[i].[j] = (- M.[i].[j])%A.
    Proof. intros. auto. Qed.
    
    Lemma madd_opp_l : forall {r c} (M : mat r c), (- M) + M = mat0.
    Proof.
      intros. unfold madd,mopp,mat0,mmap2,mmap. apply meq_iff_mnth; intros. agroup.
    Qed.
    
    Lemma madd_opp_r : forall {r c} (M : mat r c), M + (- M) = mat0.
    Proof. intros. rewrite madd_comm. apply madd_opp_l. Qed.

    Instance madd_InverseLeft : forall r c, @InverseLeft (mat r c) madd mat0 mopp.
    Proof. intros. constructor. apply madd_opp_l. Qed.

    Instance madd_InverseRight : forall r c, @InverseRight (mat r c) madd mat0 mopp.
    Proof. intros. constructor. apply madd_opp_r. Qed.

    Instance madd_AGroup : forall r c, @AGroup (mat r c) madd mat0 mopp.
    Proof.
      intros. repeat constructor;
        try apply associative;
        try apply identityLeft;
        try apply identityRight;
        try apply inverseLeft;
        try apply inverseRight;
        try apply commutative.
    Qed.

    (* Now, we ca use group theory on <madd, mat0, mopp, msub> *)

    (* Tips: a good example for `group` tactic *)
    Example madd_agroup_example1 : forall r c (M N : mat r c), mat0 + M + (- N) + N = M.
    Proof.
      intros. pose proof (madd_AGroup r c).
      (* rewrite associative. *)
      (* rewrite inverseLeft. *)
      (* rewrite identityRight. *)
      (* rewrite identityLeft. *)
      agroup.
    Qed.
    
    (** - (- M) = M *)
    Lemma mopp_mopp : forall {r c} (M : mat r c), - (- M) = M.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** - M = N <-> M = - N *)
    Lemma mopp_exchange : forall {r c} (M N : mat r c), - M = N <-> M = - N.
    Proof. intros. pose proof (madd_AGroup r c). split; intros; agroup. Qed.

    (** - (mat0) = mat0 *)
    Lemma mopp_mat0 : forall {r c:nat}, - (@Matrix.mat0 _ 0 r c) = mat0.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** - (m1 + m2) = (-m1) + (-m2) *)
    Lemma mopp_madd : forall {r c : nat} (M N : mat r c), - (M + N) = (- M) + (- N).
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** (- M)\T = - (M\T) *)
    Lemma mtrans_mopp : forall {r c} (M : mat r c), (- M)\T = - (M\T).
    Proof. auto. Qed.

    (** tr(- M) = - (tr(m)) *)
    Lemma mtrace_mopp : forall {n} (M : smat n), tr (- M) = (- (tr M))%A.
    Proof.
      intros. unfold mopp, mtrace. rewrite vsum_opp; intros.
      apply vsum_eq; intros. rewrite !vnth_vmap; auto.
    Qed.
  End mopp.
  Notation "- M" := (mopp M) : mat_scope.
  
  (* ======================================================================= *)
  (** ** Matrix Subtraction *)
  Section msub.
    Notation msub M N := (M + (- N)).
    Infix "-" := msub : mat_scope.
    (* Definition msub {r c} (M N : mat r c) : mat r c := M + (- N). *)

    (** M - N = - (N - M) *)
    Lemma msub_comm : forall {r c} (M N : mat r c), M - N = - (N - M).
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** (M - N) - O = M - (N + O) *)
    Lemma msub_assoc : forall {r c} (M N O : mat r c),
        (M - N) - O = M - (N + O).
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** (M + N) - O = M + (N - O) *)
    Lemma msub_assoc1 : forall {r c} (M N O : mat r c), (M + N) - O = M + (N - O).
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** (M - N) - O = M - (O - N) *)
    Lemma msub_assoc2 : forall {r c} (M N O : mat r c), (M - N) - O = (M - O) - N.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.
    
    (** 0 - M = - M *)
    Lemma msub_0_l : forall {r c} (M : mat r c), mat0 - M = - M.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.
    
    (** M - 0 = M *)
    Lemma msub_0_r : forall {r c} (M : mat r c), M - mat0 = M.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.
    
    (** M - M = 0 *)
    Lemma msub_self : forall {r c} (M : mat r c), M - M = mat0.
    Proof. intros. pose proof (madd_AGroup r c). agroup. Qed.

    (** (M - N)\T = M\T - N\T *)
    Lemma mtrans_msub : forall {r c} (M N : mat r c), (M - N)\T = M\T - N\T.
    Proof. auto. Qed.

    (** tr(M - N) = tr(M) - tr(N) *)
    Lemma mtrace_msub : forall {n} (M N : smat n), tr (M - N) = (tr M - tr N)%A.
    Proof. intros. rewrite mtrace_madd, mtrace_mopp; auto. Qed.
  End msub.
  Notation "M - N" := ((M + - N)%M) : mat_scope.


  Context `{HARing : ARing tA Aadd 0 Aopp}.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Add Ring ring_inst : (make_ring_theory HARing).

  Notation vscal := (@vscal _ Amul).
  Infix "s*" := vscal : vec_scope.
  Notation vdot v1 v2 := (@vdot _ Aadd 0 Amul _ v1 v2).
  Notation "< v1 , v2 >" := (vdot v1 v2) : vec_scope.
  
  (* ======================================================================= *)
  (** ** Unit matrix *)
  Section mat1.
    Definition mat1 {n} : smat n := fun i j => if i ??= j then 1 else 0.
    
    (** mat1\T = mat1 *)
    Lemma mtrans_mat1 : forall {n : nat}, (@mat1 n)\T = mat1.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold mtrans,mat1. fin.
    Qed.

    (** mat1[i,i] = 1 *)
    Lemma mnth_mat1_same : forall {n} i, (@mat1 n).[i].[i] = 1.
    Proof. intros. unfold mat1. fin. Qed.

    (** i <> j -> mat1[i,j] = 0 *)
    Lemma mnth_mat1_diff : forall {n} i j, i <> j -> (@mat1 n).[i].[j] = 0.
    Proof. intros. unfold mat1. fin. Qed.

    (** mat1 is diagonal matrix *)
    Lemma mat1_diag : forall {n : nat}, mdiag 0 (@mat1 n).
    Proof. intros. hnf. intros. rewrite mnth_mat1_diff; auto. Qed.

    (** [1 0 0 | 0]   [1 0 0 0]
        [0 1 0 | 0]   [0 1 0 0]
        [0 0 1 | 0] = [0 0 1 0]
        [----  | -]   [0 0 0 1]
        [0 0 0 | 1] *)
    Lemma mat1_eq_mconscT_mconsrT_vconsT : forall {n},
        @mat1 (S n) = mconscT (mconsrT mat1 vzero) (vconsT vzero 1).
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec.
      unfold vconsT. fin; try rewrite vnth_vzero.
      - rewrite mnth_mat1_diff; auto.
        assert (fin2nat i <> fin2nat j) by lia. apply fin2nat_neq_iff in H; auto.
      - rewrite mnth_mat1_diff; auto.
        assert (fin2nat i <> fin2nat j) by lia. apply fin2nat_neq_iff in H; auto.
      - pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
        assert (fin2nat i = fin2nat j) by lia. apply fin2nat_eq_iff in H1.
        subst. rewrite mnth_mat1_same. auto.
    Qed.

    (** [1 0 0 | 0]   [1 0 0 0]
        [0 1 0 | 0]   [0 1 0 0]
        [0 0 1 | 0] = [0 0 1 0]
        [---------]   [0 0 0 1]
        [0 0 0 | 1] *)
    Lemma mat1_eq_mconsrT_mconscT_vconsT : forall {n},
        @mat1 (S n) = mconsrT (mconscT mat1 vzero) (vconsT vzero 1).
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec.
      unfold vconsT. unfold vmap2. fin; try rewrite vnth_vzero.
      - rewrite mnth_mat1_diff; auto.
        assert (fin2nat i <> fin2nat j) by lia. apply fin2nat_neq_iff in H; auto.
      - rewrite mnth_mat1_diff; auto.
        assert (fin2nat i <> fin2nat j) by lia. apply fin2nat_neq_iff in H; auto.
      - pose proof (fin2nat_lt i). pose proof (fin2nat_lt j).
        assert (fin2nat i = fin2nat j) by lia. apply fin2nat_eq_iff in H1.
        subst. rewrite mnth_mat1_same. auto.
    Qed.

    (** [a11 a12 | u1]
        [a21 a22 | u2]          [a11 a12]        [u1]        [v1]
        ---- ---------  = I <=> [a21 a22] = I /\ [u2] = 0 /\ [v1] = 0 /\ x = 1
        [ v1  v2 |  x] *)
    Lemma mconsrT_mconscT_vconsT_imply_mat1 : forall n (A : smat n) (u v : vec n) x,
        A = mat1 -> u = vzero -> v = vzero -> x = 1 ->
        mconsrT (mconscT A u) (vconsT v x) = mat1.
    Proof. intros. subst. rewrite <- mat1_eq_mconsrT_mconscT_vconsT. auto. Qed.

    Lemma mtailr_mat1 : forall {n}, mtailr (@mat1 (S n)) = vconsT vzero 1.
    Proof.
      intros. apply veq_iff_vnth; intros. auto_vec. unfold mat1. fin.
      rewrite vnth_vconsT_n; auto. erewrite vnth_vconsT_lt; fin.
      Unshelve. pose proof (fin2nat_lt i). lia.
    Qed.

    Lemma mtailc_mat1 : forall {n}, mtailc (@mat1 (S n)) = vconsT vzero 1.
    Proof.
      intros. apply veq_iff_vnth; intros. auto_vec. unfold mat1. fin.
      rewrite vnth_vconsT_n; auto. erewrite vnth_vconsT_lt; fin.
      Unshelve. pose proof (fin2nat_lt i). lia.
    Qed.

    Lemma mremoverT_mremovecT_mat1 : forall {n},
        mremoverT (mremovecT (@mat1 (S n))) = mat1.
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec. unfold vremoveT. auto_vec.
      destruct (i ??= j) as [Hij | Hij].
      - fin2nat. rewrite !mnth_mat1_same. auto.
      - rewrite !mnth_mat1_diff; fin. intro. destruct Hij. fin.
    Qed.

    Lemma mremovecT_mremoverT_mat1 : forall {n},
        mremovecT (mremoverT (@mat1 (S n))) = mat1.
    Proof.
      intros. rewrite <- mremoverT_mremovecT_eq_mremovecT_mremoverT.
      apply mremoverT_mremovecT_mat1.
    Qed.

    Lemma mtailc_mremoverT_mat1 : forall {n}, mtailc (mremoverT (@mat1 (S n))) = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. auto_vec. rewrite vnth_vremoveT.
      unfold mat1. unfold fSuccRange, nat2finS. fin.
      all: destruct i; fin.
    Qed.

    Lemma mtailr_mremovecT_mat1 : forall {n}, mtailr (mremovecT (@mat1 (S n))) = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. auto_vec. rewrite vnth_vremoveT.
      unfold mat1. unfold fSuccRange, nat2finS. fin.
      all: destruct i; fin.
    Qed.
      
  End mat1.

  
  (* ======================================================================= *)
  (** ** Matrix Scalar Multiplication *)
  Section mscal.
    Definition mscal {r c : nat} (a : tA) (M : mat r c) : mat r c := mmap (Amul a) M.
    Infix "s*" := mscal : mat_scope.

    (** (a * M)[i] = a * M[i] *)
    Lemma vnth_mscal : forall {r c} (M : mat r c) a i,
        (a s* M).[i] = (a s* (M.[i]))%V.
    Proof. intros. auto. Qed.

    (** (a * M)&i = a * M&i *)
    Lemma mcol_mscal : forall {r c} (M : mat r c) a i,
        (a s* M)&[i] = (a s* M&[i])%V.
    Proof. intros. auto. Qed.

    (** (a * M)[i,j] = a * M[i,j] *)
    Lemma mnth_mscal : forall r c (M : mat r c) a i j,
        (a s* M).[i].[j] = a * (M.[i].[j]).
    Proof. intros. unfold mscal. rewrite !vnth_vmap. auto. Qed.
    Hint Rewrite mnth_mscal : vec.

    Lemma cv2v_mscal : forall {n} (x : tA) (a : cvec tA n),
        cv2v (x s* a) = (x s* (cv2v a))%V.
    Proof. intros. apply veq_iff_vnth; intros. cbv. auto. Qed.

    (** x s* (mconsrH v A) = mconsrH (x s* v)%V (x s* A) *)
    Lemma mscal_mconsrH : forall {r c} (v : vec c) (A : mat r c) x,
        x s* (mconsrH v A) = mconsrH (x s* v)%V (x s* A).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mscal.
      unfold mconsrH. bdestruct (i =? 0).
      - rewrite !vnth_vconsH_0; auto. all: destruct i; fin.
      - erewrite !vnth_vconsH_gt0. easy. Unshelve. fin.
    Qed.

    (** x s* (mconsrT A v) = mconsrT (x s* A) (x s* v)%V *)
    Lemma mscal_mconsrT : forall {r c} (A : mat r c) (v : vec c) x,
        x s* (mconsrT A v) = mconsrT (x s* A) (x s* v)%V.
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec. bdestruct (i =? r).
      - rewrite !vnth_vconsT_n; auto.
      - erewrite !vnth_vconsT_lt. easy. Unshelve. fin.
    Qed.

    (** x s* (mconscH v A) = mconscH (x s* v)%V (x s* A) *)
    Lemma mscal_mconscH : forall {r c} (v : vec r) (A : mat r c) x,
        x s* (mconscH v A) = mconscH (x s* v)%V (x s* A).
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec. bdestruct (j =? 0).
      - rewrite !vnth_vconsH_0; auto. all: destruct j; fin.
      - erewrite !vnth_vconsH_gt0. easy. Unshelve. fin.
    Qed.

    (** x s* (mconscT A v) = mconscT (x s* A) (x s* v)%V *)
    Lemma mscal_mconscT : forall {r c} (A : mat r c) (v : vec r) x,
        x s* (mconscT A v) = mconscT (x s* A) (x s* v)%V.
    Proof.
      intros. apply meq_iff_mnth; intros. auto_vec. bdestruct (j =? c).
      - rewrite !vnth_vconsT_n; auto.
      - erewrite !vnth_vconsT_lt. easy. Unshelve. fin.
    Qed.

    (** a * (b * M) = (a * b) * M *)
    Lemma mscal_assoc : forall {r c} (M : mat r c) a b,
        a s* (b s* M) = (a * b)%A s* M.
    Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mscal. agroup. Qed.
    
    (** a * (b * M) = b * (a * M) *)
    Lemma mscal_perm : forall {r c} (M : mat r c) a b,
        a s* (b s* M) = b s* (a s* M).
    Proof. intros. rewrite !mscal_assoc. f_equal. ring. Qed.

    (** a * (M + N) = (a * M) + (a * N) *)
    Lemma mscal_madd_distr : forall {r c} a (M N : mat r c),
        a s* (M + N) = (a s* M) + (a s* N).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mscal, !mnth_madd, !mnth_mscal. ring.
    Qed.
    
    (** (a + b) * M = (a * M) + (b * M) *)
    Lemma mscal_add_distr : forall {r c} a b (M : mat r c),
        (a + b)%A s* M = (a s* M) + (b s* M).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mscal, !mnth_madd, !mnth_mscal. ring.
    Qed.

    (* 0 s* M = mat0 *)
    Lemma mscal_0_l : forall {r c} (M : mat r c), 0 s* M = mat0.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mscal, !mnth_mat0. ring.
    Qed.

    (** a s* mat0 = mat0 *)
    Lemma mscal_0_r : forall {r c} a, a s* (@Matrix.mat0 _ 0 r c) = mat0.
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite !mnth_mscal, !mnth_mat0. ring.
    Qed.
    
    (** 1 s* M = M *)
    Lemma mscal_1_l : forall {r c} (M : mat r c), 1 s* M = M.
    Proof. intros. apply meq_iff_mnth; intros. rewrite !mnth_mscal. ring. Qed.

    (** a s* mat1 = mdiag([a,a,...]) *)
    Lemma mscal_1_r : forall {n} a, a s* (@mat1 n) = mdiagMk 0 (vrepeat a).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mscal.
      destruct (i ??= j) as [E|E]; fin.
      - apply fin2nat_eq_iff in E; rewrite E.
        rewrite mnth_mdiagMk_same. rewrite mnth_mat1_same, vnth_vrepeat. ring.
      - apply fin2nat_neq_iff in E.
        rewrite mnth_mat1_diff, mnth_mdiagMk_diff; auto. ring.
    Qed.
    
    (* (-a) * M = - (a * M) *)
    Lemma mscal_opp : forall {r c} a (M : mat r c), (- a)%A s* M = - (a s* M).
    Proof.
      intros. apply meq_iff_mnth; intros. rewrite mnth_mopp,!mnth_mscal. ring.
    Qed.
    
    (* a * (- M) = - (a * M) *)
    Lemma mscal_mopp : forall {r c} a (M : mat r c), a s* (- M) = - (a s* M).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite !mnth_mopp,!mnth_mscal,mnth_mopp. ring.
    Qed.
    
    (* (-a) * (- M) = a * M *)
    Lemma mscal_opp_mopp : forall {r c} a (M : mat r c),
        (- a)%A s* (- M) = a s* M.
    Proof. intros. rewrite mscal_mopp, mscal_opp. apply group_opp_opp. Qed.

    (** a s* (M - N) = (a s* M) - (a s* N) *)
    Lemma mscal_msub : forall {r c} a (M N : mat r c),
        a s* (M - N) = (a s* M) - (a s* N).
    Proof. intros. rewrite mscal_madd_distr. rewrite mscal_mopp. auto. Qed.

    (** (a s* M)\T = a s* (m\T) *)
    Lemma mtrans_mscal : forall {r c} (a : tA) (M : mat r c), (a s* M)\T = a s* (M\T).
    Proof.
      intros. apply meq_iff_mnth; intros.
      rewrite mnth_mtrans, !mnth_mscal, mnth_mtrans. auto.
    Qed.

    (** tr (a s* M) = a * tr (m) *)
    Lemma mtrace_mscal : forall {n} (a : tA) (M : smat n), tr (a s* M) = (a * tr M)%A.
    Proof.
      intros. unfold mscal, mtrace. rewrite vsum_scal_l; intros.
      apply vsum_eq; intros. rewrite mnth_mmap. auto.
    Qed.
  End mscal.
  Infix "s*" := mscal : mat_scope.

  
  (* ======================================================================= *)
  (** ** Matrix Multiplication *)

  (* structural-style *)
  Definition mmul_old {r c t : nat} (M : mat r c) (N : mat c t) : mat r t :=
    vmap (fun v1 => vmap (fun v2 => <v1,v2>) (mtrans N)) M.
  
  (* functional-style *)
  Definition mmul {r c t : nat} (M : mat r c) (N : mat c t) : mat r t :=
    fun i j => <M.[i], (fun k => N.[k].[j])>.
  Infix "*" := mmul : mat_scope.

  (** (M * N)[i,j] = <row M i, col N j> *)
  Lemma mnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i j,
      (M * N).[i].[j] = <M.[i], N&[j]>.
  Proof. intros. auto. Qed.

  (** (M * N)[i] = <row M i, col N j> *)
  Lemma vnth_mmul : forall {r c t} (M : mat r c) (N : mat c t) i,
      (M * N).[i] = vmap (fun v => <M.[i],v>) (N\T).
  Proof. intros. auto. Qed.

  (** N is cvec -> M * N = fun i => <N, M.[i]> *)
  Lemma mmul_cvec : forall {r c} (M : mat r c) (N : cvec tA c),
      M * N = fun i j => <cv2v N, M.[i]>.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold cv2v.
    unfold mmul. rewrite vdot_comm. rewrite (fin1_uniq j). auto.
  Qed.

  (** M is rvec -> M * N = fun i j => <M, N&[j]> *)
  Lemma mmul_rvec : forall {r c} (M : rvec tA r) (N : mat r c),
      M * N = fun i j => <rv2v M, N&[j]>.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold rv2v, mcol.
    unfold mmul. rewrite (fin1_uniq i). auto.
  Qed.

  (** <row(M,i), col(N,j)> = [M * N].ij *)
  Lemma vdot_row_col : forall {r c s} (M : mat r c) (N : mat c s) i j,
      <M.[i], N&[j]> = (M * N).[i].[j].
  Proof. intros. apply vsum_eq; intros; auto. Qed.

  (** <col(M,i), col(N,j)> = (M\T * N)[i,j] *)
  Lemma vdot_col_col : forall {n} (M N : smat n) i j,
      <M&[i], N&[j]> = (M\T * N).[i].[j].
  Proof. intros. apply vsum_eq. intros; auto. Qed.

  (** <row(M,i), row(N,j)> = (M * N\T)[i,j] *)
  Lemma vdot_row_row : forall {n} (M N : smat n) i j,
      <M.[i], N.[j]> = (M * N\T).[i].[j].
  Proof. intros. apply vsum_eq. intros; auto. Qed.

  (** <a, b> = (a\T * b).11 *)
  Lemma vdot_eq_mmul : forall {n} (a b : vec n), <a, b> = (v2rv a * v2cv b).11.
  Proof. intros. apply vsum_eq; intros; auto. Qed.

  (** (M * N) * O = M * (N * O) *)
  Lemma mmul_assoc : forall {m n r s} (M : mat m n) (N : mat n r) (O : mat r s),
      (M * N) * O = M * (N * O).
  Proof. intros. unfold mmul. apply meq_iff_mnth; intros. apply vdot_assoc. Qed.

  (** M * (N + O) = M * N + M * O *)
  Lemma mmul_madd_distr_l : forall {r c t} (M : mat r c) (N O : mat c t),
      M * (N + O) = (M * N) + (M * O).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_madd, !mnth_mmul.
    unfold vdot. rewrite vsum_add. apply vsum_eq; intros k.
    rewrite !vnth_vmap2. rewrite mcol_madd. rewrite vnth_vadd. ring.
  Qed.
  
  (** (M + N) * O = M * O + N * O *)
  Lemma mmul_madd_distr_r : forall {r c t} (M N : mat r c) (O : mat c t),
      (M + N) * O = (M * O) + (N * O).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_madd,!mnth_mmul.
    unfold vdot. rewrite vsum_add; apply vsum_eq; intros k.
    rewrite !vnth_vmap2, mnth_madd. ring.
  Qed.

  (** (- M) * N = - (M * N) *)
  Lemma mmul_mopp_l : forall {r c t} (M : mat r c) (N : mat c t),
      (- M) * N = - (M * N).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
    unfold vdot. rewrite vsum_opp; apply vsum_eq; intros k.
    rewrite !vnth_vmap2, mnth_mopp. ring.
  Qed.

  (** M * (- N) = - (M * N) *)
  Lemma mmul_mopp_r : forall {r c t} (M : mat r c) (N : mat c t),
      M * (- N) = - (M * N).
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite mnth_mopp, !mnth_mmul.
    unfold vdot. rewrite vsum_opp; apply vsum_eq; intros k.
    rewrite !vnth_vmap2. rewrite !vnth_mcol. rewrite mnth_mopp. ring.
  Qed.

  (** M * (N - O) = M * N - M * O *)
  Lemma mmul_msub_distr_l : forall {r c t} (M : mat r c) (N O : mat c t),
      M * (N - O) = (M * N) - (M * O).
  Proof.
    intros. rewrite mmul_madd_distr_l. rewrite mmul_mopp_r. auto.
  Qed.
  
  (** (M - N) * O = M * O - N * O *)
  Lemma mmul_msub_distr_r : forall {r c t} (M N : mat r c) (O : mat c t),
      (M - N) * O = (M * O) - (N * O).
  Proof.
    intros. rewrite mmul_madd_distr_r. rewrite mmul_mopp_l. auto.
  Qed.
  
  (** 0 * M = 0 *)
  Lemma mmul_0_l : forall {r c t} (M : mat c t), mat0 * M = @Matrix.mat0 _ 0 r t.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
    rewrite mrow_mat0. apply vdot_0_l.
  Qed.
  
  (** M * 0 = 0 *)
  Lemma mmul_0_r : forall {r c t} (M : mat r c), M * mat0 = @Matrix.mat0 _ 0 r t.
  Proof.
    intros. apply meq_iff_mnth; intros. rewrite !mnth_mmul, mnth_mat0.
    rewrite mcol_mat0. apply vdot_0_r.
  Qed.
  
  (** 1 * M = M *)
  Lemma mmul_1_l : forall {r c} (M : mat r c), mat1 * M = M.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2.
    apply vsum_unique with (i:=i); fin.
  Qed.
  
  (** M * 1 = M *)
  Lemma mmul_1_r : forall {r c} (M : mat r c), M * mat1 = M.
  Proof.
    intros. apply meq_iff_mnth; intros. unfold mmul,vdot,mat1,vmap2.
    apply vsum_unique with (i:=j); fin.
  Qed.

  (** (a s* M) * N = a s* (M * N) *)
  Lemma mmul_mscal_l : forall {r c s} (a : tA) (M : mat r c) (N : mat c s), 
      (a s* M) * N = a s* (M * N).
  Proof.
    intros. apply meq_iff_mnth; intros.
    repeat rewrite ?mnth_mmul, ?mnth_mscal.
    rewrite vnth_mscal. rewrite vdot_vscal_l. auto.
  Qed.
  
  (** M * (a s* N) = a s* (M * N) *)
  Lemma mmul_mscal_r : forall {r c s} (a : tA) (M : mat r c) (N : mat c s), 
      M * (a s* N) = a s* (M * N).
  Proof.
    intros. apply meq_iff_mnth; intros.
    repeat rewrite ?mnth_mmul, ?mnth_mscal.
    rewrite mcol_mscal. rewrite vdot_vscal_r. auto.
  Qed.

  (** (M * N)\T = N\T * M\T *)
  Lemma mtrans_mmul : forall {r c s} (M : mat r c) (N : mat c s),
      (M * N)\T = N\T * M\T.
  Proof.
    intros. apply meq_iff_mnth; intros.
    rewrite !mnth_mtrans,!mnth_mmul. rewrite vdot_comm. f_equal.
  Qed.

  (** tr (M * N) = tr (N * M) *)
  Lemma mtrace_mmul : forall {r c} (M : mat r c) (N : mat c r),
      tr (M * N) = tr (N * M).
  Proof.
    (* from: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
       tr(A*B) = Σ(A*B)_{ii}
       = ΣΣ(A_{ij} B_{ji}) = ΣΣ(B_{ji} A_{ij}) 
       = Σ(BA)_{jj} = tr(B*A) *)
    intros. unfold mtrace. unfold mmul,vdot,vmap2.
    rewrite vsum_vsum. apply vsum_eq; intros. apply vsum_eq; intros. ring.
  Qed.

  (* tr(ABCD) = tr(BCDA) = tr(CDAB) = tr(DABC) *)
  Lemma mtrace_cyclic4_BCDA :
    forall {r c s t} (A : mat r c) (B : mat c s) (C : mat s t) (D : mat t r),
      tr(A * B * C * D) = tr(B * C * D * A).
  Proof.
    intros. replace (A * B * C * D) with (A * (B * C * D)). apply mtrace_mmul.
    rewrite <- !mmul_assoc. auto.
  Qed.
  
  Lemma mtrace_cyclic4_CDAB :
    forall {r c s t} (A : mat r c) (B : mat c s) (C : mat s t) (D : mat t r),
      tr(A * B * C * D) = tr(C * D * A * B).
  Proof. intros. do 2 rewrite mtrace_cyclic4_BCDA. auto. Qed.
  
  Lemma mtrace_cyclic4_DABC :
    forall {r c s t} (A : mat r c) (B : mat c s) (C : mat s t) (D : mat t r),
      tr(A * B * C * D) = tr(D * A * B * C).
  Proof. intros. do 3 rewrite mtrace_cyclic4_BCDA. auto. Qed.

  (* tr(ABC) = tr(BCA) = tr(CAB) *)
  Lemma mtrace_cyclic3_BCA : forall {n} (A B C : smat n), tr(A * B * C) = tr(B * C * A).
  Proof.
    (* tr(ABC)=tr((ABC)\T))=tr((BC)\T A\T)=tr(A\T (BC)\T)=tr(BCA) *)
    intros. rewrite <- mtrace_mtrans. rewrite mmul_assoc. rewrite mtrans_mmul.
    rewrite mtrace_mmul. rewrite <- mtrans_mmul. apply mtrace_mtrans.
  Qed.

  Lemma mtrace_cyclic3_CAB : forall {n} (A B C : smat n), tr(A * B * C) = tr(C * A * B).
  Proof.
    (* tr(ABC)=tr((ABC)\T))=tr(C\T (AB)\T)=tr((AB)\T C\T)=tr(CAB) *)
    intros. rewrite <- mtrace_mtrans. rewrite mtrans_mmul. rewrite mtrace_mmul.
    rewrite <- mtrans_mmul. rewrite mtrace_mtrans. rewrite mmul_assoc. auto.
  Qed.
  

  (* ======================================================================= *)
  (** ** Matrix multiply vector (column matrix) *)
  Section mmulv.
    Notation vec := (@vec tA).
    Notation vopp := (@vopp _ Aopp).
    Notation "- a" := (vopp a) : vec_scope.
    Notation "a - b" := ((a + -b)%V) : vec_scope.

    Definition mmulv {r c : nat} (M : mat r c) (a : vec c) : vec r :=
      fun i => <M.[i], a>.
    Infix "*v" := mmulv : mat_scope.

    (** (M *v a)[i] = <row M i, a> *)
    Lemma vnth_mmulv : forall {r c} (M : mat r c) (a : vec c) i,
        (M *v a).[i] = <M.[i], a>.
    Proof. intros. auto. Qed.

    (** (M * N) *v a = M *v (N *v a) *)
    Lemma mmulv_assoc : forall {m n r} (M : mat m n) (N : mat n r) (a : vec r),
        (M * N) *v a = M *v (N *v a).
    Proof. intros. unfold mmulv. apply veq_iff_vnth; intros. apply vdot_assoc. Qed.

    (** M *v (a + b) = M *v a + M *v b *)
    Lemma mmulv_vadd : forall {r c} (M : mat r c) (a b : vec c),
        M *v (a + b)%V = (M *v a + M *v b)%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      rewrite vnth_vadd, !vnth_mmulv. unfold vdot. unfold vmap2.
      rewrite vsum_add. apply vsum_eq; intros. rewrite vnth_vadd. ring.
    Qed.
    
    (** (M + N) *v a = M *v a + N *v a *)
    Lemma mmulv_madd : forall {r c} (M N : mat r c) (a : vec c),
        (M + N) *v a = (M *v a + N *v a)%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      rewrite !vnth_vadd, !vnth_mmulv, !vnth_madd. unfold vdot. unfold vmap2.
      rewrite vsum_add. apply vsum_eq; intros. rewrite vnth_vadd. ring.
    Qed.

    (** (- M) *v a = - (M *v a) *)
    Lemma mmulv_mopp : forall {r c} (M : mat r c) (a : vec c),
        (- M) *v a = (- (M *v a))%V.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mmulv.
      rewrite vnth_mopp. rewrite vdot_vopp_l. auto.
    Qed.

    (** M *v (- a) = - (M *v a) *)
    Lemma mmulv_vopp : forall {r c} (M : mat r c) (a : vec c),
        M *v (- a)%V = (- (M *v a))%V.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mmulv.
      rewrite vdot_vopp_r. auto.
    Qed.

    (** M *v (a - b) = M *v a - M *v b *)
    Lemma mmulv_vsub : forall {r c} (M : mat r c) (a b : vec c),
        M *v (a - b)%V = (M *v a - M *v b)%V.
    Proof. intros. rewrite mmulv_vadd. rewrite mmulv_vopp. auto. Qed.
    
    (** (M - N) *v a = M *v a - N *v a *)
    Lemma mmulv_msub : forall {r c} (M N : mat r c) (a : vec c),
        (M - N) *v a = (M *v a - N *v a)%V.
    Proof. intros. rewrite mmulv_madd. rewrite mmulv_mopp. auto. Qed.
    
    (** 0 *v a = 0 *)
    Lemma mmulv_0_l : forall {r c} (a : vec c), (@mat0 r c) *v a = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mmulv, vnth_vzero.
      apply vdot_0_l.
    Qed.
    
    (** M *v 0 = 0 *)
    Lemma mmulv_0_r : forall {r c} (M : mat r c), M *v vzero = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mmulv, vnth_vzero.
      apply vdot_0_r.
    Qed.
    
    (** 1 *v a = a *)
    Lemma mmulv_1_l : forall {n} (a : vec n), mat1 *v a = a.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite vnth_mmulv.
      apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite mnth_mat1_same. ring.
      - intros. rewrite vnth_vmap2. rewrite mnth_mat1_diff; auto. ring.
    Qed.

    (** (x s* M) *v a = x s* (M *v a) *)
    Lemma mmulv_mscal : forall {r c} (x : tA) (M : mat r c) (a : vec c), 
        (x s* M) *v a = (x s* (M *v a))%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite ?vnth_mmulv, ?vnth_vscal, ?vnth_mscal.
      rewrite vdot_vscal_l. auto.
    Qed.
    
    (** M *v (x s* v) = x s* (M *v a) *)
    Lemma mmulv_vscal : forall {r c} (x : tA) (M : mat r c) (a : vec c), 
        M *v (x s* a)%V = (x s* (M *v a))%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite ?vnth_mmulv, ?vnth_vscal, ?vnth_mscal.
      rewrite vdot_vscal_r. auto.
    Qed.

    (** <a, b> = (v2rv a *v b).1 *)
    Lemma vdot_eq_mmulv : forall {n} (a b : vec n), <a, b> = (v2rv a *v b).1.
    Proof. intros. apply vsum_eq; intros; auto. Qed.

    (** v2cv (M *v a) = M * v2cv a *)
    Lemma v2cv_mmulv : forall {r c} (M : mat r c) (a : vec c),
        v2cv (M *v a) = M * v2cv a.
    Proof. intros. auto. Qed.

    (** v2rv (M * a) = (v2rv a) * M\T *)
    Lemma v2rv_mmulv : forall {r c} (M : mat r c) (a : vec c),
        v2rv (M *v a) = v2rv a * M\T.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold v2rv.
      rewrite vnth_mmulv. rewrite mnth_mmul. rewrite vdot_comm. auto.
    Qed.

    (** [a11 a12 a13 | u1]   [b11 b12 | v1]   
        [a21 a22 a23 | u2]   [b21 b22 | v2]    [A*B+u*q  A*v+u*y]
        -----------------  * [b31 b32 | v2] =  [p*B+x*q  p*v+x*y]
        [ p1  p2  p3 |  x]   --------------
                             [ q1  q2 |  y] *)
    Lemma mmul_mconsrT_mconscT_vconsT :
      forall r c s (A : mat r c) (B : mat c s) u v p q x y,
        (mconsrT (mconscT A u) (vconsT p x)) * (mconsrT (mconscT B v) (vconsT q y))
        = mconsrT
            (mconscT (A * B + v2cv u * v2rv q) (A *v v + y s* u)%V)
            (vconsT (rv2v (v2rv p * B) + x s* q)%V (<p,v> + x * y)%A).
    Proof.
      intros. apply meq_iff_mnth; intros.
      unfold mconsrT. rewrite mnth_mmul.
      destruct (i ??= r), (j ??= s).
      - rewrite !vnth_vconsT_n; auto.
        replace ((vconsT (mconscT B v) (vconsT q y))&[j]) with (vconsT v y).
        + rewrite vdot_vconsT_vconsT. auto.
        + replace j with (@nat2finS s s); fin. rewrite <- mtailc_eq_mcol.
          erewrite <- mtailc_mconsrT_mconscT_vconsT. f_equal. unfold mconsrT. auto.
      - assert (j < s) as Hj by fin.
        rewrite vnth_vconsT_n; auto. rewrite vnth_vconsT_n; auto.
        rewrite vnth_vconsT_lt with (H:=Hj); auto. rewrite vnth_vadd.
        replace ((vconsT (mconscT B v) (vconsT q y))&[j]) with
          (vconsT (B&[fPredRange j Hj]) (q (fPredRange j Hj))).
        + rewrite vdot_vconsT_vconsT. f_equal.
        + replace (vconsT (mconscT B v) (vconsT q y)) with
            (mconsrT (mconscT B v) (vconsT q y)); auto.
          rewrite <- mconscT_mconsrT_vconsT_eq_mconsrT_mconscT_vconsT.
          rewrite mcol_mconscT_lt with (H:=Hj). rewrite mcol_mconsrT. auto.
      - assert (i < r) as Hi by fin.
        rewrite !vnth_vconsT_lt with (H:=Hi); auto. rewrite !vnth_mconscT.
        rewrite vnth_vconsT_n; auto.
        replace ((vconsT (mconscT B v) (vconsT q y))&[j]) with (vconsT v y).
        + rewrite vdot_vconsT_vconsT. rewrite vnth_vadd. f_equal.
          rewrite vnth_vscal. ring.
        + replace (vconsT (mconscT B v) (vconsT q y)) with
            (mconsrT (mconscT B v) (vconsT q y)); auto.
          rewrite <- mconscT_mconsrT_vconsT_eq_mconsrT_mconscT_vconsT.
          rewrite mcol_mconscT_n; auto.
      - assert (i < r) as Hi by fin.
        assert (j < s) as Hj by fin.
        rewrite !vnth_vconsT_lt with (H:=Hi); auto. rewrite !vnth_mconscT.
        rewrite !vnth_vconsT_lt with (H:=Hj); auto.
        replace ((vconsT (mconscT B v) (vconsT q y))&[j]) with
          (vconsT (B&[fPredRange j Hj]) (q (fPredRange j Hj))).
        + rewrite vdot_vconsT_vconsT. rewrite mnth_madd. f_equal. cbv. ring.
        + replace (vconsT (mconscT B v) (vconsT q y))
            with (mconsrT (mconscT B v) (vconsT q y)); auto.
          rewrite <- mconscT_mconsrT_vconsT_eq_mconsrT_mconscT_vconsT.
          rewrite mcol_mconscT_lt with (H:=Hj); auto.
          rewrite mcol_mconsrT. auto.
    Qed.

  End mmulv.
  Infix "*v" := mmulv : mat_scope.
  
  
  (* ======================================================================= *)
  (** ** Vector (row matrix) multiply matrix *)
  Section mvmul.
    Notation vec := (@vec tA).
    Notation vopp := (@vopp _ Aopp).
    Notation "- a" := (vopp a) : vec_scope.
    Notation "a - b" := ((a + -b)%V) : vec_scope.

    Definition mvmul {r c : nat} (a : vec r) (M : mat r c) : vec c :=
      fun i => <a, M&[i]>.
    Infix "v*" := mvmul : mat_scope.

    (** (M v* a)[i] = <row M i, a> *)
    Lemma vnth_mvmul : forall {r c} (a : vec r) (M : mat r c) i,
        (a v* M).[i] = <a, M&[i]>.
    Proof. intros. auto. Qed.

    (** a v* (M * N) = (a v* M) v* N *)
    Lemma mvmul_assoc : forall {r c s} (a : vec r) (M : mat r c) (N : mat c s),
        a v* (M * N) = (a v* M) v* N.
    Proof.
      intros. unfold mvmul. apply veq_iff_vnth; intros. rewrite vdot_assoc. auto.
    Qed.

    (** (a + b) v* M = a v* M + b v* M *)
    Lemma mvmul_vadd : forall {r c} (a b : vec r) (M : mat r c),
        (a + b)%V v* M = (a v* M + b v* M)%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      rewrite !vnth_vadd, !vnth_mvmul.
      unfold vdot. unfold vmap2.
      rewrite vsum_add. apply vsum_eq; intros. rewrite vnth_vadd. ring.
    Qed.
    
    (** a v* (M + N) = a v* M + N v* a *)
    Lemma mvmul_madd : forall {r c} (a : vec r) (M N : mat r c),
        a v* (M + N) = (a v* M + a v* N)%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      rewrite !vnth_vadd, !vnth_mvmul. unfold vdot. unfold vmap2.
      rewrite vsum_add. apply vsum_eq; intros.
      rewrite !vnth_mcol. rewrite mnth_madd. ring.
    Qed.

    (** a v* (- M) = - (a v* M) *)
    Lemma mvmul_mopp : forall {r c} (a : vec r) (M : mat r c),
        a v* (- M) = (- (a v* M))%V.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mvmul.
      rewrite mcol_mopp. rewrite <- vdot_vopp_r. auto.
    Qed.

    (** (- a) v* M = - (a v* M) *)
    Lemma mvmul_vopp : forall {r c} (a : vec r) (M : mat r c),
        (- a)%V v* M = (- (a v* M))%V.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite ?vnth_vopp, ?vnth_mvmul.
      rewrite vdot_vopp_l. auto.
    Qed.

    (** (a - b) v* M = a v* M - b v* M *)
    Lemma mvmul_vsub : forall {r c} (a b : vec r) (M : mat r c),
        (a - b)%V v* M = (a v* M - b v* M)%V.
    Proof. intros. rewrite mvmul_vadd. rewrite mvmul_vopp. auto. Qed.
    
    (** a v* (M - N) = a v* M - a v* N *)
    Lemma mvmul_msub : forall {r c} (a : vec r) (M N : mat r c),
        a v* (M - N) = (a v* M - a v* N)%V.
    Proof. intros. rewrite mvmul_madd. rewrite mvmul_mopp. auto. Qed.
    
    (** 0 v* M = 0 *)
    Lemma mvmul_0_l : forall {r c} (M : mat r c), vzero v* M = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mvmul, vnth_vzero.
      apply vdot_0_l.
    Qed.
    
    (** a v* 0 = 0 *)
    Lemma mvmul_0_r : forall {r c} (a : vec r), a v* (@mat0 r c) = vzero.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite !vnth_mvmul, vnth_vzero.
      apply vdot_0_r.
    Qed.
    
    (** a v* mat1 = a *)
    Lemma mvmul_1_r : forall {n} (a : vec n), a v* mat1 = a.
    Proof.
      intros. apply veq_iff_vnth; intros. rewrite vnth_mvmul.
      unfold vdot. apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite vnth_mcol. rewrite mnth_mat1_same. ring.
      - intros. rewrite vnth_vmap2. rewrite vnth_mcol.
        rewrite mnth_mat1_diff; auto. ring.
    Qed.

    (** a v* (x s* M) = x s* (a v* M) *)
    Lemma mvmul_mscal : forall {r c} (a : vec r) (x : tA) (M : mat r c), 
        a v* (x s* M) = (x s* (a v* M))%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite vnth_mvmul, !vnth_vscal. rewrite vnth_mvmul.
      rewrite mcol_mscal. rewrite vdot_vscal_r. auto.
    Qed.
    
    (** (x s* a) v* M  = x s* (a v* M) *)
    Lemma mvmul_vscal : forall {r c} (a : vec r) (x : tA) (M : mat r c), 
        (x s* a)%V v* M = (x s* (a v* M))%V.
    Proof.
      intros. apply veq_iff_vnth; intros.
      repeat rewrite ?vnth_mvmul, ?vnth_vscal, ?vnth_mscal.
      rewrite vdot_vscal_l. auto.
    Qed.

    (** <a, b> = (a v* v2cv b).1 *)
    Lemma vdot_eq_mvmul : forall {n} (a b : vec n), <a, b> = (a v* v2cv b).1.
    Proof. intros. apply vsum_eq; intros; auto. Qed.

    (** v2cv (a v* M) = v2rv a * M *)
    Lemma v2cv_mvmul : forall {r c} (a : vec r) (M : mat r c),
        v2cv (a v* M) = M\T * v2cv a.
    Proof.
      intros. apply meq_iff_mnth; intros. unfold v2cv.
      rewrite vnth_mvmul. rewrite mnth_mmul. rewrite vdot_comm. auto.
    Qed.

    (** v2rv (a v* M) = (v2rv a) * M *)
    Lemma v2rv_mvmul : forall {r c} (a : vec r) (M : mat r c),
        v2rv (a v* M) = v2rv a * M.
    Proof. auto. Qed.
    
  End mvmul.
  Infix "v*" := mvmul : mat_scope.

  (** *** Mixed properties about mmul, mmulv, mvmul  *)
  Section mmul_mmulv_mvmul.

    (** x x x               xy xy | bx
        x x x   y y | b     xy xy | bx
        ----- * y y | b  =  ----- | --
        a a a   y y | b     ax ax | ab *)
    Lemma mmul_mconsrT_mconscT_eq_mconscT :
      forall {r c s} (M1 : mat r c) (v1 : vec c) (M2 : mat c s) (v2 : vec c),
        mconsrT M1 v1 * mconscT M2 v2 =
          mconscT (mconsrT (M1 * M2) (v1 v* M2)) (vconsT (M1 *v v2) (<v1,v2>)).
    Proof.
      intros. auto_vec. apply meq_iff_mnth; intros.
      rewrite mnth_mmul. auto_vec.
      pose proof (fin2nat_lt i); pose proof (fin2nat_lt j).
      destruct (fin2nat i ??= r), (fin2nat j ??= s).
      - rewrite !vnth_vconsT_n; auto. f_equal. apply veq_iff_vnth; intros.
        auto_vec. rewrite vnth_vconsT_n; auto.
      - rewrite !(vnth_vconsT_n _ _ i); try erewrite !(vnth_vconsT_lt _ _ j); auto.
        rewrite vnth_mvmul. f_equal. apply veq_iff_vnth; intros.
        auto_vec. erewrite vnth_vconsT_lt; auto.
      - rewrite !(vnth_vconsT_n _ _ j); try erewrite !(vnth_vconsT_lt _ _ i); auto.
        rewrite vnth_mmulv. f_equal. apply veq_iff_vnth; intros.
        auto_vec. rewrite vnth_vconsT_n; auto.
      - erewrite !(vnth_vconsT_lt); auto.
        rewrite mnth_mmul. f_equal. apply veq_iff_vnth; intros.
        auto_vec. erewrite vnth_vconsT_lt; auto.
        Unshelve. all: fin.
    Qed.

    (** x x x               xy xy | bx
        x x x   y y | b     xy xy | bx
        ----- * y y | b  =  ----------
        a a a   y y | b     ax ax | ab *)
    Lemma mmul_mconsrT_mconscT_eq_mconsrT :
      forall {r c s} (M1 : mat r c) (v1 : vec c) (M2 : mat c s) (v2 : vec c),
        mconsrT M1 v1 * mconscT M2 v2 =
          mconsrT (mconscT (M1 * M2) (M1 *v v2)) (vconsT (v1 v* M2) (<v1,v2>)).
    Proof.
      intros. rewrite mmul_mconsrT_mconscT_eq_mconscT.
      rewrite mconscT_mconsrT_vconsT_eq_mconsrT_mconscT_vconsT. auto.
    Qed.
    
  End mmul_mmulv_mvmul.
  
  (* ======================================================================= *)
  (** ** Skew-symmetric matrix *)
  Section skew.
    
    (** Given matrix is skew-symmetric matrices *)
    Definition skewP {n} (M : smat n) : Prop := - M = M\T.

  End skew.
  

  Context {ADec : Dec (@eq tA)}.

  (** *** Properties when equipped with `Dec` *)
  Section with_Dec.
    
    (** (M <> 0 /\ N <> 0 /\ x s* M = N) -> x <> 0 *)
    Lemma mscal_eq_imply_not_x0 : forall {r c} (M N : mat r c) x,
        M <> mat0 -> N <> mat0 -> x s* M = N -> x <> 0.
    Proof.
      intros. destruct (Aeqdec x 0); auto. exfalso. subst.
      rewrite mscal_0_l in H0. easy.
    Qed.
  End with_Dec.

  
  (** Properties below, need a field structure *)
  Context `{HField : Field tA Aadd 0 Aopp Amul 1 Ainv}.

  
  (** *** Properties when equipped with `Field` *)
  Section with_Field.

    (** x s* A = x s* B -> x <> 0 -> A = B *)
    Lemma mscal_eq_reg_l : forall {r c} x (A B : mat r c),
        x s* A = x s* B -> x <> Azero -> A = B.
    Proof.
      intros. rewrite meq_iff_mnth in *. intros i j. specialize (H i j).
      rewrite !mnth_mscal in H. apply field_mul_cancel_l in H; auto.
    Qed.
    
    (** x s* A = y * A -> A <> mat0 -> x = y *)
    Lemma mscal_eq_reg_r : forall {r c} x y (A : mat r c), 
        x s* A = y s* A -> A <> mat0 -> x = y.
    Proof.
      intros. destruct (Aeqdec x y); auto. rewrite veq_iff_vnth in *.
      destruct H0. intros i. specialize (H i). rewrite !vnth_mscal in H.
      destruct (Aeqdec (A i) vzero); auto.
      apply vscal_eq_reg_r in H; try easy.
    Qed.
  
    (** x * M = 0 -> (x = 0) \/ (M = 0) *)
    Lemma mscal_eq0_imply_x0_or_m0 : forall {r c} (M : mat r c) x,
        x s* M = mat0 -> (x = 0)%A \/ (M = mat0).
    Proof.
      intros. destruct (Aeqdec x 0); auto. right.
      apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H. specialize (H i j).
      cbv in H. cbv. apply field_mul_eq0_iff in H. tauto.
    Qed.

    (** (M <> 0 /\ x * M = 0) -> M = 0 *)
    Lemma mscal_mnonzero_eq0_imply_x0 : forall {r c} (M : mat r c) x,
        M <> mat0 -> x s* M = mat0 -> (x = 0)%A.
    Proof. intros. apply mscal_eq0_imply_x0_or_m0 in H0; auto. tauto. Qed.

    (** x * M = M -> x = 1 \/ M = 0 *)
    Lemma mscal_same_imply_x1_or_m0 : forall {r c} x (M : mat r c),
        x s* M = M -> (x = 1)%A \/ (M = mat0).
    Proof.
      intros. destruct (Aeqdec x 1); auto. right.
      apply meq_iff_mnth; intros. rewrite meq_iff_mnth in H. specialize (H i j).
      cbv in H. cbv. apply field_mul_eq_imply_a1_or_b0 in H; auto. tauto.
    Qed.
  End with_Field.

End malg.

Section test.
  Let M0 := @l2m _ 9 2 2 [].
  Let M := @l2m _ 9 2 2 [[1;2];[3;4]].
  Let N := @l2m _ 9 2 2 [[1];[3;4]].
  Let O := @l2m _ 9 2 2 [[1;2];[3]].
  Let M4 := @l2m _ 9 2 2 [[1;2;3];[3;4]].
  Let M5 := @l2m _ 9 2 2 [[1;2];[3;4;5]].
  (* Compute m2l M0. *)
  (* Compute m2l M. *)
  (* Compute m2l N. *)
  (* Compute m2l O. *)
  (* Compute m2l M4. *)
  (* Compute m2l M5. *)
End test.


(* ######################################################################### *)
(** * Elementary Row Transform *)

Section RowTrans.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation "a - b" := (a + - b) : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "+" := (@madd _ Aadd _ _) : mat_scope.
  Notation mat1 := (@mat1 _ 0 1).
  Infix "*" := (@mmul _ Aadd 0 Amul _ _ _) : mat_scope.


  (* ======================================================================= *)
  (** ** Matrix with one given element *)
  
  (** An matrix which (x,y) element is _a_ *)
  Definition matOneElem {n} (x y : 'I_n) (a : tA) : smat tA n :=
    fun i j => if i ??= x then (if j ??= y then a else 0) else 0.

  (* ======================================================================= *)
  (** ** Row scaling *)

  (** Scalar multiply with c to x-th row of matrix M *)
  Definition mrowScale {n} (x : 'I_n) (c : tA) (M : smat tA n) : smat tA n :=
    fun i j => if i ??= x then (c * M i j)%A else M i j.
  
  (** 行数乘矩阵
      作用：E(x,c) * M 的结果是 M 的第 x 行乘以 c 倍
      形式：第 (x,x) 的元素是 c, 其余是单位阵 *)
  Definition mrowScaleM {n} (x : 'I_n) (c : tA) : smat tA n :=
    fun (i j : 'I_n) => if i ??= j then (if i ??= x then c else 1) else 0.

  (** rowScale of `M` equal to left multiply rowScaleMat of `M` *)
  Lemma mrowScale_eq : forall {n} (x : 'I_n) (c : tA) (M : smat tA n),
      mrowScale x c M = (mrowScaleM x c) * M.
  Proof.
    intros. unfold mrowScale, mrowScaleM. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. unfold vdot. fin.
    - apply fin2nat_eq_iff in E; rewrite E. symmetry.
      apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; fin.
    - symmetry.
      apply vsum_unique with (i := i); intros; rewrite vnth_vmap2; fin.
      rewrite vnth_mcol. ring.
  Qed.

  (** mrowScale i c (M * N) = mrowScale i c M * N *)
  Lemma mrowScale_mmul : forall {n} (M N : smat tA n) (i : 'I_n) (c : tA),
      mrowScale i c (M * N) = mrowScale i c M * N.
  Proof. intros. rewrite !mrowScale_eq. rewrite mmul_assoc; auto. Qed.

  (* ======================================================================= *)
  (** ** Row addition with scaling *)

  (** 行倍加：矩阵 M 的第 y 行的 c 倍加到第 x 行 *)
  Definition mrowAdd {n} (x y : 'I_n) (c : tA) (M : smat tA n) : smat tA n :=
    fun i j => if i ??= x then (M i j + c * M y j)%A else M i j.
  
  (** 行倍加矩阵
      作用：E(x,y,c) * M 的结果是 M 的第 y 行的 c 倍加到第 x 行
      形式：单位阵 + 第 (x,y) 的元素是 c *)
  Definition mrowAddM {n} (x y : 'I_n) (c : tA) : smat tA n :=
    mat1 + matOneElem x y c.

  Lemma mrowAdd_eq : forall {n} (x y : 'I_n) (c : tA) (M : smat tA n),
      mrowAdd x y c M = (mrowAddM x y c) * M.
  Proof.
    intros. unfold mrowAdd, mrowAddM, matOneElem. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. symmetry. fin.
    - rewrite vnth_madd. rewrite vdot_vadd_l. f_equal.
      + apply fin2nat_eq_iff in E; rewrite E.
        apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; fin.
        * rewrite vnth_mcol. rewrite mnth_mat1_same. ring.
        * rewrite vnth_mcol. rewrite mnth_mat1_diff; auto. ring.
      + apply vsum_unique with (i := y); intros; rewrite vnth_vmap2; fin.
    - rewrite vnth_madd. unfold vadd.
      apply vsum_unique with (i := i); intros; rewrite !vnth_vmap2; fin.
      + rewrite vnth_mcol. rewrite mnth_mat1_same. ring.
      + rewrite vnth_mcol. rewrite mnth_mat1_diff; auto. ring.
  Qed.

  (** mrowAdd i j c (M * N) = mrowScale i j c M * N *)
  Lemma mrowAdd_mmul : forall {n} (M N : smat tA n) (i j : 'I_n) (c : tA),
      mrowAdd i j c (M * N) = mrowAdd i j c M * N.
  Proof. intros. rewrite !mrowAdd_eq. rewrite mmul_assoc; auto. Qed.

  (** (i)+c(j)) * (i)+(-c)(j) = mat1 *)
  Lemma mmul_mrowAddM_mrowAddM : forall {n} (i j : 'I_n) (c : tA),
      i <> j -> mrowAddM i j c * mrowAddM i j (-c) = mat1.
  Proof.
    intros. rewrite <- mrowAdd_eq. unfold mrowAddM, mrowAdd.
    apply meq_iff_mnth; intros. rewrite !mnth_madd. unfold matOneElem. fin.
    - fin2nat. rewrite mnth_mat1_same. ring.
    - fin2nat. subst. rewrite (mnth_mat1_diff j j0); auto. ring.
  Qed.
  
  (* ======================================================================= *)
  (** ** Row swapping *)

  (** 行交换：矩阵 M 的第 x, y 两行互换 *)
  Definition mrowSwap {n} (x y : 'I_n) (M : smat tA n) : smat tA n :=
    fun i j => if i ??= x then M y j else (if i ??= y then M x j else M i j).
  
  (** 行交换矩阵
      作用：E(x,y) * M 的结果是 M 的第 x 行和第 y 行交换
      形式：在x,y所在行时，(x,y) 和 (y,x) 是 1；其余行时是单位阵 *)
  Definition mrowSwapM {n} (x y : 'I_n) : smat tA n :=
    fun i j =>
      if i ??= x
      then (if j ??= y then 1 else 0)
      else (if i ??= y
            then (if j ??= x then 1 else 0)
            else (if i ??= j then 1 else 0)).

  Lemma mrowSwap_eq : forall {n} (x y : 'I_n) (M : smat tA n),
      mrowSwap x y M = (mrowSwapM x y) * M.
  Proof.
    intros. unfold mrowSwap, mrowSwapM. apply meq_iff_mnth; intros.
    rewrite mnth_mmul. symmetry. fin.
    - apply vsum_unique with (i := y); intros; rewrite vnth_vmap2; fin.
      rewrite vnth_mcol. ring.
    - apply vsum_unique with (i := x); intros; rewrite vnth_vmap2; fin.
      rewrite vnth_mcol. ring.
    - apply vsum_unique with (i := i); intros; rewrite vnth_vmap2; fin.
      rewrite vnth_mcol. ring.
  Qed.

  (** mrowSwap i j (M * N) = mrowSwap i j M * N *)
  Lemma mrowSwap_mmul : forall {n} (M N : smat tA n) (i j : 'I_n),
      mrowSwap i j (M * N) = mrowSwap i j M * N.
  Proof. intros. rewrite !mrowSwap_eq. rewrite mmul_assoc; auto. Qed.

  (** (i,j) * (i,j) = mat1 *)
  Lemma mmul_mrowSwapM_mrowSwapM : forall {n} (i j : 'I_n),
      mrowSwapM i j * mrowSwapM i j = mat1.
  Proof.
    intros. rewrite <- mrowSwap_eq. unfold mrowSwapM, mrowSwap.
    apply meq_iff_mnth; intros. fin.
    - fin2nat. rewrite mnth_mat1_same; auto.
    - fin2nat. rewrite mnth_mat1_diff; auto.
    - fin2nat. rewrite mnth_mat1_same; auto.
    - fin2nat. rewrite mnth_mat1_diff; auto.
    - fin2nat. rewrite mnth_mat1_same; auto.
    - fin2nat. rewrite mnth_mat1_diff; auto.
  Qed.

  (* If we equipped a "Field" *)
  Section Field.
    Context `{HField : Field tA Aadd 0 Aopp Amul 1}.
    Add Field field_inst : (make_field_theory HField).
    
    Notation "/ a" := (Ainv a) : A_scope.
    Notation "a / b" := (a * / b) : A_scope.
    
    (** c(i) * (/c)(i) = mat1 *)
    Lemma mmul_mrowScaleM_mrowScaleM : forall {n} (i : 'I_n) (c : tA),
        c <> 0 -> mrowScaleM i c * mrowScaleM i (/c) = mat1.
    Proof.
      intros. rewrite <- mrowScale_eq. unfold mrowScaleM, mrowScale.
      apply meq_iff_mnth; intros. fin.
      - fin2nat. rewrite mnth_mat1_same; auto. field. auto.
      - fin2nat. rewrite mnth_mat1_diff; auto. field.
    Qed.
  End Field.

End RowTrans.

Section test.
  Import Reals.
  Open Scope R.

  Notation mrowScale := (mrowScale (Amul:=Rmult)).
  Notation mrowAdd := (mrowAdd (Aadd:=Rplus) (Amul:=Rmult)).
  
  Let M : smat R 2 := @l2m _ 0 2 2 ([[1;2];[3;4]]).

  Let i0 : 'I_2 := nat2finS 0.
  Let i1 : 'I_2 := nat2finS 1.

  Goal m2l (mrowScale i0 2 M) = [[2;4];[3;4]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowScale i1 2 M) = [[1;2];[6;8]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap i0 i0 M) = m2l M. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowSwap i0 i1 M) = [[3;4];[1;2]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowAdd i1 i0 2 M) = [[1;2];[5;8]]. Proof. cbv. list_eq; ring. Qed.
  Goal m2l (mrowAdd i0 i1 2 M) = [[7;10];[3;4]]. Proof. cbv. list_eq; ring. Qed.
End test.
