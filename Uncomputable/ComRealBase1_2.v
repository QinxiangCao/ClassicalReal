(** Uncomputablity in the definition of R function **)
(** For convenience's sake, we focus on real numbers in [0,1] **) 
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Export Field.
From Coq Require Export Omega.
From CReal Require Export Uncomputable.TMSet.
From CReal Require Export INR_libs.
From Coq Require Export Psatz.
Import ListNotations.
Import TM_1_2.
Module Type Vir_R.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv : {a0 : R | ~(a0 = R0)} -> R.
  Parameter Rlt : R -> R -> Prop.
  Parameter Rabs : R -> R.
  Parameter up : R -> Z.
  Parameter IZR : Z -> R.
  Parameter QTR : Q -> R.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  Infix "-" := Rminus : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Parameter Rpow : {a0 : R | ~(a0 = R0)} -> nat ->R. 
  Parameter Rlim : (nat -> R) -> R -> Prop.
  Definition Reqb (x y : R) : Prop := x = y.
  Parameter Reqb_refl : forall (x : R) , Reqb x x.
  Theorem Proper_Reqb : forall (x : R),Proper Reqb x.
  Proof.
    intros.
    unfold Proper.
    apply Reqb_refl.
  Qed.

  Parameter Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Parameter Rlt_not_refl : forall r1 : R , ~ (r1 < r1).
  Theorem Req : forall (x y : R) , x <= y /\ y <= x <-> x = y.
  Proof.
    intros.
    split.
    - intros.
      destruct H ; auto.
      destruct H ; auto.
      destruct H0 ; auto.
      pose proof Rlt_trans x y x H H0.
      exfalso. apply (Rlt_not_refl x) ; auto.
    - intros.
      split ; unfold Rle in * ; unfold Rge in *; auto.
  Qed.
  
  Theorem Rle_ge : forall (x y : R) , x >= y <-> y <= x.
  Proof.
    intros.
    unfold Rge in *.
    unfold Rle in *.
    split ; intros ; destruct H ; auto.
  Qed.
  
  Parameter Rplus_0 : forall r1 r2 : R , r1 - r2 = R0 <-> r1 = r2.
  Parameter Rle_ge_eq : forall x y : R , x >= y -> y >= x -> x = y.
  Parameter Bin_R : R -> nat -> nat -> Prop.
  Axiom Bin_R_pro1 : forall (r : R) (n : nat) , Bin_R r n 1 \/ Bin_R r n 0.
  Axiom Bin_R_pro2 : forall (r : R) (n : nat) , Bin_R r n 1 <-> (~ Bin_R r n 0).
  Axiom Zero_Bin : forall (n : nat) , Bin_R R0 n 0.
  Axiom One_Bin : forall (n : nat) , Bin_R R1 n 1.
  Theorem Bin_R_pro2' : forall (r : R) (n : nat) , (~Bin_R r n 1) <-> (Bin_R r n 0).
  Proof.
    intros.
    split.
    - intros. apply NNPP. unfold not in *.
      intros. apply H. apply Bin_R_pro2. unfold not in *. apply H0.
    - unfold not in *. intros. rewrite Bin_R_pro2 in H0.
      apply H0. apply H.
  Qed.

  Axiom Bin_R_pro3  : forall (r1 r2 : R) , r1 = r2 <-> (forall (j : nat) , Bin_R r1 j 1 <-> Bin_R r2 j 1).
  Axiom Bin_R_pro3' : forall (r1 r2 : R) , r1 < r2 <-> 
                      exists (j : nat), (Bin_R r1 j 0) /\ (Bin_R r2 j 1) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (Bin_R r1 k 1 <-> Bin_R r2 k 1)).
  
  Theorem Bin_R_pro3'' : forall (r1 r2 : R) , r1 > r2 <-> 
                      exists (j : nat), (Bin_R r1 j 1) /\ (Bin_R r2 j 0) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (Bin_R r1 k 1 <-> Bin_R r2 k 1)%nat).
  Proof.
    intros.
    pose proof (Bin_R_pro3' r2 r1).
    split.
    - intros.
      apply H in H0.
      inversion H0.
      exists x.
      destruct H1 as [H2 [H3 H4]].
      split ; auto.
      split ; auto.
      intros.
      rewrite (H4 _ H1). apply iff_refl.
    - intros.
      apply H.
      inversion H0.
      exists x.
      destruct H1 as [H2 [H3 H4]].
      split ; auto.
      split ; auto.
      intros.
      rewrite (H4 _ H1). apply iff_refl.
  Qed.

  Theorem Bin_R_pro3_not : forall (r1 r2 : R) , r1 <> r2 <-> exists (j : nat), (Bin_R r1 j 1 <-> Bin_R r2 j 0).
  Proof.
    intros.
    split.
    - intros.
      pose proof Bin_R_pro3 r1 r2.
      rewrite H0 in H.
      clear H0.
      apply not_all_ex_not in H.
      destruct H.
      exists x.
      unfold not in H.
      split.
      + intros. apply Bin_R_pro2'. unfold not. intros. apply H.
        split ; auto.
      + intros. apply Bin_R_pro2. unfold not. intros. apply H.
        split ; intros ; apply Bin_R_pro2 in H2 ; exfalso ; apply H2 ; auto.
    - intros.
      destruct H.
      unfold not in *.
      intros.
      rewrite (Bin_R_pro3 r1 r2) in H0.
      rewrite (H0 x) in H.
      rewrite (Bin_R_pro2 r2 x) in H.
      destruct H.
      pose proof classic (Bin_R r2 x 0).
      destruct H2.
      + apply H1 ; auto.
      + apply H2 ; auto.
  Qed.
  
  Lemma ge_pow_ge : forall n: nat , (2 ^ n > n)%nat.
  Proof.
    intros.
    apply Nat.pow_gt_lin_r.
    auto.
  Qed.
  
  Definition CR (r : R) : Prop := 
      exists f : nat -> nat, (forall (n: nat), (f n = 1%nat \/ f n = 0%nat) /\ Bin_R r n (f n)).
  Definition CR1 (r : R) := {f : nat -> nat | (forall (n: nat), (f n = 1%nat \/ f n = 0%nat) /\ Bin_R r n (f n)) }.
  Definition limit (f : nat -> Q) (r : R) : Prop :=
    forall eps : Q , (eps > 0)%Q -> exists N : nat , forall n : nat , (n >= N)%nat -> Rabs(QTR (f n) - r) < QTR eps.
  (** exists a sequence of rational number limits to r *)
  Definition CR2 (r : R) := exists f : nat -> Q, limit f r.
  (** exists a Cauthy sequence of rational number limits to r *)
  Definition CR3 (r : R) :=
      {f : nat -> Q & {N : Q -> nat | limit f r /\ (forall eps : Q , (eps > 0)%Q -> forall (n m : nat) , (n >= N eps)%nat /\ (n >= 1) %nat -> (m >= n)%nat -> (Qabs(f n - f m) < eps)%Q)} }.
 
  Theorem CR1_CR : forall r : R , CR1 r -> CR r.
  Proof.
    intros.
    unfold CR1 in *.
    unfold CR in *.
    destruct H as [f ?].
    exists f. auto.
  Qed.
  Theorem CR3_CR2 : forall r : R , CR3 r -> CR2 r.
  Proof.
    unfold CR3 in *.
    unfold CR2 in *.
    intros.
    destruct H as [? [? ?]].
    exists x. destruct a. auto.
  Qed.

  Fixpoint sum_f (f : nat -> nat) (n : nat) : Q :=
    match n with
      | 0%nat => INR (f 0%nat)
      | S n' => (sum_f f n' + (INR (f n) / INR (2 ^ n)))%Q
    end.
 
  Axiom sum_f_limit_r : forall (f : nat -> nat) (r : R) , limit (sum_f f) r <-> (forall n : nat , Bin_R r n (f n)).
  
  Axiom sum_f_limit_eps : forall (f : nat -> nat)(n m : nat) , (n <= m) % nat -> (Qabs(sum_f f n - sum_f f m) < 1 / INR (2^n))%Q.

  Theorem CR_CR2 : forall r : R , CR r -> CR2 r.
  Proof.
    unfold CR.
    unfold CR2.
    intros.
    destruct H.
    exists (sum_f x).
    rewrite sum_f_limit_r.
    apply H.
  Qed.
  
  Theorem CR1_CR3 : forall r : R , CR1 r -> CR3 r.
  Proof.
    unfold CR1.
    unfold CR3.
    intros.
    destruct H.
    exists (sum_f x).
    exists (fun eps => eps_arrow_nat eps).
    split.
    - rewrite sum_f_limit_r. apply a.
    - intros.
      destruct H0.
      pose proof eps_arrow_correct eps.
      remember (eps_arrow_nat eps) as n0.
      apply Qlt_trans with (y := (1 / INR(n0))).
      + apply Qlt_trans with (y := (1 / INR(2^n))).
        * apply sum_f_limit_eps ; auto.
        * apply Qlt_shift_div_l.
          ** rewrite Heqn0. apply eps_arrow_pro ; auto.
          ** rewrite Qmult_comm.
             assert (H' : 1 / INR (2 ^ n) == / INR (2 ^ n)).
             {
               field.
               unfold not.
               intros.
               pose proof INR_lt (2 ^ n) 0 (Max_pown_0 n).
               rewrite H4 in H5.
               apply (Qlt_irrefl 0). auto.
             }
             rewrite H'.
             clear H'.
             apply Qlt_shift_div_r.
             apply Max_pown_0Q.
             rewrite Qmult_1_l.
             apply INR_lt.
             pose proof ge_pow_ge n.
             apply le_lt_trans with (m := n) ; auto.
      + apply Qlt_shift_div_r.
        * rewrite Heqn0. apply eps_arrow_pro ; auto.
        * rewrite Qmult_comm.
        assert (H' : 1 == 1 / eps * eps).
        { field. unfold not. intros.
          rewrite H4 in H. apply (Qlt_irrefl 0). auto.
        }
        rewrite H' at 1.
        apply Qmult_lt_compat_r ; auto.
  Qed.
  
End Vir_R.
