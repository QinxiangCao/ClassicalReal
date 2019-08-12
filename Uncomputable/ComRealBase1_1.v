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
Import TM_1_1.
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
  Parameter Rlt_irrefl : forall r1 : R , ~ (r1 < r1).
  Instance Proper_Reqb : forall (x : R),Proper Reqb x.
  Proof.
    intros.
    unfold Proper.
    apply Reqb_refl.
  Qed.
  Parameter QTR_R0 : QTR (0%Q) = R0.
  Parameter QTR_R1 : QTR (1%Q) = R1.
  Parameter QTR_plus : forall r1 r2 : Q , QTR r1 + QTR r2 = QTR (r1 + r2).
  Parameter QTR_le : forall r1 r2 : Q , (r1 <= r2)%Q -> QTR r1 <= QTR r2.
  Parameter QTR_lt : forall r1 r2 : Q , (r1 < r2)%Q -> QTR r1 < QTR r2.
  Parameter QTR_eq : forall r1 r2 : Q , (r1 = r2)%Q -> QTR r1 = QTR r2.
  Parameter Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Parameter Rabs_pos : forall r1 : R , (r1 >= R0) -> Rabs r1 = r1.
  Parameter Rabs_neg : forall r1 : R , (r1 <= R0) -> Rabs r1 = - r1.
  Parameter Ropp_R0 : R0 = - R0. 
  Parameter Ropp_QTR : forall r : Q ,  - QTR r  = QTR ( - r).
  Parameter Rlt_pos_eqb : forall r1 r2 : R  , r1 < r2 <-> r2 - r1 > R0.
  Parameter Rlt_neg_eqb : forall r1 r2 : R  , r1 > r2 <-> r2 - r1 < R0.
  Parameter Rle_pos_eqb : forall r1 r2 : R  , r1 <= r2 <-> r2 - r1 >= R0.
  Parameter Rle_neg_eqb : forall r1 r2 : R  , r1 >= r2 <-> r2 - r1 <= R0.
  Parameter Rplus_0_l : forall r1 : R , r1 = R0 + r1.
  Parameter Rplus_0_r : forall r1 : R , r1 = r1 + R0.
  Parameter Rplus_comm : forall r1 r2 : R , r1 + r2 = r2 + r1.
  Parameter Rplus_assoc : forall r1 r2 r3 : R , r1 + r2 + r3 = r1 + (r2 + r3).
  Parameter Ropp_minus : forall r1 r2 : R , - (r1 - r2) = r2 - r1.
  Theorem Rle_lt_weak : forall r1 r2 : R , r1 < r2 -> r1 <= r2.
  Proof.
    intros.
    unfold Rle. auto.
  Qed.

  Theorem Rle_refl : forall r1 : R , r1 <= r1.
  Proof.
    intros.
    unfold Rle. auto.
  Qed.

  Theorem Rle_trans : forall r1 r2 r3:R, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
  Proof.
    intros.
    destruct H , H0.
    - apply Rle_lt_weak. apply Rlt_trans with r2 ; auto.
    - rewrite <- H0. apply Rle_lt_weak. auto.
    - rewrite H. apply Rle_lt_weak. auto.
    - rewrite H , H0. apply Rle_refl.
  Qed.

  Theorem Rlt_le_trans : forall r1 r2 r3:R , r1 < r2 -> r2 <= r3 -> r1 < r3.
  Proof.
    intros.
    destruct H0.
    - apply Rlt_trans with r2 ; auto.
    - rewrite <- H0. auto.
  Qed.

  Theorem Rle_lt_trans : forall r1 r2 r3:R , r1 <= r2 -> r2 < r3 -> r1 < r3.
  Proof.
    intros.
    destruct H.
    - apply Rlt_trans with r2 ; auto.
    - rewrite H. auto.
  Qed.

  Parameter Rlt_Rplus_r : forall r1 r2 r3: R , r1 < r2 -> r1 + r3 < r2 + r3.
  Parameter Rlt_Rplus_l : forall r1 r2 r3: R , r1 < r2 -> r3 + r1 < r3 + r2.
  Parameter Rlt_Rminus_r : forall r1 r2 r3: R , r1 - r2 < r3 -> r1 - r3 < r2.
  Parameter Rlt_Rminus_Rplus : forall r1 r2 r3: R , r1 < r2 + r3 -> r1 - r2 < r3.
  Theorem Req : forall (x y : R) , x <= y /\ y <= x <-> x = y.
  Proof.
    intros.
    split.
    - intros.
      destruct H ; auto.
      destruct H ; auto.
      destruct H0 ; auto.
      pose proof Rlt_trans x y x H H0.
      exfalso. apply (Rlt_irrefl x) ; auto.
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

  Theorem Rlt_gt : forall (x y : R) , x > y <-> y < x.
  Proof.
    intros.
    split ; auto.
  Qed.

  Parameter Rplus_0 : forall r1 r2 : R , r1 - r2 = R0 <-> r1 = r2.
  Parameter Rle_ge_eq : forall x y : R , x >= y -> y >= x -> x = y.
  Parameter Dec_R : R -> nat -> nat -> Prop.
  Axiom Dec_R_inject : forall (r : R) (n m1 m2: nat) , Dec_R r n m1 -> Dec_R r n m2 -> m1 = m2.

  Definition CR (r : R) : Prop := 
      exists f : nat -> nat, (forall (n: nat),Dec_R r n (f n)).
  Definition CR1 (r : R) := {f : nat -> nat | (forall (n: nat),Dec_R r n (f n)) }.
  Definition limit (f : nat -> Q) (r : R) : Prop :=
    forall eps : Q , (eps > 0)%Q -> exists N : nat , forall n : nat , (n >= N)%nat -> Rabs(QTR (f n) - r) < QTR eps.
  (** exists a sequence of rational number limits to r *)
  Definition CR2 (r : R) := exists f : nat -> Q, limit f r.
  (** exists a Cauthy sequence of rational number limits to r *)
  Definition CR3 (r : R) :=
      {f : nat -> Q & {N : Q -> nat | limit f r /\ (forall eps : Q , (eps > 0)%Q -> forall (n m : nat) , (n >= N eps)%nat /\ (n >= 1) %nat -> (m >= n)%nat -> (Qabs(f n - f m) < eps)%Q)} }.

  Lemma ge_pow_ge : forall n: nat , (10 ^ n > n)%nat.
  Proof.
    intros.
    apply Nat.pow_gt_lin_r.
    omega.
  Qed.

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
      | S n' => (sum_f f n' + (INR (f n) / INR (10 ^ n)))%Q
    end.

  Axiom sum_f_limit_r : forall (f : nat -> nat) (r : R) , limit (sum_f f) r <-> (forall n : nat , Dec_R r n (f n)).

  Axiom sum_f_limit_eps : forall (f : nat -> nat)(n m : nat) , (n <= m) % nat -> (Qabs(sum_f f n - sum_f f m) < 1 / INR(10^n))%Q.

  Axiom sum_f_limit_lt : forall (f : nat -> nat)(r : R) , limit (sum_f f) r -> forall (n : nat) , QTR(sum_f f n) < r.

  Theorem sum_f_expand : forall (f : nat -> nat)(n : nat) , sum_f f (S n) == sum_f f n + (INR (f (S n)) / INR (10 ^ (S n))).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem f_lt_sum_f_lt : forall (f f1 : nat -> nat) , (forall n : nat , (f n < f1 n)%nat) -> (forall n : nat , (sum_f f n < sum_f f1 n)%Q).
  Proof.
    intros.
    induction n.
    - simpl. apply INR_lt. apply (H O).
    - rewrite (sum_f_expand f n). 
      rewrite (sum_f_expand f1 n).
      apply Qplus_lt_le_compat ; auto.
      apply Qlt_le_weak.
      unfold Qdiv. 
      assert (~ INR(10 ^ S n) == 0).
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H0 at 2. 
        rewrite <- INR_Qeq_0.
        apply INR_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply ge_pow_ge.
      }
      apply Qlt_shift_div_l. 
      + rewrite <- INR_Qeq_0. apply INR_lt. 
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply ge_pow_ge.
      + rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ INR (10 ^ S n)) (INR (10 ^ S n))).
        rewrite Qmult_inv_r ; auto.
        rewrite Qmult_1_r.
        apply INR_lt. auto.
  Qed.

  Theorem f_le_sum_f_le : forall (f f1 : nat -> nat) , (forall n : nat , (f n <= f1 n)%nat) -> (forall n : nat , (sum_f f n <= sum_f f1 n)%Q).
  Proof.
    intros.
    induction n.
    - simpl. apply INR_le. apply (H O).
    - rewrite (sum_f_expand f n). 
      rewrite (sum_f_expand f1 n).
      apply Qplus_le_compat; auto.
      unfold Qdiv. 
      assert (~ INR(10 ^ S n) == 0).
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H0 at 2. 
        rewrite <- INR_Qeq_0.
        apply INR_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply ge_pow_ge.
      }
      apply Qle_shift_div_l. 
      + rewrite <- INR_Qeq_0. apply INR_lt. 
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply ge_pow_ge.
      + rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ INR (10 ^ S n)) (INR (10 ^ S n))).
        rewrite Qmult_inv_r ; auto.
        rewrite Qmult_1_r.
        apply INR_le. auto.
  Qed.

  Theorem sum_f_up : forall f : nat -> nat , (forall n : nat, (f n < 10)%nat)
        -> (forall n : nat , sum_f f (S n) <= sum_f f n + INR(1) / INR (10 ^ n))%Q.
  Proof.
    intros.
    rewrite sum_f_expand. rewrite Qplus_le_r.
    assert (INR (10) / INR(10 ^ (S n)) == INR (1) / INR (10 ^ n)).
    {
      rewrite Nat.pow_succ_r'.
      rewrite <- INR_mult.
      unfold Qdiv.
      rewrite Qinv_mult_distr.
      rewrite Qmult_assoc.
      rewrite Qmult_inv_r.
      rewrite INR_Qeq_1. reflexivity.
      unfold not. intros. inversion H0.
    }
    rewrite <- H0.
    apply Qle_shift_div_l.
    - rewrite <- INR_Qeq_0. apply INR_lt. 
      apply lt_trans with (m := S n).
      destruct n ; omega.
      apply ge_pow_ge.
    - unfold Qdiv. 
      assert (~ INR(10 ^ S n) == 0).
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H1 at 2. 
        rewrite <- INR_Qeq_0.
        apply INR_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply ge_pow_ge.
      }
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (/ INR (10 ^ S n)) (INR (10 ^ S n))).
      rewrite Qmult_inv_r ; auto.
      pose proof H (S n).
      rewrite Qmult_1_r.
      apply INR_le.
      apply lt_le_weak ; auto.
  Qed.

  Theorem sum_f_down : forall (f : nat -> nat)(n : nat) , (sum_f f (S n) >= sum_f f n)%Q.
  Proof.
    intros.
    rewrite sum_f_expand.
    rewrite <- Qplus_0_r at 1.
    rewrite Qplus_le_r.
    apply Qle_shift_div_l.
    - rewrite <- INR_Qeq_0. apply INR_lt. 
      apply lt_trans with (m := S n).
      destruct n ; omega.
      apply ge_pow_ge.
    - rewrite Qmult_0_l. rewrite <- INR_Qeq_0. apply INR_le.
      omega.
  Qed.

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
    - rewrite sum_f_limit_r. auto.
    - intros.
      destruct H0.
      pose proof eps_arrow_correct eps.
      remember (eps_arrow_nat eps) as n0.
      apply Qlt_trans with (y := (1 / INR(n0))).
      + apply Qlt_trans with (y := (1 / INR(10^n))).
        * apply sum_f_limit_eps ; auto.
        * apply Qlt_shift_div_l.
          ** rewrite Heqn0. apply eps_arrow_pro ; auto.
          ** rewrite Qmult_comm.
             assert (H' : 1 / INR (10 ^ n) == / INR (10 ^ n)).
             {
               field.
               unfold not.
               intros.
               assert ((10 > 0)%nat). omega.
               pose proof INR_lt (10 ^ n) 0 (Max_powan_0 _ _ H5).
               rewrite H4 in H6.
               apply (Qlt_irrefl 0). auto.
             }
             rewrite H'.
             clear H'.
             apply Qlt_shift_div_r.
             --  rewrite <- INR_Qeq_0.
                 apply INR_lt. apply Max_powan_0. omega.
             --  rewrite Qmult_1_l.
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

  Definition mono_up (X : nat -> Q) : Prop := forall n : nat , (X (S n) >= X n)%Q.
  Definition mono_down (X : nat -> Q) : Prop := forall n : nat , (X (S n) <= X n)%Q.
  Definition mono (X : nat -> Q) : Prop := mono_up X \/ mono_down X.
  Definition upper_bound (X : nat -> Q) (U : R) : Prop := forall n : nat , QTR (X n) <= U.
  Definition Sup (X : nat -> Q) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.
  Definition lower_bound (X : nat -> Q) (L : R) : Prop := forall n : nat , L <= QTR (X n).
  Definition Inf (X : nat -> Q) (inf : R) : Prop := (forall r : R , lower_bound X r -> r <= inf) /\ lower_bound X inf.
  Definition bound (X : nat -> Q) : Prop := (exists n1 : R , upper_bound X n1) /\ (exists n2 : R ,lower_bound X n2).
  Definition f_max : nat -> nat := (fun _ => 10%nat).
  Parameter f_max_limit : R .
  Parameter limit_f_max : limit (sum_f f_max) f_max_limit.
  Parameter Sup_pro : forall (X : nat -> Q) (sup : R) , Sup X sup -> forall y : R , (y < sup -> (exists n : nat , QTR (X n) <= sup /\ y < QTR(X n))).
  Parameter Inf_pro : forall (X : nat -> Q) (inf : R) , Inf X inf -> forall y : R , (y > inf -> (exists n : nat , QTR (X n) >= inf /\ y > QTR(X n))).

  Theorem upper_bound_exists_Sup : forall (X : nat -> Q) , (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).
  Proof. Admitted.

  Theorem Sup_unique : forall (X : nat -> Q) (r1 r2 : R), Sup X r1 -> Sup X r2 -> r1 = r2.
  Proof. 
    intros.
    unfold Sup in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; apply Rle_ge ; auto.
  Qed.

  Theorem lower_bound_exists_Inf : forall (X : nat -> Q) , (exists r : R , lower_bound X r) ->
                                          (exists inf : R , Inf X inf).
  Proof. Admitted.

  Theorem Inf_unique : forall (X : nat -> Q) (r1 r2 : R), Inf X r1 -> Inf X r2 -> r1 = r2.
  Proof.
    intros.
    unfold Inf in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; auto.
  Qed.

  Theorem mono_up_pro : forall (X : nat -> Q) , mono_up X -> (forall n m : nat , (n >= m)%nat -> (X n >= X m)%Q).
  Proof.
    intros.
    unfold mono_up in H.
    induction H0.
    - lra.
    - apply Qle_trans with (X m0) ; auto.
  Qed.

  Theorem mono_up_upper_bound_seq_has_limit : forall (X : nat -> Q) , mono_up X -> (exists r : R , upper_bound X r) -> exists r : R ,limit X r.
  Proof. 
    intros.
    pose proof upper_bound_exists_Sup X H0.
    destruct H1.
    clear H0.
    exists x.
    unfold limit.
    intros.
    assert (x - QTR eps < x).
    { rewrite Rplus_0_r.
      unfold Rminus.
      apply Rlt_Rplus_l.
      rewrite <- QTR_R0.
      rewrite Ropp_QTR.
      apply QTR_lt.
      lra.
    }
    pose proof Sup_pro X x H1 (x - QTR eps) H2.
    destruct H3.
    exists x0.
    clear H2.
    destruct H3.
    intros.
    rewrite Rabs_neg.
    - rewrite Ropp_minus.
      apply Rlt_Rminus_r.
      apply Rlt_le_trans with (QTR (X x0)) ; auto.
      apply QTR_le.
      apply mono_up_pro ; auto.
    - apply Rle_neg_eqb.
      rewrite Rle_ge.
      unfold Sup in H1. destruct H1.
      auto.
  Qed.

  Theorem mono_down_pro : forall (X : nat -> Q) , mono_down X -> (forall n m : nat , (n >= m)%nat -> (X n <= X m)%Q).
  Proof.
    intros.
    unfold mono_down in H.
    induction H0.
    - lra.
    - apply Qle_trans with (X m0) ; auto.
  Qed.

  Theorem mono_down_lower_bound_seq_has_limit : forall (X : nat -> Q) , mono_down X -> (exists r : R , lower_bound X r) -> exists r : R , limit X r.
  Proof.
    intros.
    pose proof lower_bound_exists_Inf X H0.
    destruct H1.
    clear H0.
    exists x.
    unfold limit.
    intros.
    assert (x + QTR eps > x).
    { rewrite Rplus_0_r.
      unfold Rminus.
      apply Rlt_Rplus_l.
      rewrite <- QTR_R0.
      apply QTR_lt.
      lra.
    }
    pose proof Inf_pro X x H1 (x + QTR eps) H2.
    destruct H3.
    exists x0.
    clear H2.
    destruct H3.
    intros.
    rewrite Rabs_pos.
    - apply Rlt_Rminus_r.
      apply Rlt_Rminus_Rplus.
      rewrite Rplus_comm in H3.
      apply Rle_lt_trans with (QTR (X x0)) ; auto .
      apply QTR_le.
      apply mono_down_pro ; auto.
    - apply Rle_pos_eqb.
      rewrite Rle_ge in H2.
      unfold Inf in H1. destruct H1.
      auto.
  Qed.

  Theorem mono_bound_seq_has_limit : forall (X : nat -> Q) , bound X -> mono X -> exists r : R , limit X r.
  Proof.
    intros.
    unfold bound in *.
    destruct H.
    destruct H0.
    - apply mono_up_upper_bound_seq_has_limit ; auto.
    - apply mono_down_lower_bound_seq_has_limit ; auto.
  Qed.

  Theorem mono_up_sum_f : forall (f : nat -> nat) , mono_up (sum_f f).
  Proof.
    unfold mono_up.
    intros.
    rewrite sum_f_expand.
    rewrite <- Qplus_0_r at 1.
    apply Qplus_le_r.
    apply Qle_shift_div_l.
    - rewrite <- INR_Qeq_0.
      apply INR_lt.
      pose proof ge_pow_ge (S n).
      apply le_lt_trans with (m := S n) ; omega.
    - rewrite Qmult_0_l. apply INR_nonneg.
  Qed.

  Lemma all_sum_f_limit_r : forall (f : nat -> nat) , (forall n : nat, (f n < 10)%nat) -> exists r : R , limit (sum_f f) r.
  Proof.
    intros.
    apply mono_bound_seq_has_limit.
    - unfold bound.
      split .
      + exists f_max_limit. 
        unfold upper_bound.
        intros.
        pose proof sum_f_limit_lt.  
        apply Rle_trans with (r2 := QTR (sum_f f_max n)).
        * apply QTR_le. apply f_le_sum_f_le. intros.
          unfold f_max. apply lt_le_weak.
          apply H.
        * apply Rle_lt_weak.
          apply sum_f_limit_lt. apply limit_f_max.
      + exists (QTR(sum_f f 0)).
        unfold lower_bound.
        intros.
        apply QTR_le.
        induction n.
        * lra.
        * apply Qle_trans with (sum_f f n) ; auto.
          apply (sum_f_down f n).
    - unfold mono.
      left.
      apply mono_up_sum_f.
  Qed.

  Lemma all_sum_f_limit_CR2 : forall (f : nat -> nat) (r : R) , limit (sum_f f) r -> CR2 r.
  Proof.
    intros.
    unfold CR2.
    exists (sum_f f). auto.
  Qed.

  Definition Dec_f (f : nat -> nat) : Prop := (forall n : nat , (f n < 10)%nat).
  Definition Dec_f_R (r : R) : Prop := exists f : nat -> nat , Dec_f f /\ limit (sum_f f) r.

  Theorem Dec_f_R_is_CR2 : forall r : R , Dec_f_R r -> CR2 r.
  Proof.
    intros.
    destruct H.
    apply (all_sum_f_limit_CR2 x r).
    destruct H. auto.
  Qed.

End Vir_R.
