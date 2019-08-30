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
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Classes.Equivalence.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Classes.RelationClasses.
Require Import Ring.
From Coq Require Import Field.
From Coq Require Import Omega.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
From CReal Require Import Countable.
From CReal Require Import INQ_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import ComRealBase.
From CReal Require Import ComRealField.
From CReal Require Import ComRealBaseLemma1.

Module VirRLemmas (VirR : VIR_R).
  Module RF := VirR_Field (VirR).
  Module Lemma1 := VirRLemma1 (VirR).
  Import VirR RF Lemma1.
  Local Open Scope R_scope.
  
  Theorem Rabs_le_0 : forall r : R , Rabs r >= 0.
  Proof.
    intros.
    destruct (Rtotal_order r 0).
    - rewrite Rabs_neg ; auto with Vir_real.
      rewrite <- Ropp_0. auto with Vir_real.
    - rewrite or_comm in H. rewrite Rabs_pos ; auto.
  Qed.
  
  Hint Resolve Rabs_le_0 : Vir_real.
  Theorem Rabs_le : forall r : R , r <= Rabs r.
  Proof.
    intros.
    destruct (Rtotal_order r 0).
    - apply Rle_trans with 0 ; auto with Vir_real.
    - rewrite or_comm in H. rewrite Rabs_pos ; auto with Vir_real.
  Qed.
  Hint Resolve Rabs_le : Vir_real.
   
  Theorem IQR_inv : forall r : Q, (~ r == 0)%Q -> / IQR r = IQR (/ r).
  Proof. 
    intros.
    destruct r.
    simpl. unfold Rdiv , Qinv. simpl.
    assert (forall p , IPR p <> 0). { intros. rewrite <- INR_IPR. auto with Vir_real. } 
    destruct Qnum ; simpl.
    - assert (0 # Qden == 0). { unfold Qeq. auto. }
      exfalso. auto.
    - unfold IZR. field. split ; auto.
    - unfold IZR. field. split ; auto. 
  Qed.
  Hint Resolve IQR_inv : Vir_real.
  
  Theorem Rlt_opp : forall r : R , r > R0 -> - r < R0.
  Proof. auto with Vir_real. Qed.
  Theorem Rle_opp : forall r : R , r >= R0 -> - r <= R0.
  Proof. auto with Vir_real. Qed.
  Hint Resolve Rlt_opp Rle_opp : Vir_real.

  Theorem Rlt_pos_eqb : forall r1 r2 : R  , r1 < r2 <-> r2 - r1 > R0.
  Proof. 
    split ; intros.
    - apply Rlt_Rminus. auto.
    - apply Rminus_gt. auto.
  Qed.
  
  Theorem Rlt_neg_eqb : forall r1 r2 : R  , r1 > r2 <-> r2 - r1 < R0.
  Proof.
    split ; intros ; auto with Vir_real.
    hnf. apply Rminus_lt. auto.
  Qed.
  
  Hint Resolve Rlt_pos_eqb Rlt_neg_eqb : Vir_real.
  
  Theorem Rle_pos_eqb : forall r1 r2 : R  , r1 <= r2 <-> r2 - r1 >= R0.
  Proof.
    split ; intros ; destruct H.
    - left. rewrite <- Rlt_pos_eqb. auto.
    - right. subst. ring.
    - left. apply Rlt_pos_eqb. auto.
    - right. subst. auto with Vir_real.
  Qed.
   
  Theorem Rle_neg_eqb : forall r1 r2 : R  , r1 >= r2 <-> r2 - r1 <= R0.
  Proof.
    split ; intros ; destruct H.
    - left. rewrite <- Rlt_neg_eqb. auto.
    - right. subst. ring.
    - left. apply Rlt_neg_eqb. auto.
    - right. subst. auto with Vir_real.
  Qed. 

  Hint Resolve Rle_pos_eqb Rle_neg_eqb : Vir_real.
  
  Theorem Rmult_le_l : forall r1 r2 r3 : R , r3 > R0 -> r3 * r1  <= r3 * r2 <-> r1 <= r2.
  Proof.  split ; intros ; auto with Vir_real. apply Rmult_le_reg_l with r3 ; auto. Qed.
  
  Theorem Rmult_lt_l : forall r1 r2 r3 : R , r3 > R0 -> r3 * r1 < r3 * r2 <-> r1 < r2.
  Proof.  split ; intros ; auto with Vir_real. apply Rmult_gt_reg_l with r3 ; auto. Qed.
  
  Theorem Rmult_le_r : forall r1 r2 r3 : R , r3 > R0 -> r1 * r3 <= r2 * r3 <-> r1 <= r2.
  Proof.  split ; intros ; auto with Vir_real. apply Rmult_le_reg_r with r3 ; auto. Qed.
  
  Theorem Rmult_lt_r : forall r1 r2 r3 : R , r3 > R0 -> r1 * r3 < r2 * r3 <-> r1 < r2.
  Proof. split ; intros ; auto with Vir_real. apply Rmult_lt_reg_r with r3 ; auto. Qed.
  
  Hint Resolve Rmult_le_l Rmult_le_r  Rmult_lt_l Rmult_le_l : Vir_real.
  
  Theorem Rmult_lt_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 < r2 * r3 <-> r1  / r3  < r2.
  Proof. 
    split ; intros ; auto with Vir_real.
    - apply Rmult_lt_r with r3 ; auto.
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r. auto.
      auto with Vir_real.
    - apply Rmult_lt_r with (/ r3 ) ; auto.
      apply Rinv_0_lt_compat ; auto.
      rewrite Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. auto.
      auto with Vir_real.
  Qed.
  
  Theorem Rmult_le_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 <= r2 * r3 <-> r1 / r3 <= r2.
  Proof.
    split ; intros ; auto with Vir_real.
    - apply Rmult_le_r with r3 ; auto.
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r. auto.
      auto with Vir_real.
    - apply Rmult_le_r with (/ r3) ; auto.
      apply Rinv_0_lt_compat ; auto. 
      rewrite Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. auto.
      auto with Vir_real.
  Qed.
  
  Hint Resolve Rmult_lt_divr Rmult_le_divr : Vir_real.
  
  Theorem Rmult_gt_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 > r2 * r3 <-> r1 / r3  > r2.
  Proof.
    split ; intros ; auto with Vir_real.
    - apply Rmult_lt_r with r3 ; auto.
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r. auto.
      auto with Vir_real.
    - apply Rmult_lt_r with (/ r3) ; auto.
      apply Rinv_0_lt_compat ; auto. 
      rewrite Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. auto.
      auto with Vir_real.
  Qed.

  Theorem Rmult_ge_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 >= r2 * r3 <-> r1 / r3 >= r2.
  Proof.
    split ; intros ; apply Rle_ge ; auto with Vir_real.
    - apply Rmult_le_r with r3 ; auto.
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l ; auto with Vir_real. rewrite Rmult_1_r. 
      auto with Vir_real.
    - apply Rmult_le_r with (/ r3) ; auto.
      apply Rinv_0_lt_compat ; auto. 
      rewrite Rmult_assoc. rewrite Rinv_r ; auto with Vir_real. rewrite Rmult_1_r. 
      auto with Vir_real.
  Qed.
  
  Hint Resolve Rmult_gt_divr Rmult_ge_divr : Vir_real.
  
  Theorem Rlt_Rlt_minus : forall r1 r2 r3 r4 : R , r1 < r2 -> r3 < r4 -> r3 - r2 < r4 - r1.
  Proof. intros. apply Rplus_lt_reg_r with (r2 + r1). 
    assert (r3 - r2 + (r2 + r1) = r3 + r1). { ring. }
    assert (r4 - r1 + (r2 + r1) = r4 + r2). { ring. }
    rewrite H1 , H2.
    auto with Vir_real.
  Qed.
  
  Theorem Rle_Rle_minus : forall r1 r2 r3 r4 : R , r1 <= r2 -> r3 <= r4 -> r3 - r2 <= r4 - r1.
  Proof. intros. apply Rplus_le_reg_r with (r2 + r1). 
    assert (r3 - r2 + (r2 + r1) = r3 + r1). { ring. }
    assert (r4 - r1 + (r2 + r1) = r4 + r2). { ring. }
    rewrite H1 , H2.
    auto with Vir_real.
  Qed.
  
  Theorem Rlt_Rle_minus : forall r1 r2 r3 r4 : R , r1 < r2 -> r3 <= r4 -> r3 - r2 < r4 - r1.
  Proof. intros. apply Rplus_lt_reg_r with (r2 + r1). 
    assert (r3 - r2 + (r2 + r1) = r3 + r1). { ring. }
    assert (r4 - r1 + (r2 + r1) = r4 + r2). { ring. }
    rewrite H1 , H2.
    auto with Vir_real.
  Qed.
  
  Theorem Rle_Rlt_minus : forall r1 r2 r3 r4 : R , r1 <= r2 -> r3 < r4 -> r3 - r2 < r4 - r1.
  Proof. intros. apply Rplus_lt_reg_r with (r2 + r1). 
    assert (r3 - r2 + (r2 + r1) = r3 + r1). { ring. }
    assert (r4 - r1 + (r2 + r1) = r4 + r2). { ring. }
    rewrite H1 , H2.
    auto with Vir_real.
  Qed.
  Hint Resolve Rlt_Rlt_minus Rle_Rlt_minus Rlt_Rle_minus Rle_Rle_minus : Vir_real.
  
  Theorem Rlt_Rminus_r : forall r1 r2 r3: R , r1 - r2 < r3 -> r1 - r3 < r2.
  Proof. intros. apply Rplus_lt_reg_r with (r3 - r2). 
    assert (r1 - r3 + (r3 - r2) = r1 - r2). { ring. }
    assert (r2 + (r3 - r2) = r3). { ring. }
    rewrite H0 , H1.
    auto with Vir_real.
  Qed.
  
  Theorem Rlt_Rminus_Rplus : forall r1 r2 r3: R , r1 < r2 + r3 <-> r1 - r2 < r3.
  Proof. split ; intros .
    - apply Rplus_lt_reg_r with r2. 
      assert (r1 - r2 + r2 = r1). { ring. }  rewrite H0. rewrite Rplus_comm. auto.
    - apply Rplus_lt_reg_r with (-r2). 
      assert (r2 + r3 + - r2 = r3). { ring. } rewrite H0. auto.
  Qed.
  
  Theorem Rle_Rminus_r : forall r1 r2 r3: R , r1 - r2 <= r3 -> r1 - r3 <= r2.
  Proof. intros. apply Rplus_le_reg_r with (r3 - r2).
    assert (r1 - r3 + (r3 - r2) = r1 - r2). { ring. }
    assert (r2 + (r3 - r2) = r3). { ring. }
    rewrite H0 , H1. auto.
  Qed.
  
  Theorem Rle_Rminus_Rplus : forall r1 r2 r3: R , r1 <= r2 + r3 <-> r1 - r2 <= r3.
  Proof. split ; intros .
    - apply Rplus_le_reg_r with r2. 
      assert (r1 - r2 + r2 = r1). { ring. }  rewrite H0. rewrite Rplus_comm. auto.
    - apply Rplus_le_reg_r with (-r2). 
      assert (r2 + r3 + - r2 = r3). { ring. } rewrite H0. auto.
  Qed.
  
  Hint Resolve Rlt_Rminus_r  Rlt_Rminus_Rplus  Rle_Rminus_r Rle_Rminus_Rplus : Vir_real.
  
  Theorem Rle_Rminus :forall r1 r2 r3 : R , r1 + r3 <= r2 <-> r1 <= r2 - r3.
  Proof. split ; intros.
    - apply Rplus_le_reg_r with r3. 
      assert (r2 - r3 + r3 = r2). { ring. }  rewrite H0. auto.
    - apply Rplus_le_reg_r with (-r3). 
      assert (r1 + r3 + - r3 = r1). { ring. } rewrite H0. auto.
  Qed.
  Hint Resolve Rle_Rminus : Vir_real.

  Theorem Rlt_opp_eqb :forall r1 r2 :R , r1 < -r2 <->  r2 < - r1.
  Proof. split ; intros ; rewrite <- Ropp_involutive at 1;  apply Ropp_lt_contravar; auto. Qed.
    
  Theorem Rle_opp_eqb :forall r1 r2 :R , r1 <= -r2 <-> r2 <= - r1.
  Proof. split ; intros ; rewrite <- Ropp_involutive at 1; apply Ropp_le_contravar ; auto. Qed.
  
  Hint Resolve Rlt_opp_eqb Rle_opp_eqb : Vir_real.
  
  Theorem Rgt_Rinv : forall r1 : R , r1 > R1 -> r1 > / r1.
  Proof. intros. assert (r1 > 0). { apply Rlt_trans with 1 ; auto with Vir_real. }
    apply Rmult_lt_r with r1 ; auto.
    rewrite Rinv_l ; auto with Vir_real.
    apply Rlt_trans with r1 ; auto.
    rewrite <- Rmult_1_r at 1. apply Rmult_lt_l ; auto.
  Qed.
  
  Theorem Rge_Rinv : forall r1 : R , r1 >= R1 -> r1 >= / r1.
  Proof. intros. assert (r1 > 0). { apply Rlt_le_trans with 1 ; auto with Vir_real. }
    apply Rle_ge.
    apply Rmult_le_r with r1 ; auto.
    rewrite Rinv_l ; auto with Vir_real.
    apply Rle_trans with r1 ; auto with Vir_real.
    rewrite <- Rmult_1_r at 1. apply Rmult_le_compat_l ; auto with Vir_real.
  Qed.
  
  Theorem Rlt_Rinv : forall r1 : R , r1 < R1 /\ r1 > R0 -> r1 < / r1.
  Proof.  intros. destruct H.
    apply Rmult_lt_r with r1 ; auto.
    rewrite Rinv_l ; auto with Vir_real.
    apply Rlt_trans with r1 ; auto with Vir_real.
    rewrite <- Rmult_1_r. apply Rmult_lt_l ; auto with Vir_real.
  Qed.
  
  Theorem Rle_Rinv : forall r1 : R , r1 <= R1 /\ r1 > R0 -> r1 <= / r1.
  Proof. intros. destruct H.
    apply Rmult_le_r with r1 ; auto.
    rewrite Rinv_l ; auto with Vir_real.
    apply Rle_trans with r1 ; auto with Vir_real.
    rewrite <- Rmult_1_r. apply Rmult_le_l ; auto with Vir_real.
  Qed.
  
  Hint Resolve Rgt_Rinv Rge_Rinv Rlt_Rinv Rle_Rinv : Vir_real.
  
  Definition archimedean : nat -> R -> Prop .
    intros n r.
    apply (IQR (INQ n) <= r /\ r < IQR (INQ (n + 1))).
  Defined.
  
  Theorem archimedean_exists : forall r : R , r >=0 -> exists x : nat , archimedean x r.
  Proof.  
    intros.
    elim archimed with r ; intros.
    exists (Z.to_nat (x - 1)).
    destruct H0.
    assert (x > 0)%Z. { apply Z.lt_gt. apply lt_IZR. rewrite IZR_R0. apply Rle_lt_trans with r ; auto with Vir_real. }
    split ;  rewrite INQ_IQR_INR ;  rewrite INR_IZR_INZ.  
    - rewrite Z2Nat.id ; try (omega).
      rewrite minus_IZR. rewrite IZR_R1.
      apply Rminus_le. apply Rle_minus in H1.  
      assert (IZR x - r - 1 = IZR x - 1 - r). { ring. }
      rewrite <- H3. auto.
    - rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id ; try (omega). simpl.
      assert (x - 1 + 1 = x)%Z. { ring. }
      rewrite H3. auto with Vir_real.
  Qed.
  
  Definition Same_Ipart : R -> R -> Prop.
    intros.
    apply (exists a : nat , IQR (INQ (a)) <= X /\ IQR (INQ (a)) <= X0 /\ X < IQR (INQ (a + 1)) /\ X0 < IQR (INQ (a + 1))).
  Defined.
  
  Definition Same_Ipart_n(r : R)(n : nat) : Prop := Same_Ipart (r * INR (10 ^ n)) (((r + INR 1 / INR (10 ^ S n))) * INR (10 ^ n)).
  
  Theorem Ipart_unique : forall (r : R)(n m : nat) , archimedean n r -> archimedean m r -> n = m%Z.
  Proof.
    intros.
    destruct H , H0.
    rewrite INQ_IQR_INR in *.
    rewrite plus_INR in *.
    assert (INR 1 = 1). { auto. }
    rewrite H3 in *. clear H3.
    rewrite INR_IZR_INZ in *.
    assert (r - 1 + 1 = r). { ring. }
    rewrite <- H3 in H1 , H2.
    apply Rplus_lt_reg_r in H1.
    apply Rplus_lt_reg_r in H2.
    apply Nat2Z.inj.
    apply one_IZR_r_R1 with (r - 1) ; rewrite H3 ; split ; auto.
  Qed.
  
  Theorem Same_Ipart_mult : forall (r1 r2 : R)(k : nat) , (k > 0)%nat -> 
                Same_Ipart (r1 * (INR k)) (r2 * (INR k)) -> Same_Ipart r1 r2.
  Proof.
    intros.
    destruct H0 , H0 , H1 , H2.
    rewrite !INQ_IQR_INR in *.
    assert (INR (k) > 0).
    { apply lt_INR in H. auto with Vir_real. }
    apply Rmult_le_divr in H0; auto.
    apply Rmult_le_divr in H1; auto.
    apply Rmult_gt_divr in H2; auto.
    apply Rmult_gt_divr in H3; auto.
    destruct (archimedean_exists (INR x / INR k)).
    apply Rmult_ge_divr ; auto. rewrite Rmult_0_l. auto with Vir_real.
    destruct H5. rewrite !INQ_IQR_INR in *.
    assert (INR (x + 1) / INR k <= INR (x0 + 1)).
    { apply Rmult_le_divr ; auto.
      rewrite <- Rmult_lt_divr in H6 ; auto.
      rewrite <- mult_INR in *.
      apply le_INR. apply INR_lt in H6.
      omega.
    }
    exists x0. rewrite !INQ_IQR_INR.
    repeat split.
    - apply Rle_trans with (INR x / INR k) ; auto.
    - apply Rle_trans with (INR x / INR k) ; auto.
    - apply Rlt_le_trans with (INR (x + 1) / INR k) ; auto.
    - apply Rlt_le_trans with (INR (x + 1) / INR k) ; auto.
  Qed.

  Definition Un_cv (A : nat -> R -> Prop) (r : R) : Prop :=
    is_function A /\ (
    forall eps : R , eps > R0 -> (exists n : nat , 
          forall (m : nat) (r1 : R) , (m >= n)%nat -> A m r1 -> Rabs(r1 - r) < eps)).
  
  Theorem Un_cv_inject : forall (X : nat -> R -> Prop) (r1 r2 : R) , Un_cv X r1 -> Un_cv X r2 -> r1 = r2.
  Proof. 
    intros.
    hnf in *.
    apply NNPP.
    intro.
    apply Rdichotomy in H1. destruct H , H0.
    destruct H , H0.
    destruct H1 ; apply Rlt_mid in H1 ; destruct H1 ; destruct H1 ;
    apply IQR_lt in H1 ; rewrite IQR_R0 in H1; 
    specialize (H2 (IQR x) H1) ; specialize (H3 (IQR x) H1) ; destruct H2 , H3 ; destruct (H (max x0 x1));
    destruct (H0 (max x0 x1)) ; 
    specialize (H2 (max x0 x1) x2 (Nat.le_max_l x0 x1) H7 ) ; specialize (H3 (max x0 x1) x3 (Nat.le_max_r x0 x1) H8); 
    apply Rabs_tri in H2 ; apply Rabs_tri in H3 ; destruct H2 , H3 ; specialize (H4 (max x0 x1) x2 x3 H7 H8) ; subst ;
    apply (Rlt_irrefl x3). 
    - apply Rlt_trans with (r1 + IQR x) ; auto.
      apply Rlt_trans with (r2 - IQR x) ; auto.
    - apply Rlt_trans with (r2 + IQR x) ; auto.
      apply Rlt_trans with (r1 - IQR x) ; auto.
  Qed.
  
  Definition mono_up (X : nat -> R -> Prop) : Prop := is_function X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q >= q1).
  Definition mono_down (X : nat -> R -> Prop) : Prop := is_function X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q <= q1).
  Definition mono (X : nat -> R -> Prop) : Prop := mono_up X \/ mono_down X.
  Definition lower_bound (X : nat -> R -> Prop) (L : R) : Prop := forall (n : nat)(q : R) , X n q -> L <= q.
  Definition Inf (X : nat -> R -> Prop) (inf : R) : Prop := (forall r : R , lower_bound X r -> r <= inf) /\ lower_bound X inf.
  Definition bound (X : nat -> R -> Prop) : Prop := (exists n1 : R , upper_bound X n1) /\ (exists n2 : R ,lower_bound X n2).

  Theorem Sup_pro : forall (X : nat -> R -> Prop) (sup : R) , is_function X -> Sup X sup -> forall y : R , (y < sup -> 
                              (exists n : nat , forall q : R , X n q -> ( q <= sup /\ y < q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0.
    apply Rlt_not_ge in H1.
    apply H1.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q = q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply (H5 n) ; auto.
    - apply Rnot_lt_ge in H3. auto with Vir_real. 
  Qed.
  
  Theorem Inf_pro : forall (X : nat -> R -> Prop) (inf : R) , is_function X -> Inf X inf -> forall y : R , (y > inf -> 
                              (exists n : nat , forall q : R , X n q -> (q >= inf /\ y > q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0.
    apply Rlt_not_ge in H1.
    apply H1. apply Rle_ge.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q = q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply Rle_ge. apply (H5 n); auto.
    - apply Rnot_gt_le in H3. auto.
  Qed.

  Theorem upper_bound_T_lower_bound : forall (X P : nat -> R -> Prop) , is_function X -> is_function P
                                                                     -> (forall n r , X n r <-> P n (-r)) 
                                                                      -> forall r , upper_bound X r <-> lower_bound P (-r).
  Proof.
    intros.
    split ; intros.
    - hnf. intros.
      specialize (H1 n (-q)).
      rewrite <- Ropp_involutive in H3.
      rewrite <- H1 in H3.
      specialize (H2 n (-q) H3).
      rewrite <- Ropp_involutive. rewrite <- Ropp_involutive in H2.
      apply Rle_opp_eqb ; auto.
    - hnf. intros.
      specialize (H1 n q).
      rewrite H1 in H3.
      specialize (H2 n (-q) H3).
      rewrite <- Ropp_involutive. apply Rle_opp_eqb ; auto.
  Qed.
  
  Theorem lower_bound_exists_Inf : forall (X : nat -> R -> Prop) , is_function X -> (exists r : R , lower_bound X r) ->
                                          (exists inf : R , Inf X inf).
  Proof.
    intros.
    destruct H0.
    set (fun (n : nat)(r : R) => X n (-r)).
    assert (is_function P).
    {
      destruct H.
      split.
      - intro. destruct (H a). exists (-x0).
        rewrite <- Ropp_involutive in H2.
        apply H2.
      - intro. intros.
        specialize (H1 a (-b1) (-b2) H2 H3).
        rewrite <- Ropp_involutive at 1. rewrite <- Ropp_involutive.
        rewrite H1. auto.
    }
    assert (exists x , upper_bound P x).
    {
      exists (-x).
      apply (upper_bound_T_lower_bound P X) ; auto.
      - intros.  split; auto.
      - rewrite Ropp_involutive. auto.
    }
    pose proof upper_bound_exists_Sup P H1 H2.
    destruct H3.
    exists (-x0).
    destruct H3.
    split.
    - intros.
      assert (upper_bound P (-r)).
      { apply (upper_bound_T_lower_bound P X) ; auto.
        - intros. split; auto.
        - rewrite Ropp_involutive. auto.
      }
      specialize (H3 (-r) H6).
      apply Rge_le in H3.
      apply Rle_opp_eqb ; auto.
    - apply (upper_bound_T_lower_bound P X) ; auto.
      intros. split ; auto.
  Qed.
  
  Theorem Sup_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Sup X r1 -> Sup X r2 -> r1 = r2.
  Proof. 
    intros.
    unfold Sup in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with Vir_real.
  Qed.

  Theorem Inf_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Inf X r1 -> Inf X r2 -> r1 = r2.
  Proof.
    intros.
    unfold Inf in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with Vir_real.
  Qed.

  Theorem mono_up_upper_bound_seq_has_limit : forall (X : nat -> R -> Prop) , mono_up X -> (exists r : R , upper_bound X r) -> exists r : R ,Un_cv X r.
  Proof. 
    intros.
    destruct H.
    pose proof upper_bound_exists_Sup X H H0.
    destruct H2.
    clear H0.
    exists x.
    unfold Un_cv , mono_up in *.
    split ; auto.
    intros.
    assert (x - eps < x).
    { rewrite <- Rplus_0_r.
      apply Rplus_lt_compat_l.
      apply Rlt_opp. auto.
    }
    pose proof Sup_pro X x H H2 (x - eps) H3.
    destruct H4 , H.
    exists x0.
    intros.
    rewrite Rabs_neg.
    - rewrite Ropp_minus_distr'.
      apply Rlt_Rminus_r.
      destruct (H x0).
      apply Rlt_le_trans with x1.
      + apply H4 ; auto.
      + apply Rge_le. apply (H1 m x0) ; auto.
    - apply Rle_neg_eqb.
      apply Rle_ge.
      destruct H2.
      apply (H8 m) ; auto.
  Qed. 

  Theorem mono_up_limit_sup : forall (X : nat -> R -> Prop) , mono_up X -> (exists r : R , upper_bound X r) -> forall r : R , Un_cv X r -> Sup X r.
  Proof.
    intros.
    destruct H.
    pose proof upper_bound_exists_Sup X H H0.
    destruct H3.
    clear H0.
    assert (r = x).
    {
      apply (Un_cv_inject X) ; auto.
      unfold Un_cv , mono_up in *.
      split ; auto.
      intros.
      assert (x - eps < x).
      { rewrite <- Rplus_0_r.
        apply Rplus_lt_compat_l.
        apply Rlt_opp. auto.
      }
      pose proof Sup_pro X x H H3 (x - eps) H4.
      destruct H5 , H.
      exists x0.
      intros.
      rewrite Rabs_neg.
      - rewrite Ropp_minus_distr'.
        apply Rlt_Rminus_r.
        destruct (H x0).
        apply Rlt_le_trans with x1.
        + apply H5 ; auto.
        + apply Rge_le. apply (H2 m x0) ; auto.
      - apply Rle_neg_eqb.
        apply Rle_ge.
        destruct H3.
        apply (H9 m) ; auto.
    }
    subst. auto.
  Qed.
  
  Theorem mono_down_lower_bound_seq_has_limit : forall (X : nat -> R -> Prop) , mono_down X -> (exists r : R , lower_bound X r) -> exists r : R , Un_cv X r.
  Proof.
    intros.
    destruct H.
    pose proof lower_bound_exists_Inf X H H0.
    destruct H2.
    clear H0.
    exists x.
    unfold Un_cv , mono_down in *.
    split ; auto.
    intros.
    assert (x + eps > x).
    { rewrite <- Rplus_0_r.
      apply Rplus_lt_compat_l.
      auto.
    }
    pose proof Inf_pro X x H H2 (x + eps) H3.
    destruct H4 , H.
    exists x0.
    clear H0.
    intros.
    rewrite Rabs_pos.
    - apply Rlt_Rminus_r.
      apply Rlt_Rminus_Rplus.
      rewrite Rplus_comm in H3.
      destruct (H x0).
      apply Rle_lt_trans with x1.
      + apply (H1 m x0) ; auto.
      + rewrite Rplus_comm. apply (H4 x1) ; auto.
    - apply Rle_pos_eqb.
      destruct H2.
      apply (H7 m) ; auto.
  Qed. 

  Theorem mono_bound_seq_has_limit : forall (X : nat -> R -> Prop) , bound X -> mono X -> exists r : R , Un_cv X r.
  Proof.
    intros.
    unfold bound in *.
    destruct H.
    destruct H0.
    - apply mono_up_upper_bound_seq_has_limit ; auto.
    - apply mono_down_lower_bound_seq_has_limit ; auto.
  Qed.
  Theorem mod_exists : forall r a b : nat , (b <> 0)%nat -> (r < b)%nat -> (a mod b = r)%nat -> exists p : nat , (a = b * p + r)%nat.
  Proof.
    intros.
    exists (a / b)%nat. inversion H1.
    apply Nat.div_mod. auto.
  Qed.
  
  Theorem archimedean_extend : forall r1 r2 : R , r1 > R0 /\ r2 > R0 -> exists n : nat , INR n * r2 > r1.
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H0.
    set (fun (n : nat)(r : R) => r = INR n * r2).
    assert (is_function P).
    {
      subst P.
      split ; hnf ; intros.
      - exists (INR a * r2). auto.
      - subst ; auto.
    }
    assert (upper_bound P r1).
    { hnf ; intros.
      subst P.
      simpl in *.
      subst.
      apply Rnot_gt_le.
      apply (H1 n).
    }
    assert (exists r : R , upper_bound P r).
    { exists r1 ; auto. }
    pose proof upper_bound_exists_Sup _ H2 H4.
    destruct H5.
    pose proof (Sup_pro _ _ H2 H5).
    assert (x - r2 < x). 
    {
      apply Rlt_Rminus_r.
      assert (x - x = R0). { ring. }
      rewrite H7. apply H.
    }
    specialize (H6 (x - r2) H7).
    destruct H6.
    destruct H2.
    destruct (H2 x0).
    specialize (H6 x1 H9).
    destruct H6.
    apply Rlt_Rminus_Rplus in H10.
    destruct H5.
    hnf in H11.
    apply (Rlt_irrefl x).
    apply Rlt_le_trans with (r2 + x1) ; auto.
    assert (P (S x0) (r2 + x1)).
    {
      subst P.
      simpl in *.
      subst.
      rewrite <- Rmult_1_l at 1.
      rewrite Rmult_plus_distr_l.
      rewrite <- Rmult_assoc.
      rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      assert (INR 1 = 1). { auto. }
      rewrite <- H9. rewrite Rplus_comm.
      rewrite <- plus_INR.
      destruct x0 ; auto. 
    }
    apply (H11 (S x0) (r2 + x1) H12).
  Qed.
  
  Theorem eps_gt_10n :forall eps : R , eps > R0 -> exists n : nat , INR 1 / INR (10 ^ n) < eps.
  Proof.
     intros.
     assert (INR 1 > R0 /\ eps > R0).
     { split; auto. assert (INR 0 = 0). { auto. }
       rewrite <- H0. apply lt_INR. omega.
     }
     pose proof (archimedean_extend (INR 1) eps H0).
     destruct H1.
     destruct H0.
     exists x.
     apply Rmult_lt_divr.
     - apply Rlt_le_trans with (INR 1) ; auto.
       apply le_INR. apply Max_powan_0. omega.
     - apply Rlt_trans with (INR x * eps) ; auto.
       rewrite (Rmult_comm eps (INR (10 ^ x))).
       apply Rmult_lt_r ; auto.
       apply lt_INR.
       apply Nat.pow_gt_lin_r. omega.
  Qed.
  
  Theorem Req_same : forall r1 r2 : R , r1 = r2 <-> forall eps : R , eps > R0 -> Rabs(r1 - r2) < eps.
  Proof.
    intros.
    split; intros ; subst ; try (reflexivity).
    - unfold Rminus. rewrite Rplus_opp_r. rewrite Rabs_pos. apply Rlt_gt. auto.
      apply Rle_refl.
    - apply NNPP.
      intro.
      apply Rdichotomy in H0.
      destruct H0.
      + apply Rlt_neg_eqb in H0.
        assert (r1 - r2 <= R0). { auto with Vir_real. }
        apply Rlt_neg_eqb in H0. apply Rlt_pos_eqb in H0.
        apply eps_gt_10n in H0.
        destruct H0.
        apply (Rlt_irrefl (INR 1 / INR (10 ^ x))).
        apply Rlt_trans with (Rabs (r1 - r2)) ; auto.
        rewrite (Rabs_neg (r1 - r2)) ; auto.
        rewrite Ropp_minus_distr'. auto.
        apply H.
        apply Rmult_gt_divr.
        * rewrite <- INR_R0. apply lt_INR.
          apply Max_powan_0. omega.
        * rewrite Rmult_0_l. rewrite <- INR_R0. apply lt_INR. omega.
     + apply Rlt_pos_eqb in H0.
        assert (r1 - r2 >= R0). { apply Rle_ge. auto with Vir_real. }
        apply eps_gt_10n in H0.
        destruct H0.
        apply (Rlt_irrefl (INR 1 / INR (10^ x))).
        apply Rlt_trans with (r1 - r2) ; auto.
        rewrite <- (Rabs_pos (r1 - r2)) ; auto.
        apply H.
        apply Rmult_gt_divr.
        * rewrite <- INR_R0. apply lt_INR. apply Max_powan_0. omega.
        * rewrite Rmult_0_l. rewrite <- INR_R0. apply lt_INR. omega.
  Qed.

  Theorem Z_same_R' : forall z1 z2 : Z , (z1 <> z2)%Z <-> IZR z1 <> IZR z2.
  Proof. split ; intros ; auto with Vir_real.
    apply Rdichotomy in H.
    destruct H ; apply lt_IZR in H ; omega.
  Qed.
  
  Theorem Ex_Z_R' : forall z : Z , (z <> 0)%Z <-> IZR z <> R0.
  Proof.
    split ; intros ; auto with Vir_real.
    rewrite <- IZR_R0 in H.
    apply Rdichotomy in H. destruct H ; apply lt_IZR in H ; omega.
  Qed.

End VirRLemmas.
