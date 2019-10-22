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
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Classes.Equivalence.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Classes.RelationClasses.
Require Import Ring.
From Coq Require Import Field.
From Coq Require Import Omega.
From CReal Require Import Uncomputable.TMSet.
From CReal Require Import INQ_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import ComRealBase.
From CReal Require Import ComRealField.
From CReal Require Import ComRealBaseLemma1.
From CReal Require Import ComRealLemmas.
From CReal Require Import ComRealBase_Dec.
From CReal Require Import ComRealBase_TMR.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
Import TM_u_u.

Module Wrong_Up (VirR_ex : VIR_R_EXTRA).
  Module TR := VirR_ex.VirR.
  Module TMR := TMR_Set (VirR_ex).
  Import TR VirR_ex.
  Export TMR.
  Local Open Scope R_scope.
  
  Parameter up : R -> Z.
  Parameter Up_R0 : (up R0 = 0)%Z.
  Axiom up_comp : Proper (Req ==> eq) up.
  Existing Instance up_comp .
  
  Theorem Up_same : forall (r1 r2 : R) , r1 == r2 -> (up r1 = up r2)%Z.
  Proof.
    intros. rewrite H. 
    auto.
  Qed.
  
  Theorem Up_R : (forall (r : R) (z : Z) , IZR (z - 1) < r /\ r <= IZR z <-> (up r = z)%Z) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof TMR_get i.
    remember (Get_TMR i) as X0.
    clear HeqX0.
    pose proof Z.eq_dec (up X0) 0%Z.
    destruct H0. pose proof H2. destruct H2.
    destruct H1.
    - rewrite <- (H X0 0%Z) in e.
      simpl in *. destruct e.
      rewrite IZR_R0 in H5.
      apply Rge_le in H2.
      pose proof conj H5 H2.
      assert (X0 == 0). { auto with real. }
      clear H6.
      pose proof H7 as H6. clear H7.
      right.
      rewrite Dec_R_eq in H6 ; auto ; try (apply In_Search_R0).
      intros.
      clear H5 H4 H3 H2 H1.
      specialize (H0 j).
      rewrite H6 in H0.
      assert (Nat.b2n (TM i j) = 0)%nat.
      { apply (partial_functional_Dec_R R0 j) ; auto. apply Zero_Dec. }
      apply Nat.b2n_inj. auto.
    - left. destruct H2.
      + apply Dec_R_gt in H1 ; auto ; try (apply In_Search_R0).
        repeat destruct H1. exists x.
        specialize (H0 x).
        destruct (TM i x) ; auto.
        simpl in *.
        pose proof Zero_Dec x.
        exfalso. apply (lt_irrefl O). apply H1 ; auto.
      + apply Up_same in H1.
        exfalso. apply n.
        rewrite H1. apply Up_R0.
  Qed.

End Wrong_Up.

Module CR_uu (VirR_ex : VIR_R_EXTRA).
  Module TR := VirR_ex.VirR.
  Module TMR := TMR_Set (VirR_ex).
  Import TR VirR_ex.
  Export TMR.
  Local Open Scope R_scope.

  Fixpoint sum_f (f : nat -> nat) (n : nat) : Q :=
    match n with
      | 0%nat => INQ (f 0%nat)
      | S n' => (sum_f f n' + (INQ (f n) / INQ (10 ^ n)))%Q
    end.
    
  Theorem sum_f_expand : forall (f : nat -> nat)(n : nat) , (sum_f f (S n) == sum_f f n + (INQ (f (S n)) / INQ (10 ^ (S n))))%Q.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem f_lt_sum_f_lt : forall (f f1 : nat -> nat) , (forall n : nat , (f n < f1 n)%nat) -> (forall n : nat , (sum_f f n < sum_f f1 n)%Q).
  Proof.
    intros.
    induction n.
    - simpl. apply INQ_lt. apply (H O).
    - rewrite (sum_f_expand f n). 
      rewrite (sum_f_expand f1 n).
      apply Qplus_lt_le_compat ; auto.
      apply Qlt_le_weak.
      unfold Qdiv. 
      assert (~ INQ(10 ^ S n) == 0)%Q.
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H0 at 2. 
        rewrite <- INQ_Qeq_0.
        apply INQ_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply Nat.pow_gt_lin_r. omega.
      }
      apply Qlt_shift_div_l. 
      + rewrite <- INQ_Qeq_0. apply INQ_lt. 
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply Nat.pow_gt_lin_r. omega.
      + rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ INQ (10 ^ S n)) (INQ (10 ^ S n))).
        rewrite Qmult_inv_r ; auto.
        rewrite Qmult_1_r.
        apply INQ_lt. auto.
  Qed.

  Theorem f_le_sum_f_le : forall (f f1 : nat -> nat) , (forall n : nat , (f n <= f1 n)%nat) -> (forall n : nat , (sum_f f n <= sum_f f1 n)%Q).
  Proof.
    intros.
    induction n.
    - simpl. apply INQ_le. apply (H O).
    - rewrite (sum_f_expand f n). 
      rewrite (sum_f_expand f1 n).
      apply Qplus_le_compat; auto.
      unfold Qdiv. 
      assert (~ INQ(10 ^ S n) == 0)%Q.
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H0 at 2. 
        rewrite <- INQ_Qeq_0.
        apply INQ_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply Nat.pow_gt_lin_r. omega.
      }
      apply Qle_shift_div_l. 
      + rewrite <- INQ_Qeq_0. apply INQ_lt. 
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply Nat.pow_gt_lin_r. omega.
      + rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ INQ (10 ^ S n)) (INQ (10 ^ S n))).
        rewrite Qmult_inv_r ; auto.
        rewrite Qmult_1_r.
        apply INQ_le. auto.
  Qed.

  Theorem sum_f_up : forall f : nat -> nat , Indec f -> (forall n : nat , sum_f f (S n) <= sum_f f n + INQ(1) / INQ (10 ^ n))%Q.
  Proof.
    intros.
    rewrite sum_f_expand. rewrite Qplus_le_r.
    assert (INQ (10) / INQ(10 ^ (S n)) == INQ (1) / INQ (10 ^ n))%Q.
    {
      rewrite Nat.pow_succ_r'.
      rewrite <- INQ_mult.
      unfold Qdiv.
      rewrite Qinv_mult_distr.
      rewrite Qmult_assoc.
      rewrite Qmult_inv_r.
      rewrite INQ_Qeq_1. reflexivity.
      unfold not. intros. inversion H0.
    }
    rewrite <- H0.
    apply Qle_shift_div_l.
    - rewrite <- INQ_Qeq_0. apply INQ_lt. 
      apply lt_trans with (m := S n).
      destruct n ; omega.
      apply Nat.pow_gt_lin_r. omega.
    - unfold Qdiv. 
      assert (~ INQ(10 ^ S n) == 0)%Q.
      {
        unfold not.
        intros.
        apply (Qlt_irrefl 0).
        rewrite <- H1 at 2. 
        rewrite <- INQ_Qeq_0.
        apply INQ_lt.
        apply lt_trans with (m := S n).
        destruct n ; omega.
        apply Nat.pow_gt_lin_r. omega.
      }
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (/ INQ (10 ^ S n)) (INQ (10 ^ S n))).
      rewrite Qmult_inv_r ; auto.
      pose proof H (S n).
      rewrite Qmult_1_r.
      apply INQ_le.
      apply lt_le_weak ; auto.
      destruct H2; omega.
  Qed.
  
  Theorem Mono_up_sum_f : forall (f : nat -> nat)(n m : nat) , (n <= m)%nat -> (sum_f f n <= sum_f f m)%Q.
  Proof.
    intros.
    induction H.
    - lra.
    - apply Qle_trans with (sum_f f m) ; auto.
      simpl.
      rewrite <- Qplus_0_r at 1.
      apply Qplus_le_r.
      unfold Qdiv. apply Qmult_le_0_compat.
      + rewrite <- INQ_Qeq_0. apply INQ_le. omega.
      + apply Qinv_le_0_compat. rewrite <- INQ_Qeq_0. apply INQ_le. omega.
  Qed.

  Theorem sum_f_Dec_R_up : forall (f : nat -> nat) (n m : nat) , Indec f -> (n < m)%nat ->  Dec_R (IQR (sum_f f n)) m 0.
  Proof.
    intros.
    generalize dependent m.
    induction n.
    - intros.
      hnf. 
      exists ((f 0) * (10 ^ m))%nat. rewrite <- mult_IQR.
      repeat split .
      + apply IQR_le.
        simpl. rewrite INQ_mult. lra.
      + apply IQR_lt. simpl.
        rewrite INQ_mult. apply INQ_lt. omega.
      + assert (m = m - 1 + 1)%nat. { omega. }
        rewrite H1.
        rewrite Nat.pow_add_r.
        rewrite mult_assoc. 
        rewrite Nat.mod_mul ; auto.
    - intros. hnf. 
      assert (n < m)%nat. { omega. }
      specialize (IHn m H1).
      destruct IHn , H2 , H2.
      rewrite <- mult_IQR in *.
      apply le_IQR in H2. apply lt_IQR in H4.
      exists (x + (f (S n)) * (10 ^ (m - S n)))%nat. rewrite <- mult_IQR in *.
      repeat split .
      + apply IQR_le. rewrite sum_f_expand.
        rewrite Qmult_plus_distr_l. rewrite <- INQ_plus.
        apply Qle_Qplus_Qle ; auto.
        unfold Qdiv. rewrite <- Qmult_assoc. rewrite <- INQ_mult.
        destruct (H (S n)).
        * rewrite H5. rewrite INQ_Qeq_0. rewrite !Qmult_0_l. lra.
        * rewrite H5. rewrite INQ_Qeq_1. rewrite !Qmult_1_l. 
          assert (m = m - S n + S n)%nat. { omega. }
          rewrite H6 at 2.
          rewrite Nat.pow_add_r.
          rewrite <- INQ_mult.
          rewrite Qmult_comm at 1.
          rewrite <- Qmult_assoc.
          rewrite Qmult_inv_r.
          rewrite Qmult_1_r. lra.
          intro.
          rewrite <- INQ_Qeq_0 in H7. apply Qeq_INQ_eq in H7.
          apply (lt_irrefl O). rewrite <- H7 at 2.
          apply Max_powan_0. omega.
      + apply IQR_lt. rewrite sum_f_expand.
        rewrite Qmult_plus_distr_l. 
        assert (x + f (S n) * 10 ^ (m - S n) + 1 = x + 1 + f (S n) * 10 ^ (m - S n))%nat. { omega. }
        rewrite H5. clear H5. rewrite <- INQ_plus.
        apply Qlt_Qplus_Qle ; auto.
        unfold Qdiv. rewrite <- Qmult_assoc. rewrite <- INQ_mult.
        destruct (H (S n)).
        * rewrite H5. rewrite INQ_Qeq_0. rewrite !Qmult_0_l. lra.
        * rewrite H5. rewrite INQ_Qeq_1. rewrite !Qmult_1_l. 
          assert (m = m - S n + S n)%nat. { omega. }
          rewrite H6 at 1.
          rewrite Nat.pow_add_r.
          rewrite <- INQ_mult.
          rewrite Qmult_comm at 1.
          rewrite <- Qmult_assoc.
          rewrite Qmult_inv_r.
          rewrite Qmult_1_r. lra.
          intro.
          rewrite <- INQ_Qeq_0 in H7. apply Qeq_INQ_eq in H7.
          apply (lt_irrefl O). rewrite <- H7 at 2.
          apply Max_powan_0. omega. 
      + rewrite Nat.add_mod ; auto.
        rewrite <- H3. rewrite plus_0_l.
        rewrite Nat.mod_mod ; auto.
        assert (m - S n = m - S n - 1 + 1)%nat. { omega. }
        rewrite H5. rewrite Nat.pow_add_r.
        rewrite mult_assoc.
        rewrite Nat.mod_mul ; auto.
  Qed.
  
  Theorem sum_f_le_0 : forall (f : nat -> nat)(n : nat) , Indec f -> (0 <= IQR (sum_f f n)).
  Proof.
    intros.
    rewrite <- IQR_R0. apply IQR_le.
      apply Qle_trans with (sum_f f O).
      - rewrite <- INQ_Qeq_0. simpl. apply INQ_le. destruct (H O) ; omega.
      - assert (forall n : nat , sum_f f n >= sum_f f O)%Q.
        { intros. induction n0 ; try (lra).
          apply Qle_trans with (sum_f f n0) ; auto.
          apply Mono_up_sum_f. omega.
        }
        apply H0.
  Qed.
  
  Theorem sum_f_Same_Ipart : forall (f : nat -> nat) (n : nat) , Indec f -> (Same_Ipart (IQR(sum_f f (S n))) (IQR(sum_f f n))).
  Proof.
    intros.
    apply (Same_Ipart_mult _ _ (10 ^ n)).
    - apply Max_powan_0. omega.
    - destruct (archimedean_exists (IQR (sum_f f n) * IQR (10 ^ n)%nat)).
      apply Rle_ge. apply Rmult_le_pos. apply sum_f_le_0 ; auto.
      rewrite INQ_IQR_INR. auto with real.
      exists x. destruct H0.
      rewrite <- INQ_IQR_INR.
      repeat split ; auto.
      + apply Rle_trans with (IQR (sum_f f n) * IQR (10 ^ n)%nat) ; auto.
        rewrite INQ_IQR_INR.
        apply Rmult_le_compat_r. auto with real.
        apply IQR_le. apply Mono_up_sum_f. omega.
      + rewrite <- mult_IQR in *. apply IQR_lt. apply lt_IQR in H1. apply le_IQR in H0.
        rewrite sum_f_expand.
        destruct (H (S n)).
        * rewrite H2. rewrite INQ_Qeq_0. unfold Qdiv. rewrite Qmult_0_l.
          rewrite Qplus_0_r. auto.
        * rewrite H2. clear H2.
          rewrite Qmult_plus_distr_l.
          assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
          assert (INQ(1) / INQ(10^ S n) * INQ (10 ^ n) == INQ (1) / INQ(10) )%Q. 
          { 
            apply (Qmult_inj_r _ _ (INQ 10)).
            - intro. rewrite <- INQ_Qeq_0 in H3. apply Qeq_INQ_eq in H3. inversion H3.
            - rewrite <- Qmult_assoc. rewrite INQ_mult.  rewrite <- H2.
              field. split ; intro.
              + rewrite <- INQ_Qeq_0 in H3. apply Qeq_INQ_eq in H3. inversion H3.
              + apply (Qlt_irrefl 0%Q). rewrite <- H3 at 2.
                rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0 ; omega.
          }
          rewrite H3.
          pose proof (sum_f_Dec_R_up f n (S n)). 
          assert (S n > n)%nat. { omega. }
          specialize (H4 H H5). clear H5.
          hnf in H4. 
          destruct H4,H4,H4. rewrite <- mult_IQR in *.
          apply le_IQR in H4. apply lt_IQR in H6.
          symmetry in H5.
          apply mod_exists in H5 ; try (omega) .
          destruct H5.  rewrite plus_0_r in *.
          rewrite H2 in *. rewrite <- INQ_mult in *.
          rewrite Qmult_assoc in *.
          subst x0.
          rewrite mult_comm in *.
          rewrite <- INQ_plus in H6.
          rewrite <- INQ_mult in *.
          assert (INQ(10) > 0)%Q. { rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
          apply Qmult_lt_0_le_reg_r in H4 ; auto.
          assert (INQ(1) == INQ(1) / INQ(10) * INQ(10))%Q. { field. intro. rewrite H7 in H5. apply Qlt_irrefl in H5. auto. }
          rewrite H7 in H6.
          rewrite <- Qmult_plus_distr_l in H6.
          apply Qmult_lt_r in H6 ; auto.
          assert (sum_f f n * (10 ^ n)%nat < x1 + 1%nat)%Q.
          { apply Qlt_trans with (x1 + 1%nat / 10%nat)%Q ; auto.
            apply Qplus_lt_r. rewrite INQ_Qeq_1.
            unfold Qdiv. rewrite Qmult_1_l.
            apply Qlt_shift_inv_r ; auto.
          }
          assert (x = x1).
          {
            apply (Ipart_unique (IQR (sum_f f n * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
            rewrite <- INQ_plus. auto.
          }
          subst.
          apply Qlt_trans with (x1 + 1%nat / 10%nat + 1%nat / 10%nat)%Q.
          ** apply Qplus_lt_l. auto.
          ** rewrite <- INQ_plus. rewrite <- Qplus_assoc.
             apply Qplus_lt_r.
             unfold Qdiv. rewrite <- Qmult_plus_distr_l.
             rewrite INQ_plus. simpl. rewrite INQ_Qeq_1.
             apply Qmult_lt_r with (INQ (10)) ; auto.
  Qed.
  
  Theorem sum_f_Dec_R_same : forall (f : nat -> nat) (n m : nat) , Indec f -> (m <= n)%nat ->  Dec_R (IQR (sum_f f n)) m (f m).
  Proof.
    intros.
    generalize dependent m.
    induction n.
    - intros. inversion H0.
      subst. exists (f 0)%nat.
      repeat split.
      * rewrite <- mult_IQR. simpl. rewrite Zmult_1_r. apply Rle_refl.
      * rewrite <- mult_IQR. apply IQR_lt. simpl. rewrite INQ_Qeq_1. rewrite Qmult_1_r.
        apply INQ_lt. omega.
      * destruct (H O) ; rewrite H1 ; auto.
    - intros.
      inversion H0.
      * subst. assert (n < S n)%nat. { omega. } 
        pose proof sum_f_Dec_R_up f n (S n) H H1.
        clear H0 H1 IHn. 
        destruct H2 , H0 , H0.
        hnf. 
        exists (x + f (S n))%nat.
        rewrite <- mult_IQR in *. apply le_IQR in H0. apply lt_IQR in H2.
        repeat split.
        + apply IQR_le. rewrite sum_f_expand.
          rewrite Qmult_plus_distr_l.
          rewrite <- INQ_plus.
          apply Qle_Qplus_Qle ; auto.
          rewrite Qmult_comm.
          rewrite Qmult_div_r. lra.
          intro.
          apply (Qlt_irrefl 0).
          rewrite <- H3 at 2.
          rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
        + apply IQR_lt. rewrite sum_f_expand.
          rewrite Qmult_plus_distr_l.
          assert (x + f (S n) + 1 = x + 1 + f (S n))%nat. { omega. }
          rewrite H3. clear H3.
          rewrite <- INQ_plus.
          apply Qlt_Qplus_Qle ; auto.
          rewrite Qmult_comm.
          rewrite Qmult_div_r. lra.
          intro.
          apply (Qlt_irrefl 0).
          rewrite <- H3 at 2.
          rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. 
        + rewrite Nat.add_mod ; auto.
          rewrite <- H1. rewrite plus_0_l.
          destruct (H (S n)) ; rewrite H3 ; auto. 
      * subst. specialize (IHn _ H2).
        subst. assert (n < S n)%nat. { omega. } 
        pose proof sum_f_Dec_R_up f n (S n) H H1.
        clear H1.
        destruct IHn , H1 , H1.
        destruct H3 , H3 , H3.
        hnf.
        rewrite <- mult_IQR in *. apply le_IQR in H3. apply lt_IQR in H7.
        exists x.
        split ; auto.
        assert (Same_Ipart (IQR (sum_f f (S n) * (10 ^ m)%nat)) (IQR (sum_f f n * (10 ^ m)%nat))).
        { 
          apply  (Same_Ipart_mult _ _ (10 ^ (n - m))).
          - apply Max_powan_0 ; omega.
          - destruct (archimedean_exists (IQR ((sum_f f n) * INQ (10 ^ n)))).
            rewrite mult_IQR. apply Rle_ge. apply Rmult_le_pos.
            apply sum_f_le_0 ; auto. 
            rewrite INQ_IQR_INR. auto with real.
            destruct H8.
            exists x1.
            assert (((10 ^ m)%nat * (10 ^ (n - m))%nat) == (10 ^ n)%nat)%Q.
            { rewrite INQ_mult. apply eq_INQ_Qeq. 
              rewrite <- Nat.pow_add_r.
              assert (m + (n - m) = n)%nat. { omega. }
              subst. auto.
            }
            rewrite <- INQ_IQR_INR.
            repeat split ; repeat rewrite <- mult_IQR ; try (apply IQR_le) ; try (apply IQR_lt); auto ;
            apply le_IQR in H8 ; apply lt_IQR in H9 ;
            try (rewrite <- Qmult_assoc) ; try (rewrite H10); clear H10;
            try (rewrite sum_f_expand ; rewrite Qmult_plus_distr_l) ; auto.
            + apply Qle_trans with ((sum_f f n) * (INQ (10 ^ n)))%Q ; auto.
              rewrite <- Qplus_0_r at 1.
              apply Qplus_le_r.
              unfold Qdiv. 
              assert (INQ(10^n) >= 0)%Q.
              {  rewrite <- INQ_Qeq_0. apply INQ_le. apply lt_le_weak. apply Max_powan_0. omega. }
              apply Qmult_le_0_compat ; auto.
              apply Qmult_le_0_compat.
              * rewrite <- INQ_Qeq_0. apply INQ_le. destruct (H (S n)) ; omega.
              * apply Qinv_le_0_compat.
                rewrite <- INQ_Qeq_0. apply INQ_le. apply lt_le_weak. apply Max_powan_0. omega.
            + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
              assert (INQ(f (S n)) / INQ(10^S n) * INQ (10 ^ n) == INQ (f (S n)) / INQ(10) )%Q. 
              { 
                apply (Qmult_inj_r _ _ (INQ 10)).
                - intro. rewrite <- INQ_Qeq_0 in H11. apply Qeq_INQ_eq in H11. inversion H11.
                - rewrite <- Qmult_assoc. rewrite INQ_mult.  rewrite <- H10.
                  field. split ; intro.
                  + rewrite <- INQ_Qeq_0 in H11. apply Qeq_INQ_eq in H11. inversion H11.
                  + apply (Qlt_irrefl 0%Q). rewrite <- H11 at 2.
                    rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0 ; omega.
              }
              rewrite H11. 
              symmetry in H6.
              apply mod_exists in H6 ; try (omega) .
              destruct H6. rewrite plus_0_r in H6.
              rewrite H10 in *. rewrite <- INQ_mult in *.
              rewrite Qmult_assoc in *.
              subst x0.
              rewrite mult_comm in *.
              rewrite <- INQ_plus in H7.
              rewrite <- INQ_mult in *.
              assert (INQ(10) > 0)%Q. { rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
              apply Qmult_lt_0_le_reg_r in H3 ; auto.
              assert (INQ(1) == INQ(1) / INQ(10) * INQ(10))%Q. { field. intro. rewrite H12 in H6. apply Qlt_irrefl in H6. auto. }
              rewrite H12 in H7.
              rewrite <- Qmult_plus_distr_l in H7.
              apply Qmult_lt_r in H7 ; auto.
              assert ((sum_f f n) * (10 ^ n)%nat < x2 + 1%nat)%Q.
              { apply Qlt_trans with (x2 + 1%nat / 10%nat)%Q ; auto.
                apply Qplus_lt_r. rewrite INQ_Qeq_1.
                unfold Qdiv. rewrite Qmult_1_l.
                apply Qlt_shift_inv_r ; auto.
              }
              assert (x2 = x1).
              {
                apply (Ipart_unique (IQR ((sum_f f n) * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
                rewrite <- INQ_plus. auto.
              }
              subst.
              apply Qlt_trans with (x1 + 1%nat / 10%nat + f (S n) / 10%nat)%Q.
              * apply Qplus_lt_l. auto.
              * rewrite <- INQ_plus. rewrite <- Qplus_assoc.
                apply Qplus_lt_r.
                unfold Qdiv. rewrite <- Qmult_plus_distr_l.
                rewrite INQ_plus. simpl. rewrite INQ_Qeq_1.
                apply Qmult_lt_r with (INQ (10)) ; auto.
                destruct (H (S n)) ; rewrite H14 ; auto.
        }
        destruct H8 , H8 , H9 , H10.
        assert (x = x1)%nat. {apply (Ipart_unique (IQR ((sum_f f n) * (10 ^ m)%nat))) ; split ; auto. }
        subst.
        split; rewrite <- mult_IQR ; auto.
  Qed.
  
  Theorem sum_f_In_Search : forall (f : nat -> nat)(n : nat) , Indec f -> (sum_f f n < INQ 10)%Q.
  Proof.
    intros.
    pose proof sum_f_Same_Ipart f.
    assert ((f 0 = 0)%nat -> archimedean 0%nat (IQR (sum_f f O))).
    {
      split .
      - apply IQR_le. apply INQ_le. omega.
      - apply IQR_lt. apply INQ_lt. omega.
    }
    assert ((f 0 = 0)%nat -> forall n : nat , archimedean 0%nat (IQR (sum_f f n))).
    {
      intros.
      induction n0 ; auto.
      destruct (H0 n0 H).
      destruct H3 , H4 , H5. destruct IHn0.
      assert (x = 0)%nat.
      { apply (Ipart_unique (IQR (sum_f f n0))) ; split; auto. }
      subst. split; auto.
    }
    assert ((f 0 = 1)%nat -> archimedean 1%nat (IQR (sum_f f O))).
    {
      split .
      - apply IQR_le. apply INQ_le. omega.
      - apply IQR_lt. apply INQ_lt. omega.
    }
    assert ((f 0 = 1)%nat -> forall n : nat , archimedean 1%nat (IQR (sum_f f n))).
    {
      intros.
      induction n0 ; auto.
      destruct (H0 n0 H).
      destruct H5 , H6 , H7. destruct IHn0.
      assert (x = 1)%nat.
      { apply (Ipart_unique (IQR (sum_f f n0))) ; split ;auto. }
      subst. split; auto.
    }
    destruct (H O).
    - specialize (H1 H5). specialize (H2 H5).
      apply Qlt_trans with (INQ (1%nat)).
      + destruct (H2 n). simpl in H7. apply lt_IQR. auto.
      + apply INQ_lt. omega.
    - specialize (H3 H5). specialize (H4 H5).
      apply Qlt_trans with (INQ(2%nat)).
      + destruct (H4 n). simpl in H7. apply lt_IQR. auto.
      + apply INQ_lt. omega.
  Qed.
  
  Theorem In_search_sum_f : forall (f :nat -> nat)(n :nat) , Indec f -> In_Search (IQR (sum_f f n)).
  Proof.
    intros.
    split.
    * rewrite <- IQR_R0. apply Rle_ge. apply IQR_le.
      apply Qle_trans with (sum_f f O).
      - rewrite <- INQ_Qeq_0. simpl. apply INQ_le. destruct (H O) ; omega.
      - assert (forall n : nat , sum_f f n >= sum_f f O)%Q.
        { intros. induction n0 ; try (lra).
          apply Qle_trans with (sum_f f n0) ; auto.
          apply Mono_up_sum_f. omega.
        }
        apply H0.
    * apply IQR_lt. apply sum_f_In_Search. auto.
  Qed.
  
  Theorem InDecR_sum_f : forall ( f: nat -> nat) (n : nat) , Indec f -> InDecR (IQR (sum_f f n)).
  Proof.
    intros.
    hnf. intros m.
    destruct (classic (n < m)%nat).
    - left. apply sum_f_Dec_R_up ; auto.
    - assert (m <= n)%nat. {omega. }
      destruct (H m).
      + left. rewrite <- H2. apply sum_f_Dec_R_same ; auto.
      + right. rewrite <- H2. apply sum_f_Dec_R_same ; auto.  
  Qed.
  
  Theorem sum_f_NQ_eqb : forall (f : nat -> nat) , Indec f -> forall n : nat , NNP_T_NQP (NN_T_NNP f) n ((sum_f f) n).
  Proof.
    intros.
    induction n.
    - repeat split; intros ; hnf in * .
      + destruct H1 , H1 , H1. inversion H0. subst.
        assert (IQR (10 ^ 0)%nat == 1). { auto with real. }
        rewrite H2 in *. clear H2.
        rewrite Rmult_1_r in *.
        apply lt_IQR in H3. apply INQ_lt in H3.
        apply le_IQR in H1. apply INQ_le in H1.
        assert (f 0 = x)%nat. { omega. }
        subst. 
        destruct (H O) ; rewrite H2 ; auto.
      + inversion H0. subst.
        exists (f 0%nat).
        split.
        * assert (IQR (10 ^ 0)%nat == 1). { auto with real.  }
          rewrite H1. clear H1.
          split ; rewrite Rmult_1_r.
          ** apply Rle_refl.
          ** apply IQR_lt. apply INQ_lt. omega.
        * destruct (H O) ; rewrite H1 ; auto.
      + exists ( (f 0) * (10 ^ m))%nat.
        split.
        * split ; rewrite <- mult_IQR.
          ** apply IQR_le. simpl. rewrite INQ_mult. apply Qle_refl.
          ** apply IQR_lt. simpl. rewrite INQ_mult. apply INQ_lt. omega.
        * destruct (H O) ; rewrite H1 ; auto.
          rewrite mult_1_l.
          assert (m = m - 1 + 1)%nat. { omega. }
          rewrite H2. 
          rewrite Nat.pow_add_r.
          rewrite Nat.mul_mod ; auto.
          assert (10 ^ 1 mod 10 = 0)%nat. { auto. }
          rewrite H3. rewrite mult_0_r. auto.
      + destruct (H O).
        * right. simpl. rewrite H0. apply IQR_R0. 
        * left. rewrite <- IQR_R0. apply IQR_lt. simpl. rewrite H0. rewrite INQ_Qeq_1. lra.
      + destruct (H O) ; apply IQR_lt ; apply INQ_lt ; omega. 
    - destruct IHn. repeat split ; intros ; auto.
      + inversion H2.
        * subst ; hnf.
          apply (partial_functional_Dec_R (IQR (sum_f f (S n))) (S n)) ; auto.
          apply sum_f_Dec_R_same ; auto. 
        * apply H0 ; auto. 
          assert (l = f m)%nat. 
          { 
            apply (partial_functional_Dec_R (IQR (sum_f f (S n))) m) ; auto.
            apply sum_f_Dec_R_same ;  auto. 
          }
          subst. apply sum_f_Dec_R_same ; auto.
      + hnf in H3. subst.
        apply sum_f_Dec_R_same ; auto.
      + apply sum_f_Dec_R_up ;  auto.
      + apply Rle_ge.
        apply Rle_trans with (IQR (sum_f f n)).
        destruct H1. auto with real.
        apply IQR_le. apply Mono_up_sum_f. auto.
      + apply IQR_lt. apply (sum_f_In_Search f (S n)). auto. 
  Qed.
  
  Theorem limit_r_Un_cv'_eqb : forall (f : nat -> nat) (r : R) , Indec f -> limit (sum_f f) r <-> (Un_cv' (NNP_T_NQP (NN_T_NNP f)) r).
  Proof.
    intros.
    pose proof InDec_eqb f.
    destruct H0. specialize (H0 H). clear H1.
    split ; intros ; hnf ; simpl in *.
    - split ; intros.
      + repeat split ; hnf ; intros ; subst ; try (rewrite H3 in *; apply H4 ; auto) ;
        try (rewrite <- H3 in *; apply H4 ; auto).
        * exists (sum_f f a). apply sum_f_NQ_eqb. auto.
        * apply (partial_functional_NNP_T_NQP (NN_T_NNP f) H0 a) ; auto.
      + destruct H1. 
        specialize (H3 eps H2).
        destruct H3.
        exists x.
        intros.
        assert (q == sum_f f m)%Q.
        { apply (partial_functional_NNP_T_NQP (NN_T_NNP f) H0 m) ; auto.
          apply sum_f_NQ_eqb ; auto.
        }
        apply (H3 _ _ H4 H6). 
   - split ; intros.
     + repeat split ; hnf ; intros ; subst ; try (lra).
       exists (sum_f f a). reflexivity.
     + destruct H1.
       specialize (H3 eps H2).
       destruct H3.
       exists x. intros.
       apply (H3 m) ; auto.
       pose proof sum_f_NQ_eqb _ H m. rewrite H5. auto. 
  Qed.
  
  Theorem sum_f_limit_r : forall (f : nat -> nat) (r : R) , Indec f -> 
      limit (sum_f f) r <-> (forall n : nat , Dec_R r n (f n)) /\ In_Search r.
  Proof.
    intros.
    split ; intros.
    - apply limit_r_Un_cv'_eqb in H0 ; auto.
      split ; intros.
      * apply (Un_cv'_Dec (NN_T_NNP f)) ; auto.
        + apply InDec_eqb. auto.
        + reflexivity.
      * assert (Sup_Q (NNP_T_NQP (NN_T_NNP f)) r).
        { apply mono_up_limit_sup_Q ; auto.
          - hnf. split ; hnf; intros.
            + repeat split ; hnf ; intros ; subst ; try (rewrite <- H2 in * ; apply H3 ; auto).
              * exists (sum_f f a).
                split ; auto.
                apply sum_f_NQ_eqb. auto. apply In_search_sum_f ; auto.
              * apply InDec_eqb in H.
                apply (partial_functional_NNP_T_NQP (NN_T_NNP f) H a) ; auto.
            + split. apply is_function_NQP_T_NRP. apply is_function_NNP_T_NQP. apply InDec_eqb. auto. 
              intros.
              destruct H1 , H1. destruct H2 , H2.
              subst. 
              inversion H3.
              * right. rewrite <- H1 , <- H2. apply IQR_eq. subst. apply InDec_eqb in H.
                apply (partial_functional_NNP_T_NQP (NN_T_NNP f) H n) ; auto.
              * subst.
                destruct H4, H5.
                destruct (classic (forall n , (n > n1)/\(n <= S m) -> f n = 0)%nat).
                ** right. apply Dec_R_eq ; intros. 
                   rewrite <- H1 ; auto. rewrite <- H2 ; auto.
                   rewrite <- H1 , <- H2 . clear H1 H2.
                   specialize (H4 j). specialize (H5 j).
                   destruct H4 , H5.
                   destruct (classic (j <= n1)%nat).
                   ++ assert (j <= S m)%nat. { omega. } 
                      specialize (H1 H11). specialize (H4 H10).
                      rewrite H1. rewrite H4. reflexivity.
                   ++ apply Nat.nle_gt in H10.
                      specialize (H5 H10). 
                      destruct (classic (j <= S m)%nat).
                      -- specialize (H1 H11). 
                         rewrite H1.
                         split ; intros.
                         *** assert (m0 = 0)%nat. { destruct H12. auto. }
                             subst. auto.
                         *** assert (m0 = 0)%nat. { apply (partial_functional_Dec_R (IQR x0) j) ; auto. }
                             subst. hnf. apply H9. omega.
                      -- apply Nat.nle_gt in H11.
                         specialize (H2 H11).
                         split ; intros.
                         *** assert (m0 = 0)%nat. { apply (partial_functional_Dec_R (IQR x) j) ; auto. }
                             subst. auto.
                         *** assert (m0 = 0)%nat. { apply (partial_functional_Dec_R (IQR x0) j) ; auto. }
                             subst. auto.
                ** apply not_all_ex_not in H9. destruct H9.
                   pose proof H9.
                   apply not_imply_elim in H9.
                   apply not_imply_elim2 in H10.
                   rewrite <- H1 , <- H2. clear H1 H2.
                   left. pose proof (H4 x1). pose proof (H5 x1).
                   destruct H9 , H1 , H2.
                   specialize (H13 H9). specialize (H1 H11).
                   assert (f x1 = 1)%nat. {destruct (H x1) ; auto. exfalso. auto. }
                   apply Dec_R_lt ; auto.
                   exists x1. split ; intros.
                   ++ assert (m1 = 0)%nat. {apply (partial_functional_Dec_R (IQR x0) x1) ; auto. }
                      assert (Dec_R (IQR x) x1 1). { apply H1 ; hnf ;  auto. }
                      assert (m2 = 1)%nat. {apply (partial_functional_Dec_R (IQR x) x1) ; auto. }
                      subst. auto.
                   ++ clear H10 H8. 
                      assert (k <= S m)%nat. { omega. } 
                      specialize (H4 k). specialize (H5 k). 
                      destruct H4 , H5. specialize (H4 H8). rewrite H4 in H17.
                      hnf in H17.
                      destruct (classic (k <= n1)%nat).
                      --  specialize (H5 H19). rewrite H5 in H16. hnf in H16.
                          subst. auto.
                      --  apply Nat.nle_gt in H19. specialize (H18 H19).
                          assert (m1 = 0)%nat. {apply (partial_functional_Dec_R (IQR x0) k) ; auto. }
                          subst. omega.
          - exists 2. apply Dec_R2_bound. apply InDec_eqb. auto.
        }
        assert (upper_bound_Q (NNP_T_NQP (NN_T_NNP f)) 2). { apply Dec_R2_bound. apply InDec_eqb. auto. }
        destruct H1.
        hnf in H3.
        split .
        + apply Rle_ge.
          apply Rle_trans with (IQR (INQ (f 0)%nat)).
          ** rewrite <- IQR_R0. apply IQR_le.
             rewrite <- INQ_Qeq_0. apply INQ_le. destruct (H O) ; omega.
          ** apply (H3 O).
             hnf. exists (INQ (f 0%nat)).
             split; auto with real.
             hnf. split ; intros.
             ++ split ; intros.
                -- inversion H4. subst.
                   pose proof (sum_f_Dec_R_same f O O H H4).
                   simpl in H5.
                   split ; intros.
                   assert (l = f 0%nat). {apply (partial_functional_Dec_R (IQR (f 0%nat)) 0) ; auto. }
                   hnf . auto.
                   hnf in H6. subst. auto.
                -- apply (sum_f_Dec_R_up f O m) ; auto.
             ++ apply (In_search_sum_f f O). auto.
        + apply Rle_lt_trans with 2.
          ** apply Rge_le. apply H1. auto.
          ** apply R2_Rlt_R10.
    - hnf. split ; intros.
      + repeat split ; hnf ; intros ; subst ; try (rewrite H2 in * ; auto).
        * exists (sum_f f a). reflexivity.
      + apply eps_gt_10n in H1.
        destruct H1.
        exists x.
        intros.
        subst. apply IQR_eq in H3. rewrite H3. 
        rewrite <- !INQ_IQR_INR in *.
        assert (IQR 1%nat = IQR 1). { auto. } rewrite H4 in *. clear H4. 
        apply Rlt_trans with (IQR 1 * / IQR (10 ^ x)%nat) ; auto.
        apply Dec_R_eq_lemma ; auto.
        * apply In_search_sum_f. auto.
        * apply H0.
        * intros. split ; intros.
          ** assert (f j = m0)%nat. { apply (partial_functional_Dec_R (IQR (sum_f f m)) j) ; auto.
                                      apply sum_f_Dec_R_same ; auto. omega. }
             subst. apply H0.
          ** assert (f j = m0)%nat. { apply (partial_functional_Dec_R r j) ; auto. apply H0. }
             subst. apply sum_f_Dec_R_same ; auto. omega. 
  Qed.
  
  Theorem sum_f_limit_eps : forall (f : nat -> nat)(n m : nat) , Indec f -> (n <= m) % nat -> (Qabs(sum_f f n - sum_f f m) < 1 / INQ (10^n))%Q.
  Proof.
    intros.
    apply Qabs_diff_Qlt_condition.
    assert (Rabs(IQR (sum_f f n) - IQR (sum_f f m)) < IQR 1 / IQR ((10^n)%nat)).
    { apply Dec_R_eq_lemma ; try (apply In_search_sum_f ; auto).
      intros.
      split ; intros.
      * assert (f j = m0)%nat. { apply (partial_functional_Dec_R (IQR (sum_f f n)) j) ; auto.
                                 apply sum_f_Dec_R_same ; auto. }
        subst. apply sum_f_Dec_R_same ; auto. omega.
      * assert (f j = m0)%nat. { apply (partial_functional_Dec_R (IQR (sum_f f m)) j) ; auto.
                                 apply sum_f_Dec_R_same ; auto. omega. }
        subst. apply sum_f_Dec_R_same ; auto.
    }
    apply Rabs_tri in H1.
    destruct H1.
    assert (IQR 1 / IQR (10 ^ n)%nat == IQR (1 / (10^n)%nat)).
    {
      unfold Rdiv.
      rewrite IQR_inv.
      - rewrite <- mult_IQR. reflexivity.
      - intro. apply (Qlt_irrefl 0).
        rewrite <- H3 at 2.
        rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
    }
    split; apply lt_IQR.
    - apply Rlt_le_trans with (IQR (sum_f f m) + IQR 1 / IQR (10 ^ n)%nat) ; auto.
      rewrite plus_IQR.
      apply Rplus_le_compat_l.
      rewrite <- H3. apply Rle_refl.
   - apply Rle_lt_trans with (IQR (sum_f f m) - IQR 1 / IQR (10 ^ n)%nat) ; auto.
     apply Rle_Rminus.
     unfold Qminus. rewrite plus_IQR.
     rewrite <- (Rplus_0_r (IQR (sum_f f m))) at 2.
     rewrite Rplus_assoc. 
     apply Rplus_le_compat_l.
     rewrite H3.
     rewrite <- plus_IQR. rewrite <- IQR_R0.
     apply IQR_le. lra.
  Qed.
  
  
  Theorem P_OR_NP : (forall P : Prop, {P} + {~ P}) -> Halting.
  Proof. 
    unfold Halting.
    intros.
    pose proof X (exists j : nat , TM i j = true).
    destruct H ; auto.
    right.
    intros.
    destruct (TM i j) eqn : En ; auto.
    exfalso. apply n. exists j. auto.
  Qed.

  Theorem Two_dimensions : (forall r1 r2 : R, {r1 == r2} + {~ r1 == r2}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof TMR_get i.
    remember (Get_TMR i) as X0.
    pose proof X X0 R0.
    clear HeqX0 X. destruct H.
    destruct H0. 
    - rewrite Dec_R_eq in r ; auto.
      + right. intros.
        pose proof Zero_Dec j.
        rewrite <- r in H0. 
        specialize (H j).
        assert (0 = Nat.b2n (TM i j))%nat. { apply (partial_functional_Dec_R X0 j) ; auto. }
        apply Nat.b2n_inj. auto.
      + apply In_Search_R0.
    - apply Dec_R_not_eq in n ; auto.
      + left. destruct n.
        exists x.
        pose proof Zero_Dec x.
        specialize (H x).
        assert (Nat.b2n (TM i x) <> 0)%nat.
        { intro. apply (H0 O) ; auto.
          rewrite H3 in H. auto.
        }
        destruct (TM i x) ; auto.
      + apply In_Search_R0.
  Qed.

  Theorem Three_dimensions : (forall r1 r2 : R, {r1 == r2} + {r1 > r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Two_dimensions.
    intros.
    pose proof (X r1 r2).
    clear X.
    destruct H ; auto with real.
    destruct s ; auto with real.
  Qed.
  
  Theorem Two_dimensions2 : (forall r1 r2 : R, {r1 >= r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Three_dimensions.
    intros.
    pose proof (X r1 r2).
    destruct H ; auto.
    pose proof (X r2 r1).
    destruct H ; auto.
    left. left. auto with real.
  Qed.
  
  Theorem Exam_dimensions2 : (forall r : R , {r == R0} + {~ r == R0}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    apply Two_dimensions.
    intros.
    pose proof X (r1 - r2).
    destruct H.
    - left. auto with real.
    - right. auto with real.
  Qed.
  
  Definition CR (r : R) : Prop := 
      exists f : nat -> nat, Indec f /\  (forall (n: nat), Dec_R r n (f n)).
  Definition CR1 (r : R) := {f : nat -> nat | Indec f /\  (forall (n: nat), Dec_R r n (f n)) }.
  (** exists a sequence of rational number limits to r *)
  Definition CR2 (r : R) := exists f : nat -> Q, limit f r.
  (** exists a Cauthy sequence of rational number limits to r *)
  Definition CR3 (r : R) :=
      {f : nat -> Q & {N : Q -> nat | limit f r 
      /\ (forall eps : Q , (eps > 0)%Q -> forall (n m : nat) , (n >= N eps)%nat /\ (n >= 1) %nat -> (m >= n)%nat -> (Qabs(f n - f m) < eps)%Q)
      /\ (forall n , (f n >= 0)%Q) } }.
       
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
  
  Theorem CR_CR2 : forall r : R , In_Search r -> CR r -> CR2 r.
  Proof.
    unfold CR.
    unfold CR2.
    intros.
    destruct H0 , H0.
    exists (sum_f x).
    rewrite sum_f_limit_r ; auto.
  Qed.

  Theorem CR1_CR3 : forall r : R , In_Search r -> CR1 r -> CR3 r.
  Proof.
    unfold CR1.
    unfold CR3.
    intros.
    destruct H0 , a.
    exists (sum_f x).
    exists (fun eps => eps_arrow_nat eps).
    split.
    - rewrite sum_f_limit_r ; auto.
    - split ; intros ; try (apply le_IQR ; rewrite IQR_R0 ; apply Rge_le ;
        apply In_search_sum_f ; auto).
      destruct H3.
      pose proof eps_arrow_correct eps.
      remember (eps_arrow_nat eps) as n0.
      apply Qlt_trans with (y := (1 / INQ(n0))%Q).
      + apply Qlt_trans with (y := (1 / INQ(10^n))%Q).
        * apply sum_f_limit_eps ; auto.
        * apply Qlt_shift_div_l.
          ** rewrite Heqn0. apply eps_arrow_pro ; auto.
          ** rewrite Qmult_comm.
             assert (1 / INQ (10 ^ n) == / INQ (10 ^ n))%Q.
             {
               field.
               unfold not.
               intros.
               apply (Qlt_irrefl 0). 
               rewrite <- H7 at 2.
               rewrite <- INQ_Qeq_0. apply INQ_lt.
               apply Max_powan_0. omega.
             }
             rewrite H7.
             clear H7.
             apply Qlt_shift_div_r.
             rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
             rewrite Qmult_1_l.
             apply INQ_lt.
             apply le_lt_trans with (m := n) ; auto.
             apply Nat.pow_gt_lin_r . omega.
      + apply Qlt_shift_div_r.
        * rewrite Heqn0. apply eps_arrow_pro ; auto.
        * rewrite Qmult_comm.
        assert (1 == 1 / eps * eps)%Q.
        { field. unfold not. intros.
          rewrite H7 in H2. apply (Qlt_irrefl 0). auto.
        }
        rewrite H7 at 1.
        apply Qmult_lt_compat_r ; auto.
  Qed.

  Theorem TM'r_is_computable1 : forall n : nat , CR1 (TM'r n).
  Proof.
    intros.
    unfold CR1.
    exists (fun n0 => Nat.b2n (TM n0 n)).
    intros.
    split.
    - hnf. intros.
      destruct (TM x n) ; auto.
    - apply TM'r_pro.
  Qed.
  
  Theorem TM'r_is_computable : forall n : nat , CR (TM'r n).
  Proof.
    intros.
    apply CR1_CR. apply TM'r_is_computable1.
  Qed.
  
  Theorem TM'r_is_computable3 : forall n : nat , CR3 (TM'r n).
  Proof.
    intros.
    apply CR1_CR3.
    apply In_Search_TM'r.
    apply TM'r_is_computable1.
  Qed.

  Theorem TM'r_is_computable2 : forall n : nat , CR2 (TM'r n).
  Proof.
    intros.
    apply CR3_CR2. apply TM'r_is_computable3.
  Qed.

  Theorem lim_CN_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> CR l1) -> Halting_easy'.
  Proof. 
    intros.
    pose proof H TM'r limitTM'r limit_of_TM'r TM'r_is_computable.
    clear H.
    unfold CR in *.
    unfold Halting_easy'.
    inversion H0.
    intros. destruct H.
    pose proof H1 i.
    clear H1.
    destruct (limitTM'r_pro0 i).
    - rewrite (limitTM'r_pro' i) in H1.
      assert (H' : {exists j : nat, TM i j = true} + {forall j : nat, TM i j = false}) by auto.
      exists H'. auto.
    - rewrite (limitTM'r_pro i) in H1.
      assert (H' : {exists j : nat, TM i j = true} + {forall j : nat, TM i j = false}) by auto.
      exists H'. auto.
  Qed.
  
  Theorem lim_CN_NCN' : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> CR l1) -> Halting_easy.
  Proof. 
    intros.
    pose proof H TM'r limitTM'r limit_of_TM'r TM'r_is_computable.
    clear H.
    unfold CR in *.
    unfold Halting_easy.
    destruct H0 as [f ?].
    unfold Halting.
    refine (@ex_intro _ _ _ I).
    intros. destruct H.
    pose proof H0 i.
    clear H0.
    destruct (f i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct (limitTM'r_pro0 i).
      + assert (0 = S (S n))%nat. { apply (partial_functional_Dec_R limitTM'r i) ; auto. }
        inversion H2.
      + assert (1 = S (S n))%nat. { apply (partial_functional_Dec_R limitTM'r i) ; auto. }
        inversion H2.
  Qed.
  
  Theorem lim_CN1_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR1 (Un n)) -> CR1 l1) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof X TM'r limitTM'r limit_of_TM'r TM'r_is_computable1.
    clear X.
    unfold CR1 in *.
    destruct H as [f ]. destruct a.
    specialize (H0 i).
    destruct (f i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct (limitTM'r_pro0 i).
      + assert (0 = S (S n))%nat. { apply (partial_functional_Dec_R limitTM'r i) ; auto. }
        inversion H2.
      + assert (1 = S (S n))%nat. { apply (partial_functional_Dec_R limitTM'r i) ; auto. }
        inversion H2.
  Qed.
  
  Theorem lim_CN3_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR3 (Un n)) -> CR3 l1) -> Halting.
  Proof.
    intros.
    apply limitTM'r_pro1.
    intros.
    pose proof X TM'r limitTM'r limit_of_TM'r TM'r_is_computable3.
    clear X.
    unfold CR3 in *.
    destruct H as [f [N [? ?]]].
    set (INQ 1 / INQ (10 ^ (S (S n))))%Q.
    assert (H' : (0 < q)%Q).
    {
      subst q.
      rewrite INQ_Qeq_1. unfold Qdiv. rewrite Qmult_1_l.
      apply Qinv_lt_0_compat.
      rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
    }
    remember (q / INQ 2)%Q as eps0.
    assert (H'' : (0 < eps0 )%Q).
    {
      subst.
      apply Qlt_shift_div_l.
      - rewrite <- INQ_Qeq_0. apply INQ_lt. omega.
      - rewrite Qmult_0_l. auto.
    }
    destruct H0. 
    pose proof H0 _ H''.
    remember (N eps0) as n1.
    remember (max (S n1) n) as n0. 
    clear H0.
    assert (H''' : (n0 >= n1 /\ n0 >= 1)%nat).
    {
      assert (max (S n1) n >= S n1)%nat. { apply Nat.le_max_l. }
      split ; rewrite Heqn0 ; omega.
    }
    assert (Rabs (IQR (f n0) - limitTM'r) < IQR q).
    {
      destruct H.
      assert (IQR eps0 > R0).
      { rewrite <- IQR_R0. apply IQR_lt. auto. }
      specialize (H0 _ H3).
      destruct H0.
      assert (max n0 x >= x)%nat. { apply Nat.le_max_r. }
      assert (max n0 x >= n0)%nat. { apply Nat.le_max_l. } 
      remember (max n0 x) as x0.
      assert (f x0 == f x0)%Q. { lra. }
      specialize (H0 _ _ H4 H6).
      specialize (H2 _ _ H''' H5).
      clear H''' H5 H6 H4.
      apply Rabs_tri in H0.
      destruct H0.
      apply Qabs_diff_Qlt_condition in H2.
      destruct H2.
      assert (q == eps0 + eps0)%Q.
      { subst. unfold Qdiv. rewrite <- Qmult_plus_distr_r. 
        assert (/ INQ 2 + / INQ 2 == (2 # 1) * / INQ 2)%Q. 
        { field. intro. rewrite <- INQ_Qeq_0 in H6. apply Qeq_INQ_eq in H6. omega. }
        assert (INQ 2 > 0)%Q. { rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
        rewrite H6.
        simpl. rewrite <- Qmult_1_r at 1.
        apply Qmult_inj_l.
        lra. rewrite <- (Qmult_inv_r (INQ 2)) ; try (lra).
        apply Qinv_lt_0_compat in H7.
        apply Qmult_inj_r ; try (lra).
        assert (INQ (2) == INQ (1) + INQ(1))%Q.
        { rewrite INQ_plus. simpl. reflexivity. }
        rewrite H8. rewrite INQ_Qeq_1. reflexivity.
      }
      assert (IQR q == IQR eps0 + IQR eps0).
      {
        apply NNPP. intro.
        apply Rdichotomy in H7.
        destruct H7 ; rewrite <- plus_IQR in H7 ; apply lt_IQR in H7 ; lra.
      }
      rewrite H7.
      clear H7 H6.
      apply Rabs_tri.
      apply IQR_lt in H2.
      apply IQR_lt in H5.
      rewrite plus_IQR in *.
      rewrite minus_IQR in *.
      split.
      - rewrite <- Rplus_assoc.
        apply Rlt_trans with (IQR (f x0) + IQR eps0) ; auto.
        apply Rplus_lt_compat_r ; auto.
      - apply Rlt_Rminus_Rplus. apply Rlt_Rminus_Rplus in H5.
        apply Rlt_Rminus_Rplus in H4.
        apply Rlt_trans with (IQR eps0 + IQR (f x0)) ; auto.
        rewrite Rplus_assoc.
        apply Rplus_lt_compat_l ; auto. 
    }
    subst q.
    assert (IQR (1%nat / (10 ^ (S (S n)))%nat) == IQR 1 / IQR (10 ^ (S (S n)))%nat).
    { unfold Rdiv. unfold Qdiv.
      rewrite mult_IQR. rewrite INQ_IQR_INR. rewrite IQR_R1. rewrite INR_R1. 
      rewrite IQR_inv. auto. reflexivity.
      intro.
      apply (Qlt_irrefl 0%Q).
      rewrite <- H3 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. 
    }
    rewrite H3 in H0.
    clear H3.
    assert (forall n : nat , ~ ((10 ^ n)%nat == 0)%Q).
    { intros. intro.
      apply (Qlt_irrefl 0%Q).
      rewrite <- H3 at 2.
      rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
    }
    assert (forall n : nat , (10 ^ n)%nat > 0)%Q.
    { intros. 
      rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
    }
    assert (Rabs (IQR (f n0) - limitTM'r) < IQR 1 / IQR (10 ^ S n)%nat).
    { apply Rlt_trans with (IQR 1 / IQR (10 ^ S (S n))%nat) ; auto.
      rewrite IQR_R1. unfold Rdiv. rewrite !Rmult_1_l.
      rewrite !IQR_inv ; auto.
      apply IQR_lt. apply Qlt_shift_inv_r ; auto.
      rewrite Qmult_comm.
      assert ((10 ^ (S (S n)))%nat == 10%nat * (10 ^ S n)%nat)%Q.
      { rewrite Nat.pow_succ_r'. rewrite INQ_mult. ring. }
      rewrite H5.
      rewrite <- Qmult_assoc. rewrite Qmult_inv_r ; auto.
      rewrite Qmult_1_r. rewrite <- INQ_Qeq_1. apply INQ_lt. omega.
    }
    pose proof Dec_R_eps_same _ _ (S n) H5.
    assert (Same_Ipart_n limitTM'r (S n - 1)). 
    { 
      assert (IQR 1%nat / IQR (10 ^ (S (S n - 1)))%nat == IQR (1%nat / (10 ^ (S (S n - 1)))%nat)).
      { unfold Rdiv. rewrite INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_l.
        rewrite IQR_inv.
        apply IQR_eq.
        unfold Qdiv. rewrite INQ_eq_1. rewrite Qmult_1_l. reflexivity.
        intro. rewrite <- INQ_Qeq_0 in H7. 
        apply Qeq_INQ_eq in H7. apply lt_irrefl with O.
        rewrite <- H7 at 2. apply Max_powan_0. omega.
      }
      pose proof Same_Ipart_pow10n limitTM'r (S n - 1).
      assert (In_Search limitTM'r). { apply InSearch_limitTM'r. }
      assert (InDecR_n limitTM'r (S (S n - 1))). { apply InDecR_all_n. apply limitTM'r_pro0. }
      specialize (H8 H9 H10). clear H9 H10. 
      hnf in *.
      destruct H8. exists x. rewrite <- H7 in *.
      rewrite <- !INQ_IQR_INR in *. auto with real. 
    }
    destruct (Dec_Q_nine (f n0) (S n)).
    - rewrite <- IQR_R0. apply IQR_le. auto.
    - apply (Dec_Q_Dec_R_same _ (f n0)) ; auto.
      apply InSearch_limitTM'r.
      apply limitTM'r_pro0. 
    - destruct (Dec_Q (f n0) n).
      + rewrite <- IQR_R0. apply IQR_le. auto. 
      + rewrite H6 in d ; auto.
        apply Dec_R_nine_same.
        rewrite <- IQR_R0. apply Rle_ge. apply IQR_le. auto.
        assert (S (S n - 1) = S n)%nat. { omega. }
        rewrite H8. auto.
      + rewrite H6 in n3 ; auto.
        right. destruct (limitTM'r_pro0 n) ; auto.
        exfalso. auto.
        apply Dec_R_nine_same. 
        rewrite <- IQR_R0. apply Rle_ge. apply IQR_le. auto.
        assert (S (S n - 1) = S n)%nat. { omega. }
        rewrite H8. auto.
  Qed.
  
End CR_uu.
