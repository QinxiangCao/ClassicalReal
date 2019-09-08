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
From CReal Require Import Uncomputable.Countable.
From CReal Require Import INQ_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import ComRealBase.
From CReal Require Import ComRealField.
From CReal Require Import ComRealBaseLemma1.
From CReal Require Import ComRealLemmas.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.

Module DEC_R (R : VIR_R).
  Module RLemmas := VirRLemmas (R).
  Include VIR_R_EXTRA R.
  Export RLemmas.
  Import R.
  Local Open Scope R_scope. 

  Definition In_Search : R -> Prop.
    intros.
    apply ( X >= R0 /\ X < IQR( INQ 10)).
  Defined.

  Instance In_Search_comp : Proper (Req ==> iff) In_Search.
  Proof.
    hnf ; intros.
    split ; intros ; hnf in *; rewrite H in * ; auto.
  Qed.
  
  Theorem R2_Rlt_R10 : 2 < IQR ( INQ 10).
  Proof.
    rewrite INQ_IQR_INR. assert (2 = INR 2). { auto.  }
    rewrite H. apply lt_INR. omega.
  Qed.
  
  Theorem In_Search_R0 : In_Search R0.
  Proof.
    split.
    - apply Rle_refl.
    - rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. omega.
  Qed.
  
  Instance archimedean_comp : Proper (eq ==> Req ==> iff) archimedean.
  Proof.
    hnf ; red ; intros.
    subst.
    split ; intros ; hnf in * ; rewrite H0 in * ; auto.
  Qed.
  
  Definition Dec_R : R -> nat -> nat -> Prop .
    intros r x y.
    apply (exists x0 : nat , (archimedean  x0 (r * IQR (INQ (10 ^ x)))) /\ (y = x0 mod 10)%nat).
  Defined.
  
  Instance Dec_R_comp : Proper (Req ==> eq ==> eq ==> iff) Dec_R.
  Proof.
    hnf ; red ; intros ; hnf ; intros.
    subst.
    split ; intros ; hnf in *.
    - destruct H0. exists x0.
      destruct H0 , H0.
      split ; auto.
      rewrite H in *. split ; auto.
    - destruct H0. exists x0.
      destruct H0 , H0.
      split ; auto.
      split; rewrite H ; auto.
  Qed.
  
  Definition Un_cv'(A : nat -> Q -> Prop) (r : R) : Prop := 
     is_function eq Qeq A /\ (forall eps : R , eps > R0 -> (exists n : nat , 
          forall (m : nat) (q : Q) , (m >= n)%nat -> A m q -> Rabs(IQR q - r) < eps)).
          
  Instance Un_cv'_comp : Proper (eq ==> Req ==> iff) Un_cv'.
  Proof.
    hnf ; red ; intros ; split; subst ; intros.
    - destruct H. split;  auto.
      intros. specialize (H1 _ H2).
      destruct H1. exists x. intros.
      rewrite <- H0. apply (H1 m) ; auto.
    - destruct H. split;  auto.
      intros. specialize (H1 _ H2).
      destruct H1. exists x. intros.
      rewrite H0. apply (H1 m) ; auto.
  Qed.
  
  Definition InDec (R : nat -> nat -> Prop) : Prop := (forall x , R x 0%nat \/ R x 1%nat) /\
        (forall x y z , R x y -> R x z -> y = z).
  Definition Indec (R : nat -> nat ) : Prop := forall x , R x = 0%nat \/ R x = 1%nat.
  Definition InDecR (r : R) : Prop := forall n , Dec_R r n 0 \/ Dec_R r n 1.
  Definition InDecR_n (r : R) (n : nat) : Prop := forall m : nat , (m <= n)%nat -> Dec_R r m 0 \/ Dec_R r m 1.
  Definition NN_T_NNP : (nat -> nat) -> (nat -> nat -> Prop).
    intros.
    apply (H H0 = H1).
  Defined.
  
  Theorem InDec_eqb : forall (x : nat -> nat) , Indec x <-> InDec (NN_T_NNP x).
  Proof.
    intros.
    split ; intros.
    - split ; intros.
      + destruct (H x0) ; auto.
      + hnf in *. subst. auto.
    - hnf in *. intros. destruct H.
      destruct (H x0) ; auto.
  Qed.
  
  Theorem InDecR_all_n : forall (r : R) , InDecR r -> forall n : nat , InDecR_n r n.
  Proof.
    intros. hnf in *. auto.
  Qed.
  
  Definition Dec : Type := {R : nat -> nat -> Prop | InDec R}.
  Definition NNP_Dec (P : nat -> nat -> Prop)
   (H : InDec P): Dec.
    exists P. apply H.
  Defined.

  Definition Dec_r (D : Dec) (r : R) : Prop := (forall n m : nat , Dec_R r n m <-> proj1_sig D n m) /\ In_Search r.

  Instance Dec_r_comp : Proper (eq ==> Req ==> iff) Dec_r.
  Proof.
    hnf ; red ; intros ; subst.
    split ; intros ; destruct H.
    - rewrite H0 in *. split ; auto.
      intros. rewrite <- H. rewrite H0. reflexivity.
    - rewrite <- H0 in *. split ; auto.
      intros. rewrite <- H. rewrite H0. reflexivity.
  Qed.
  
  Definition NNP_T_NQP (x : nat -> nat -> Prop) : nat -> Q -> Prop.
    intros n q.
    apply ((forall m : nat , ((m <= n)%nat -> forall l : nat , Dec_R (IQR q) m l <-> x m l)
                                               /\ ((m > n)%nat -> Dec_R (IQR q) m 0%nat)) /\ (In_Search (IQR q))).
  Defined.

  Instance NNP_T_NQP_comp : Proper (eq ==> eq ==> Qeq ==> iff) NNP_T_NQP.
  Proof.
    hnf ; red ; intros ; red ; intros.
    subst.
    repeat split ; intros ; destruct H ; try (rewrite <- H1 in * ; apply H ; auto) ;
    try (rewrite H1 in * ; apply H ; auto) ; try (rewrite <- H1 ; apply H0) ; try (rewrite H1 ; apply H0).
    apply H ; auto.   
  Qed.
  
  Definition NQP_T_NRP (x : nat -> Q -> Prop) : nat -> R -> Prop.
    intros n r.
    apply (exists q : Q , IQR q == r /\ x n q).
  Defined.

  Instance NQP_T_NRP_comp : Proper (eq ==> eq ==> Req ==> iff) NQP_T_NRP.
  Proof.
    hnf ; red ; intros ; red ; intros.
    subst.
    split ; intros ; destruct H ; exists x ; rewrite H1 in * ; auto.
  Qed.
  
  Theorem Same_Ipart_refl : forall r : R , r >= 0 -> Same_Ipart r r.
  Proof.
    intros r pH.
    destruct (archimedean_exists r) ; auto.
    exists x. destruct H.
    repeat split; auto.
  Qed.
  
  Theorem Same_Ipart_comm : forall r1 r2 : R , Same_Ipart r1 r2 -> Same_Ipart r2 r1.
  Proof.
    intros.
    destruct H , H, H0, H1.
    exists x. repeat split ; auto.
  Qed.
  
  Theorem Same_Ipart_trans : forall r1 r2 r3 : R , Same_Ipart r1 r2 -> Same_Ipart r2 r3 -> Same_Ipart r1 r3.
  Proof.
    intros.
    destruct H , H , H1 , H2.
    destruct H0 , H0 , H4, H5.
    assert (x0 = x)%nat. { apply (Ipart_unique r2); split ; auto. }
    subst.
    exists x. repeat split ; auto.
  Qed.
  
  Instance Same_Ipart_comp : Proper (Req ==> Req ==> iff) Same_Ipart.
  Proof.
    hnf ; red ; intros ; split ; intros ; destruct H1 ; exists x1 ; rewrite H , H0 in * ; auto.
  Qed.
  
  Theorem Same_Ipart_Dec_0 : forall r1 r2 : R , r1 >= 0 -> r2 >= 0 -> Same_Ipart r1 r2 -> forall l : nat , Dec_R r1 0 l <-> Dec_R r2 0 l.
  Proof. 
    intros r1 r2 pH1 pH2. intros.
    hnf in H.
    destruct H , H , H0 , H1.
    assert (10 ^ 0 = 1)%nat. { auto. }
    assert (IQR 1%nat == R1). { rewrite INQ_IQR_INR. reflexivity. }
    split ; intros ; hnf in H5 ; destruct H5 ; rewrite H3 in * ; rewrite H4 in * ; rewrite Rmult_1_r in * ;
    destruct (archimedean_exists r1) ; auto ; destruct H5 , (archimedean_exists r2) ; auto ; destruct H6 , H5, H8.
    - assert (x0 = x)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      assert (x2 = x)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      assert (x1 = x)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      subst. exists x. rewrite H3. rewrite H4. rewrite Rmult_1_r. split ; auto. split; auto.  
    - assert (x0 = x)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      assert (x1 = x)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      assert (x0 = x2)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      subst. exists x2. rewrite H3 , H4 , Rmult_1_r. split ; auto. split ; auto.
  Qed.

  Theorem partial_functional_Dec_R : forall (r : R) (n m1 m2 : nat) , Dec_R r n m1 -> Dec_R r n m2 -> m1 = m2.
  Proof.
    intros.
    hnf in *.
    destruct H , H0 , H , H0.
    assert (x = x0)%nat.  { apply (Ipart_unique (r * IQR(10^n)%nat)) ; auto. }
    subst ; auto.
  Qed.
  
  Theorem image_Defined_Dec_R : forall (r : R) (n : nat) , r >=0 -> exists m : nat , Dec_R r n m.
  Proof.
    intros.
    destruct (archimedean_exists (r * IQR (INQ (10 ^ n)))).
    rewrite INQ_IQR_INR.
    apply Rle_ge. apply Rmult_le_pos ; auto with real.
    exists (x mod 10).
    hnf. exists x.  auto.
  Qed.
  
  Theorem Dec_R_pro1 : forall (r : R)(n m : nat) , Dec_R r n m -> (m < 10)%nat.
  Proof.
    intros.
    hnf in H.
    destruct H, H. 
    subst.
    apply Nat.mod_upper_bound. omega.
  Qed.
  
  Theorem Zero_Dec : forall (n : nat) , Dec_R R0 n 0.
  Proof.
    intros.
    hnf.
    exists O.
    split ; auto.
    rewrite Rmult_0_l.
    split ; rewrite <- IQR_R0 ; try (apply IQR_le) ; try (apply IQR_lt) ; simpl.
    rewrite INQ_Qeq_0. lra.
    rewrite INQ_Qeq_1. lra.
  Qed.
  
  Theorem Two_Dec : Dec_R 2 0 2.
  Proof.
    hnf ; intros.
    exists 2%nat.
    split ; auto.
    split .
    - simpl. 
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      assert (2 = 1 + 1)%Z. { auto. }
      rewrite H. rewrite plus_IZR. unfold Rdiv. rewrite Rmult_plus_distr_r. auto with real. 
    - simpl.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      unfold Rdiv.
      rewrite <- Rmult_plus_distr_r. rewrite <- plus_IZR. simpl.
      apply Rmult_lt_r ; auto with real.
      apply Rinv_0_lt_compat. auto with real.
  Qed.
  
  Theorem Dec_R_eq_Same_Ipart : forall (r1 r2 :R)(n :nat) , In_Search r1 -> In_Search r2 -> (forall (j : nat) ,(j <= n)%nat -> 
               (forall m : nat , Dec_R r1 j m <-> Dec_R r2 j m)) -> (forall (j : nat) , (j <= n)%nat -> Same_Ipart (r1 * IQR (10^j)%nat) (r2 * IQR(10^j)%nat)).
  Proof.
    intros.
    generalize dependent n.
    induction j ; intros.
    - simpl in *.
      destruct (image_Defined_Dec_R r1 O). apply H.
      specialize (H1 O H2 x).
      destruct H1. specialize (H1 H3). clear H4 H2.
      destruct H1 , H1 , H1.
      destruct H3 , H3 , H3.
      simpl in H1 , H6 , H3 , H4.
      assert (x1 = x0).
      {
        symmetry in H2 , H5.
        assert (x < 10)%nat. { rewrite <- H5. apply Nat.mod_upper_bound. auto. }
        apply mod_exists in H5 ; auto.
        apply mod_exists in H2 ; auto.
        destruct H5, H2.
        assert (x1 < 10)%nat.
        { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with (r1 * IQR 1%nat); auto.
          rewrite INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_r. apply H.
        }
        assert (x2 = 0)%nat. { omega. }
        assert (x0 < 10)%nat.
        { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with (r2 * IQR 1%nat); auto.
          rewrite INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_r. apply H0.
        }
        assert (x3 = 0)%nat. { omega. }
        subst. reflexivity.
      }
      exists x0. subst. repeat split ; auto.
    - assert (j <= n)%nat. { omega. }
      specialize (IHj n H1 H3).
      specialize (H1 _ H2).
      clear H2 H3.
      destruct IHj.
      destruct H2 , H3 , H4.
      destruct (image_Defined_Dec_R r1 (S j)).
      apply H.
      assert (Dec_R r2 (S j) x0). { apply H1. auto. }
      clear H1.
      destruct H6 , H1 , H1. 
      destruct H7 , H7 , H7.
      symmetry in H6 , H9.
      assert (x0 < 10)%nat. { rewrite <- H6. apply Nat.mod_upper_bound. auto. }
      apply mod_exists in H6 ; auto.
      apply mod_exists in H9 ; auto.
      destruct H6 , H9.
      subst.
      assert (x = x3)%nat.
      {
        apply NNPP.
        intro.
        apply nat_total_order in H6.
        destruct H6 . 
        - apply lt_le_S in H6.
          apply (mult_le_compat_l _ _ 10) in H6.
          assert( 10 * S x <= 10 * x3 + x0)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x3 + x0)%nat) ; auto.
          apply INQ_le in H9. apply IQR_le in H9.
          apply Rlt_le_trans with (IQR (10 * S x)%nat) ; auto.
          apply Rle_lt_trans with (r1 * IQR (10 ^ j)%nat * IQR (10)%nat).
          + destruct H. destruct H.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
              rewrite Nat.pow_succ_r'. omega.
            * rewrite H in *. clear H. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. lra.
        - apply lt_le_S in H6.
          apply (mult_le_compat_l _ _ 10) in H6.
          assert( 10 * x3 + x0 + 1 <= 10 * S x3)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x3 + x0 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H9 H6 ). clear H6 H9.
          apply INQ_le in H12. apply IQR_le in H12.
          apply Rle_trans with (IQR (10 * x)%nat) ; auto.
          apply Rle_trans with (IQR x * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite <- mult_IQR.
            apply IQR_le. rewrite INQ_mult. lra.
          + apply Rle_trans with (r1 * IQR (10^j)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H. destruct H.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** rewrite H in *. clear H. rewrite !Rmult_0_l. apply Rle_refl.
      }
      assert (x = x4)%nat.
      {
        apply NNPP.
        intro.
        apply nat_total_order in H9.
        destruct H9 . 
        - apply lt_le_S in H9.
          apply (mult_le_compat_l _ _ 10) in H9.
          assert( 10 * S x <= 10 * x4 + x0)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x4 + x0)%nat) ; auto.
          apply INQ_le in H12. apply IQR_le in H12.
          apply Rlt_le_trans with (IQR (10 * S x)%nat) ; auto.
          apply Rle_lt_trans with (r2 * IQR (10 ^ j)%nat * IQR (10)%nat).
          + destruct H0. destruct H0.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
              rewrite Nat.pow_succ_r'. omega.
            * rewrite H0 in *. clear H0. subst. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. lra.
        - apply lt_le_S in H9.
          apply (mult_le_compat_l _ _ 10) in H9.
          assert( 10 * x4 + x0 + 1 <= 10 * S x4)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x4 + x0 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H12 H9 ). clear H12 H9.
          apply INQ_le in H13. apply IQR_le in H13.
          apply Rle_trans with (IQR (10 * x)%nat) ; auto.
          apply Rle_trans with (IQR x * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite <- mult_IQR.
            apply IQR_le. rewrite INQ_mult. lra.
          + apply Rle_trans with (r2 * IQR (10^j)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H0. destruct H0.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** rewrite H0 in *. rewrite !Rmult_0_l. apply Rle_refl.
      }
      subst.
      exists (10 * x4 + x0)%nat. repeat split ; auto.
  Qed.
  
  Theorem Dec_R_eq_lemma : forall (r1 r2 :R)(n :nat) , In_Search r1 -> In_Search r2 -> (forall (j : nat) ,(j <= n)%nat -> 
               (forall m : nat , Dec_R r1 j m <-> Dec_R r2 j m)) -> (Rabs(r1 - r2) < IQR 1%nat / IQR (10 ^ n)%nat).
  Proof.
    intros.
    induction n.
    - simpl in *. assert (O <= O)%nat. { omega. }
      pose proof Dec_R_eq_Same_Ipart r1 r2 _ H H0 H1 O H2.
      destruct H3 , H3 , H4 ,H5. clear H2.
      simpl in *.
      apply Rabs_tri. split.
      + apply Rmult_lt_l with (R1).
        * rewrite <- IQR_R0. rewrite <- IQR_R1. apply IQR_lt. lra.
        * apply Rlt_le_trans with (IQR (x + 1)%nat).
          ** apply Rle_lt_trans with (r1 * IQR 1%nat) ; auto.
             rewrite Rmult_comm. destruct H.
             destruct H ; auto with real.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite <- plus_IQR. apply IQR_le.
                 rewrite INQ_plus. lra.
             *** apply Rle_trans with (r2 + IQR 1%nat).
                 **** apply Rplus_le_compat_r . apply Rle_trans with (r2 * IQR 1%nat) ; auto with real.
                      rewrite <- Rmult_1_r. destruct H0. 
                      right. rewrite IQR_R1. ring.
                 **** rewrite Rmult_1_l. apply Rplus_le_compat_l. 
                      rewrite INQ_IQR_INR. unfold Rdiv. simpl.
                      rewrite IZR_R1. assert (IPR 1 == 1). { auto with real. }
                      rewrite H2. assert (/ 1 == 1). { auto with real. }
                      rewrite H7. rewrite !Rmult_1_l. auto with real.
      + apply Rlt_Rminus_Rplus. apply Rmult_lt_l with (R1).
        * rewrite <- IQR_R0. rewrite <- IQR_R1. apply IQR_lt. lra.
        * apply Rlt_le_trans with (IQR (x + 1)%nat).
          ** apply Rle_lt_trans with (r2 * IQR 1%nat) ; auto.
             rewrite Rmult_comm. destruct H0.
             destruct H0 ; auto with real.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite <- plus_IQR. apply IQR_le.
                 rewrite INQ_plus. lra.
             *** apply Rle_trans with (r1 + IQR 1%nat).
                 **** apply Rplus_le_compat_r . apply Rle_trans with (r1 * IQR 1%nat) ; auto.
                      rewrite <- Rmult_1_r. destruct H. right. rewrite IQR_R1. ring.
                 **** rewrite Rmult_1_l. rewrite Rplus_comm. apply Rplus_le_compat_r. 
                      rewrite INQ_IQR_INR. unfold Rdiv. simpl.
                      rewrite IZR_R1. assert (IPR 1 == 1). { auto with real. }
                      rewrite H2. assert (/ 1 == 1). { auto with real. }
                      rewrite H7. rewrite !Rmult_1_l. auto with real.
    - assert (forall j : nat, (j <= n)%nat -> forall m : nat, Dec_R r1 j m <-> Dec_R r2 j m).
      {  intros. apply H1. omega. }
      assert (S n <= S n)%nat. { omega. }
      pose proof Dec_R_eq_Same_Ipart r1 r2 _ H H0 H1 (S n) H3.
      destruct H4 , H4 , H5 ,H6. clear H3 H2 IHn.
      apply Rabs_tri. split.
      + apply Rmult_lt_l with (IQR(10 ^ S n)%nat).
        * rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
        * apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
          ** rewrite Rmult_comm. auto.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite <- plus_IQR. apply IQR_le.
                 rewrite INQ_plus. lra.
             *** apply Rle_trans with (IQR (10 ^ S n)%nat * r2 + IQR 1%nat).
                 **** apply Rplus_le_compat_r. rewrite Rmult_comm. auto.
                 **** rewrite Rmult_plus_distr_l. apply Rplus_le_compat_l.
                      unfold Rdiv.
                      rewrite (Rmult_comm (IQR 1%nat) (/ IQR (10 ^ S n)%nat)).
                      rewrite <- Rmult_assoc.
                      rewrite Rinv_r. 
                      ++ rewrite Rmult_1_l. apply Rle_refl.
                      ++ unfold not. intros.
                         apply (Rlt_irrefl R0). rewrite <- H2 at 2.
                         rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0.
                         apply INQ_lt. apply Max_powan_0. omega.
      + apply Rlt_Rminus_Rplus.
        apply Rmult_lt_l with (IQR(10 ^ S n)%nat).
        * rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
        * apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
          ** rewrite Rmult_comm. auto.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite <- plus_IQR. apply IQR_le.
                 rewrite INQ_plus. lra.
             *** apply Rle_trans with (IQR (10 ^ S n)%nat * r1 + IQR 1%nat).
                 **** apply Rplus_le_compat_r. rewrite Rmult_comm. auto.
                 **** rewrite Rmult_plus_distr_l. rewrite Rplus_comm. apply Rplus_le_compat_r.
                      unfold Rdiv.
                      rewrite (Rmult_comm (IQR 1%nat) (/ IQR (10 ^ S n)%nat)).
                      rewrite <- Rmult_assoc.
                      rewrite Rinv_r. 
                      ++ rewrite Rmult_1_l. apply Rle_refl.
                      ++ unfold not. intros.
                         apply (Rlt_irrefl R0). rewrite <- H2 at 2.
                         rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0.
                         apply INQ_lt. apply Max_powan_0. omega.
  Qed.
  
  Theorem Dec_R_eq  : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 == r2 <-> (forall (j : nat) , forall m : nat , Dec_R r1 j m <-> Dec_R r2 j m).
  Proof.
    split ; intros ; try (rewrite H1 ; reflexivity).
    apply Req_same.
    intros.
    apply eps_gt_10n in H2.
    destruct H2.
    apply Rlt_trans with (IQR 1 * / IQR (10 ^ x)%nat) ; auto.
    apply Dec_R_eq_lemma ; auto.
    rewrite !INQ_IQR_INR. rewrite IQR_R1. auto with real.
  Qed.
  
  Theorem Dec_R_not_eq : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> ~ r1 == r2 <-> exists (j : nat), (forall m : nat,  Dec_R r1 j m -> ~ Dec_R r2 j m).
  Proof.
    intros.
    split.
    - intros.
      apply NNPP.
      intro.
      apply H1.
      pose proof not_ex_all_not _ _ H2. simpl in *.
      apply Dec_R_eq ; auto.
      intros. specialize (H3 j).
      apply not_all_ex_not in H3.
      destruct H3.
      apply not_imply_elim in H3 as goal.
      apply not_imply_elim2 in H3.
      apply NNPP in H3.
      split ; intros.
      + assert (m = x)%nat. { apply (partial_functional_Dec_R r1 j) ; auto. }
        subst ; auto.
      + assert (m = x)%nat. { apply (partial_functional_Dec_R r2 j) ; auto. }
        subst ; auto.
    - intros.
      destruct H1.
      intro.
      pose proof image_Defined_Dec_R r2 x.
      assert (r2 >= 0). { apply H0. }
      specialize (H3 H4). 
      destruct H3. 
      apply (H1 x0) ; auto.
      rewrite H2 ; auto.
  Qed.
  
  Theorem Dec_R_lt_lemma :forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> (exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 < m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2 -> (m1 = m2)%nat))) -> r1 < r2.
  Proof.
    intros.
    destruct H1. destruct H1.
    destruct x.
    + destruct (image_Defined_Dec_R r1 O). apply H.
      destruct (image_Defined_Dec_R r2 O). apply H0.
      assert (x < x0)%nat. { apply H1 ; auto. }
      destruct H3 , H3 , H3.
      destruct H4 , H4 , H4.
      symmetry in H6 , H8.
      assert (x0 < 10)%nat. { rewrite <- H8. apply Nat.mod_upper_bound. auto. }
      apply mod_exists in H6 ; try (omega).
      apply mod_exists in H8 ; auto.
      destruct H6, H8.
      assert (x1 < 10)%nat.
      { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with (r1 * IQR 1%nat); auto.
        rewrite INQ_IQR_INR. rewrite INR_R1. 
        rewrite Rmult_1_r. apply H.
      }
      assert (x3 = 0)%nat. { omega. }
      assert (x2 < 10)%nat.
      { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with (r2 * IQR 1%nat); auto.
        rewrite INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_r. apply H0.
      }
      assert (x4 = 0)%nat. { omega. }
      subst.
      apply lt_le_S in H5. rewrite <- Nat.add_1_r in H5.
      rewrite <- Rmult_1_r. rewrite <- Rmult_1_r at 1.
      rewrite mult_0_r in *. rewrite plus_0_l in *.
      assert (IQR (10 ^ 0)%nat == 1). { auto with real. }
      rewrite H6 in *. rewrite !Rmult_1_r in *.
      apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
      apply Rle_trans with (IQR x0) ; auto.
      apply IQR_le. apply INQ_le. auto.
    + pose proof Dec_R_eq_Same_Ipart _ _ x H H0.
      assert (forall j : nat, (j <= x)%nat -> forall m : nat,  Dec_R r1 j m <-> Dec_R r2 j m).
      { split ; intros.
        - destruct (image_Defined_Dec_R r2 j). apply H0.
          assert (m = x0)%nat. { apply (H2 j) ; auto. omega. }
          subst ; auto.
        - destruct (image_Defined_Dec_R r1 j). apply H.
          assert (x0 = m)%nat. { apply (H2 j) ; auto. omega. }
          subst ; auto.
      }
      assert (x <= x)%nat. { omega. }
      specialize (H3 H4 x H5). clear H4 H5.
      destruct H3 , H3 , H4 , H5.
      destruct (image_Defined_Dec_R r1 (S x)). apply H.
      destruct (image_Defined_Dec_R r2 (S x)). apply H0.
      assert (x1 < x2)%nat. { apply H1 ; auto. }
      destruct H7 , H7 ,H7 ,H8 , H8 ,H8.
      symmetry in H10 , H12.
      assert (x2 < 10)%nat. { rewrite <- H12. apply Nat.mod_upper_bound. auto. }
      apply mod_exists in H10 ; try (omega).
      apply mod_exists in H12 ; auto.
      destruct H10 , H12.
      clear H1 H2. subst.
      assert (x0 = x5)%nat.
      {
        apply NNPP.
        intro.
        apply nat_total_order in H1.
        destruct H1 . 
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * S x0 <= 10 * x5 + x1)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x5 + x1)%nat) ; auto.
          apply INQ_le in H2. apply IQR_le in H2.
          apply Rlt_le_trans with (IQR (10 * S x0)%nat) ; auto.
          apply Rle_lt_trans with (r1 * IQR (10 ^ x)%nat * IQR (10)%nat).
          + destruct H. destruct H.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
              rewrite Nat.pow_succ_r'. omega.
            * rewrite H. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x0 + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. lra.
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * x5 + x1 + 1 <= 10 * S x5)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x5 + x1 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H2 H1 ). clear H2 H1.
          apply INQ_le in H10. apply IQR_le in H10.
          apply Rle_trans with (IQR (10 * x0)%nat) ; auto.
          apply Rle_trans with (IQR x0 * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite <- mult_IQR.
            apply IQR_le. rewrite INQ_mult. lra.
          + apply Rle_trans with (r1 * IQR (10^x)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H. destruct H.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** rewrite H. rewrite !Rmult_0_l. apply Rle_refl.
      }
      subst x5.
      assert (x0 = x6)%nat.
      {
        apply NNPP.
        intro.
        apply nat_total_order in H1.
        destruct H1 . 
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * S x0 <= 10 * x6 + x2)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x6 + x2)%nat) ; auto.
          apply INQ_le in H2. apply IQR_le in H2.
          apply Rlt_le_trans with (IQR (10 * S x0)%nat) ; auto.
          apply Rle_lt_trans with (r2 * IQR (10 ^ x)%nat * IQR (10)%nat).
          + destruct H0. destruct H0.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
              rewrite Nat.pow_succ_r'. omega.
            * rewrite H0. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x0 + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite <-mult_IQR. apply IQR_le. rewrite INQ_mult. lra.
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * x6 + x2 + 1 <= 10 * S x6)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x6 + x2 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H2 H1 ). clear H2 H1.
          apply INQ_le in H10. apply IQR_le in H10.
          apply Rle_trans with (IQR (10 * x0)%nat) ; auto.
          apply Rle_trans with (IQR x0 * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite <- mult_IQR.
            apply IQR_le. rewrite INQ_mult. lra.
          + apply Rle_trans with (r2 * IQR (10^x)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rge_le in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H0. destruct H0.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite <- mult_IQR. apply IQR_le. rewrite INQ_mult. apply INQ_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** rewrite H0. rewrite !Rmult_0_l. apply Rle_refl.
      }
      subst.
      assert (10 * x6 + x1 < 10 * x6 + x2)%nat. { omega. }
      apply lt_le_S in H1. rewrite <- Nat.add_1_r in H1.
      apply INQ_le in H1. apply IQR_le in H1.
      apply Rmult_lt_r with (IQR (10 ^ S x)%nat).
      - rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0.
        apply INQ_lt. apply Max_powan_0. omega.
      - apply Rlt_le_trans with (IQR (10 * x6 + x1 + 1)%nat) ; auto.
        apply Rle_trans with (IQR (10 * x6 + x2)%nat) ; auto.
  Qed.
  
  Theorem Dec_R_lt_same : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 < r2 <-> 
                       exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 < m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2 -> (m1 = m2)%nat)).
  Proof.
    split ; intros.
    - assert (~ r1 == r2). { auto with real. }
      apply Dec_R_not_eq in H2 ; auto.
      destruct H2.
      set (fun x => forall m : nat, Dec_R r1 x m -> ~ Dec_R r2 x m).
      assert (forall n : nat, P n \/ ~ P n). { intros. apply classic. }
      assert (exists n : nat, P n). { exists x. auto. }
      pose proof dec_inh_nat_subset_has_unique_least_element P H3 H4.
      repeat destruct H5. subst P. simpl in *. clear H3 H4.
      assert (forall n : nat , (n < x0)%nat -> forall m : nat , Dec_R r1 n m <-> Dec_R r2 n m).
      {
        intros n H3.
        apply NNPP. intro.
        apply not_all_ex_not in H4. destruct H4.
        apply Decidable.not_iff in H4 ; try (apply classic).
        destruct H4 , H4 ; apply (lt_irrefl n) ; apply lt_le_trans with x0 ; auto ; apply H7 ; intros.
        - assert (x1 = m)%nat. { apply (partial_functional_Dec_R r1 n) ; auto. }
          subst. auto.
        - intro. assert (m = x1). { apply (partial_functional_Dec_R r2 n) ; auto. }
          subst. auto.  
      }
      exists x0.
      split ; intros.
      + assert (m1 <> m2)%nat. { intro. subst. apply (H5 m2); auto. }
        apply nat_total_order in H9. destruct H9 ; auto.
        exfalso. apply (Rlt_irrefl r1). apply Rlt_trans with r2 ; auto.
        apply Dec_R_lt_lemma ; auto.
        exists x0.
        split ; intros. 
        * assert (m0 = m2)%nat. { apply (partial_functional_Dec_R r2 x0) ; auto. }
          assert (m1 = m3)%nat. { apply (partial_functional_Dec_R r1 x0) ; auto. }
          omega.
        * apply (partial_functional_Dec_R r2 k) ; auto.
          apply H3 ; auto.
      + apply H3 in H8 ;auto.
        apply (partial_functional_Dec_R r2 k); auto.
    - apply Dec_R_lt_lemma ; auto. 
  Qed.
  
  Theorem Dec_R_lt : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 < r2 <-> 
                       exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 < m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2 -> (m1 <= m2)%nat)).
  Proof.
    split ; intros.
    - apply Dec_R_lt_same in H1 ; auto.
      repeat destruct H1.
      exists x.
      split ; auto.
      intros.
      apply Nat.eq_le_incl.
      apply (H2 k) ; auto.
    - repeat destruct H1.
      set ((fun x => forall m1 m2 : nat, Dec_R r1 x m1 -> Dec_R r2 x m2 -> (m1 < m2)%nat)).
      assert (forall n : nat, P n \/ ~ P n). { intros. apply classic. }
      assert (exists n : nat, P n). { exists x. auto. }
      pose proof dec_inh_nat_subset_has_unique_least_element P H3 H4.
      repeat destruct H5.
      subst P. clear H3 H4.
      apply Dec_R_lt_same ; auto.
      exists x0.
      split ; auto.
      intros.
      assert (k < x)%nat. { apply lt_le_trans with x0 ; auto. }
      specialize (H2 k H9 _ _ H4 H8).
      destruct H2 ; auto.
      exfalso. 
      apply (lt_irrefl k).
      apply lt_le_trans with x0 ; auto.
      apply H7 ; auto. intros.
      assert (m1 = m0)%nat. { apply (partial_functional_Dec_R _ _ _ _ H4 H10). }
      assert (S m = m2)%nat. { apply (partial_functional_Dec_R _ _ _ _ H8 H11). }
      subst. omega.
  Qed.
  
  Theorem Dec_R_gt : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 > r2 <-> 
                      exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 > m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2
                                                                                                            -> (m1 >= m2)%nat)).
  Proof.
    intros.
    pose proof (Dec_R_lt r2 r1 H0 H).
    clear H H0.
    split.
    - intros. 
      rewrite H1 in H.
      repeat destruct H.
      exists x.
      split ; auto.
      intros. apply (H0 k) ; auto.
    - intros.
      apply H1.
      repeat destruct H.
      exists x.
      split ; intros . 
      + apply H ; auto.
      + apply (H0 k) ; auto.
  Qed.
  
  Theorem Dec_R_ge : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> (forall n m1 m2 : nat , Dec_R r1 n m1 -> Dec_R r2 n m2 -> (m1 >= m2)%nat) -> r1 >= r2.
  Proof.
    intros.
    destruct (classic (exists n : nat , forall m1 m2 : nat , Dec_R r1 n m1 -> Dec_R r2 n m2 -> (m1 > m2)%nat)).
    - left. destruct H2. apply Dec_R_gt ; auto.
      exists x. split ; auto. intros. apply (H1 k) ; auto.
    - pose proof (not_ex_all_not _ _ H2). simpl in H3.
      right. apply Dec_R_eq ; auto.
      split ; intros.
      * destruct (image_Defined_Dec_R r2 j). apply H0.
        specialize (H1 _ _ _ H4 H5).
        specialize (H3 j).
        destruct H1 ; auto.
        exfalso. apply H3.
        intros. 
        assert (m1 = S m)%nat. { apply (partial_functional_Dec_R r1 j) ; auto. }
        assert (m2 = x)%nat. { apply (partial_functional_Dec_R r2 j) ; auto. }
        subst. omega.
      * destruct (image_Defined_Dec_R r1 j). apply H.
        specialize (H1 _ _ _ H5 H4). 
        specialize (H3 j).
        destruct H1 ; auto.
        exfalso. apply H3.
        intros. 
        assert (m1 = S m0)%nat. { apply (partial_functional_Dec_R r1 j) ; auto. }
        assert (m2 = m)%nat. { apply (partial_functional_Dec_R r2 j) ; auto. }
        subst. omega.
  Qed.
  
  Theorem Same_Ipart_pow10n : forall (r : R)(n : nat), In_Search r -> InDecR_n r (S n) -> 
                                Same_Ipart (r * IQR (10 ^ n)%nat) ((r + IQR (1%nat / (10 ^ S n)%nat)) * IQR (10 ^ n)%nat).
  Proof.
    intros r n pH. intros. 
    destruct (archimedean_exists (r * IQR (10 ^ n)%nat)).
    rewrite INQ_IQR_INR. destruct pH. apply Rle_ge.
    apply Rmult_le_pos ; auto with real.
    destruct H0.
    exists x.
    repeat split ; auto ; rewrite Rmult_plus_distr_r in * ; repeat rewrite mult_IQR in *.
    + apply Rle_trans with (r * (IQR (10 ^ n)%nat)) ; auto.
      rewrite <- Rplus_0_r at 1. 
      apply Rplus_le_compat_l. rewrite <- IQR_R0. rewrite <- mult_IQR. apply IQR_le.
      rewrite INQ_Qeq_1. unfold Qdiv. 
      rewrite Qmult_1_l. apply Qmult_le_0_compat.
      * apply Qinv_le_0_compat. rewrite <- INQ_Qeq_0.
        apply INQ_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
      * rewrite <- INQ_Qeq_0.
        apply INQ_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
    + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
      assert (INQ(1) / INQ(10^S n) * INQ (10 ^ n) == INQ (1) / INQ(10) )%Q. 
      { 
        apply (Qmult_inj_r _ _ (INQ 10)).
        - intro. rewrite <- INQ_Qeq_0 in H3. apply Qeq_INQ_eq in H3. inversion H3.
        - rewrite <- Qmult_assoc. rewrite INQ_mult.  rewrite <- H2.
          field. split ; intro.
          + rewrite <- INQ_Qeq_0 in H3. apply Qeq_INQ_eq in H3. inversion H3.
          + apply (Qlt_irrefl 0%Q). rewrite <- H3 at 2.
            rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0 ; omega.
      }
      assert (IQR (1%nat / (10 ^ S n)%nat * (10 ^ n)%nat) == IQR (1%nat / 10%nat)).
      { apply NNPP. 
        intro. apply Rdichotomy in H4.
        destruct H4 ; apply lt_IQR in H4; rewrite H3 in H4 ; apply Qlt_irrefl in H4 ; auto.
      }
      assert (IQR (10 ^ S n)%nat == IQR (10 ^ n)%nat * IQR (10)%nat).
      { rewrite <- mult_IQR. 
        apply NNPP.  intro. apply Rdichotomy in H5.
        destruct H5 ; apply lt_IQR in H5 ; rewrite INQ_mult in * ; apply INQ_lt in H5 ;
        rewrite Nat.pow_succ_r' in H5 ; rewrite mult_comm in H5 ; apply lt_irrefl in H5; auto.
      } 
      rewrite <-mult_IQR. rewrite H4. clear H3 H4. 
      specialize (H (S n)). assert (S n <= S n)%nat. { omega. } specialize (H H3). clear H3. 
      destruct H , H , H , H ; symmetry in H3 ; apply mod_exists in H3 ; try (omega) ;
      destruct H3.
      - rewrite plus_0_r in H3. subst x0.
        rewrite H5 in *. rewrite <- Rmult_assoc in *.
        rewrite mult_comm in *.
        assert (IQR (x1 * 10)%nat == IQR x1 * IQR (10)%nat).
        { rewrite <- mult_IQR. apply NNPP. intro.
          apply Rdichotomy in H3. 
          destruct H3 ; apply lt_IQR in H3 ; rewrite INQ_mult in * ; apply Qlt_irrefl in H3 ; auto.
        }
        assert (IQR (x1 * 10 + 1)%nat == (IQR x1 + IQR (1%nat / 10%nat)) * IQR 10%nat).
        {
          rewrite <- plus_IQR. rewrite <- mult_IQR.
          apply NNPP. intro. apply Rdichotomy in H6.
          assert (INQ(1) == INQ(1) / INQ(10) * INQ(10))%Q.
          { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H7 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
          destruct H6 ; apply lt_IQR in H6 ; rewrite Qmult_plus_distr_l in H6 ; rewrite <- H7 in H6 ;
          rewrite INQ_mult in H6 ; rewrite INQ_plus in H6;  apply Qlt_irrefl in H6; auto.
        }
        rewrite H6 in *. rewrite H3 in *.
        assert (IQR (10)%nat > R0). { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
        apply Rmult_lt_r in H4 ; auto.
        apply Rmult_le_r in H ; auto.
        assert (r * IQR (10 ^ n)%nat < IQR (x1 + 1)%nat).
        { apply Rlt_trans with (IQR x1 + IQR (1%nat / 10%nat)) ; auto.
          rewrite <- plus_IQR.
          apply IQR_lt.
          rewrite <- INQ_plus.
          apply Qplus_lt_r. unfold Qdiv.
          rewrite INQ_Qeq_1. rewrite Qmult_1_l. apply Qlt_shift_inv_r.
          - rewrite <- INQ_Qeq_0. apply INQ_lt. omega.
          - rewrite Qmult_1_l. rewrite <- INQ_Qeq_1. apply INQ_lt. omega.
        }
        assert (x1 = x)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; split ; auto. }
        subst.
        apply Rlt_trans with (IQR x + IQR (1%nat / 10%nat) + IQR(1%nat / 10%nat)). 
        * apply Rplus_lt_compat_r. auto.
        * rewrite <- !plus_IQR. apply IQR_lt.
          rewrite <- INQ_plus.
          rewrite <- Qplus_assoc.
          apply Qplus_lt_r.
          unfold Qdiv.
          rewrite <- Qmult_plus_distr_l. rewrite INQ_plus. simpl.
          rewrite INQ_Qeq_1. 
          assert (INQ 10 > 0)%Q.
          { rewrite <- IQR_R0 in H7. apply lt_IQR. auto. }
          assert (INQ (10) * / INQ (10) == 1)%Q.
          { apply Qmult_inv_r. intro.
            rewrite H10 in H9. apply Qlt_irrefl in H9. auto.
          }
          rewrite <- H10.
          apply Qmult_lt_r.
          -- apply Qinv_lt_0_compat. auto.
          -- apply INQ_lt. omega.
      - subst x0. 
        rewrite H5 in *. rewrite <- Rmult_assoc in *.
        rewrite mult_comm in *. rewrite <- plus_assoc in H4. 
        assert (IQR (x1 * 10 + (1+1))%nat == (IQR x1 + IQR (2%nat / 10%nat)) * IQR 10%nat).
        {
          rewrite <- plus_IQR. rewrite <- mult_IQR.
          apply NNPP. intro. apply Rdichotomy in H3.
          assert (INQ(2) == INQ(2) / INQ(10) * INQ(10))%Q.
          { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H6 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
          destruct H3 ; apply lt_IQR in H3 ; rewrite Qmult_plus_distr_l in H3 ; rewrite <- H6 in H3 ;
          rewrite INQ_mult in H3 ; rewrite INQ_plus in H3;  apply Qlt_irrefl in H3; auto.
        }
        assert (IQR (x1 * 10 + 1)%nat == (IQR x1 + IQR (1%nat / 10%nat)) * IQR 10%nat).
        {
          rewrite <- plus_IQR. rewrite <- mult_IQR.
          apply NNPP. intro. apply Rdichotomy in H6.
          assert (INQ(1) == INQ(1) / INQ(10) * INQ(10))%Q.
          { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H7 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
          destruct H6 ; apply lt_IQR in H6 ; rewrite Qmult_plus_distr_l in H6 ; rewrite <- H7 in H6 ;
          rewrite INQ_mult in H6 ; rewrite INQ_plus in H6;  apply Qlt_irrefl in H6; auto.
        }
        rewrite H6 in *. rewrite H3 in *.
        assert (IQR (10)%nat > R0). { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
        apply Rmult_lt_r in H4 ; auto.
        apply Rmult_le_r in H ; auto.
        assert (INQ 10 > 0)%Q.
        { rewrite <- IQR_R0 in H7. apply lt_IQR. auto. }
        assert (INQ (10) * / INQ (10) == 1)%Q.
        { apply Qmult_inv_r. intro.
          rewrite H9 in H8. apply Qlt_irrefl in H8. auto.
        }
        assert (r * IQR (10 ^ n)%nat < IQR (x1 + 1)%nat).
        { apply Rlt_trans with (IQR x1 + IQR (2%nat / 10%nat)) ; auto.
          rewrite <- plus_IQR.
          apply IQR_lt.
          rewrite <- INQ_plus.
          apply Qplus_lt_r. unfold Qdiv.
          rewrite INQ_Qeq_1. rewrite <- H9.
          apply Qmult_lt_r.
          -- apply Qinv_lt_0_compat. auto.
          -- apply INQ_lt. omega.
        }
        assert (IQR x1 <= r * IQR (10 ^ n)%nat).
        { apply Rle_trans with (IQR x1 + IQR (1%nat / 10%nat)) ; auto.
          rewrite <- plus_IQR. apply IQR_le.
          rewrite <- Qplus_0_r at 1. apply Qplus_le_r.
          rewrite INQ_Qeq_1. unfold Qdiv. rewrite Qmult_1_l.
          apply Qinv_le_0_compat. auto.
          apply Qlt_le_weak. auto.
        }
        assert (x1 = x)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; split ; auto. }
        subst.
        apply Rlt_trans with (IQR x + IQR (2%nat / 10%nat) + IQR(1%nat / 10%nat)). 
        * apply Rplus_lt_compat_r. auto.
        * rewrite <- !plus_IQR. apply IQR_lt.
          rewrite <- INQ_plus.
          rewrite <- Qplus_assoc.
          apply Qplus_lt_r.
          unfold Qdiv.
          rewrite <- Qmult_plus_distr_l. rewrite INQ_plus. simpl.
          rewrite INQ_Qeq_1. 
          rewrite <- H9.
          apply Qmult_lt_r.
          -- apply Qinv_lt_0_compat. auto.
          -- apply INQ_lt. omega.
  Qed. 
  
  Theorem image_defined_NNP_T_NQP : forall (x : nat -> nat -> Prop) , 
                  InDec x -> forall n : nat , exists q : Q , (NNP_T_NQP x) n q.
  Proof.
    intros.
    destruct H.
    induction n.
    - destruct (H O).
      + exists (INQ O).
        split ; intros. 
        * split ; intros. 
          ** apply le_n_0_eq in H2. subst.
             split ; intros ; hnf in * .
             *** destruct H2 , H2 , H2.
                 rewrite <- mult_IQR in *.
                 apply le_IQR in H2. apply lt_IQR in H4. simpl in H2 , H4.
                 rewrite INQ_mult in *. rewrite mult_1_r in *.
                 apply INQ_le in H2. apply INQ_lt in H4.
                 assert (x0 = O). { omega. } subst.
                 assert (0 mod 10 = 0)%nat. { auto. }
                 rewrite H3. auto.
             *** exists O.
                 assert (l = 0)%nat. { apply (H0 O); auto. }
                 split ; auto.
                 split ; rewrite <- mult_IQR ; try (apply IQR_lt) ; try (apply IQR_le);
                 rewrite INQ_mult ; try (apply INQ_le) ; try (apply INQ_lt) ; omega.
          ** hnf.
             exists O. split ; auto.
             split ; rewrite <- mult_IQR ; try (apply IQR_lt) ; try (apply IQR_le);
             rewrite INQ_mult ; try (apply INQ_le) ; try (apply INQ_lt) ; omega.
        * split.
          ** rewrite <- IQR_R0. apply IQR_le.
             rewrite INQ_Qeq_0. lra.
          ** apply IQR_lt. apply INQ_lt. omega.
      + exists (INQ (1)).
        hnf. split ; intros.
        * split ; intros.
          ** assert (m = O). { omega. } subst.
             split ; intros ; hnf in *. 
             *** destruct H3 , H3 , H3.
                 rewrite <- mult_IQR in *.
                 apply le_IQR in H3. apply lt_IQR in H5.  simpl in H3 , H5.
                 rewrite INQ_mult in *. rewrite mult_1_l in *.
                 apply INQ_le in H3. apply INQ_lt in H5.
                 assert (x0 = 1)%nat. { omega. } subst.
                 assert (1 mod 10 = 1)%nat. { auto. }
                 rewrite H4. auto.
             *** exists 1%nat.
                 assert (1 = l)%nat. { apply (H0 O) ; auto. }
                 subst.
                 split ; auto.
                 split ; rewrite <- mult_IQR ; try (apply IQR_lt) ; try (apply IQR_le);
                 rewrite INQ_mult ; simpl ; try (apply INQ_le ; omega);  try (apply INQ_lt ; omega). 
          ** hnf. destruct (archimedean_exists (IQR 1%nat * IQR (10 ^ m)%nat)). 
             rewrite !INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_l.
             auto with real.
             exists x0. split ; auto. destruct H3.
             rewrite <- mult_IQR in * ; apply le_IQR in H3 ; apply lt_IQR in H4 ;
             rewrite INQ_mult in * ; rewrite mult_1_l in * ; apply INQ_le in H3 ; apply INQ_lt in H4.
             assert (x0 = 10 ^ m)%nat. {omega. }
             subst.
             assert (m = m - 1 + 1)%nat. { omega. }
             rewrite H5. rewrite Nat.pow_add_r. 
             rewrite Nat.mul_mod ; auto.
             assert (10 ^ 1 mod 10 = 0)%nat. { auto. }
             rewrite H6. rewrite mult_0_r. auto.
        * split.
          ** rewrite <- IQR_R0. apply Rle_ge. apply IQR_le.
             rewrite <- INQ_Qeq_0. apply INQ_le. omega.
          ** apply IQR_lt. apply INQ_lt. omega. 
    - destruct IHn.
      destruct (H (S n)).
      + exists (x0).
        hnf in *.
        split ; intros.
        * split ; intros.
          ** split ; intros ; inversion H3.
             ***  assert (0 = l)%nat.
                  { apply (partial_functional_Dec_R (IQR x0) m ) ; auto.
                    apply H1. omega.
                  }
                  subst ; auto.
             *** apply H1 ; auto.
             *** subst. assert (l = 0)%nat. { apply (H0 (S n)) ; auto. }
                 subst. apply H1 ; auto.
             *** apply H1 ; auto. 
          ** apply H1 ; omega.
        * apply H1.
      + exists (x0 + INQ (1) / INQ (10 ^ S n))%Q.
        hnf in *. split ; intros.
        * split ; intros.
          ** split ; intros ; inversion H3.
             *** subst. assert (l = 1)%nat. 
                 {
                    destruct H1. clear H5.
                    specialize (H1 (S n)). destruct H1.
                    assert (S n > n)%nat. { omega. }
                    specialize (H5 H6). clear H1 H3 H6.
                    hnf in *.
                    destruct H5 , H1 , H1.
                    destruct H4 , H4 , H4.
                    rewrite <- mult_IQR in *. apply le_IQR in H4. apply lt_IQR in H7.
                    apply le_IQR in H1. apply lt_IQR in H5.
                    rewrite Qmult_plus_distr_l in *. 
                    assert (1%nat / (10 ^ S n)%nat * (10 ^ S n)%nat == INQ (1))%Q.
                    { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
                      rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
                    }
                    rewrite H8 in H7 , H4.
                    clear H8.
                    rewrite <- (Qplus_le_l _ _ (INQ(1))) in H1.
                    rewrite <- (Qplus_lt_l _ _ (INQ(1))) in H5.
                    rewrite INQ_plus in *.
                    assert (x1 + 1 = x2)%nat. 
                    {
                      apply NNPP. intro. apply nat_total_order in H8.
                      destruct H8 ; apply lt_le_S in H8 ; rewrite <- Nat.add_1_r in H8 ; apply INQ_le in H8 ;
                      apply (Qlt_irrefl (x0 * (10 ^ S n)%nat + 1%nat)).
                      - apply Qlt_le_trans with (INQ (x1+1+1)) ; auto.
                        apply Qle_trans with (INQ x2); auto. 
                      - apply Qlt_le_trans with (INQ (x2 + 1)) ; auto.
                        apply Qle_trans with (INQ (x1 + 1));  auto.
                    }
                    subst. rewrite Nat.add_mod ; auto.
                    rewrite <- H3. auto. 
                 }
                 subst. auto.
             *** subst.
                 apply H1 ; auto. hnf in *.
                 destruct H4 , H4 , H4.
                 destruct (archimedean_exists (IQR x0 * IQR (10 ^ m)%nat)) .
                 rewrite !INQ_IQR_INR. apply Rle_ge. apply Rmult_le_pos ; auto with real.
                 destruct H1. apply Rge_le. apply H8.
                 exists x2. split ; auto. destruct H8.
                 assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat) ((IQR x0 * IQR (10 ^ m)%nat))).
                 {  apply  (Same_Ipart_mult _ _ (10 ^ (n - m))).
                    - apply Max_powan_0 ; omega.
                    - apply Same_Ipart_comm.
                      rewrite plus_IQR.
                      assert (IQR (10 ^ m)%nat * INR (10 ^ (n - m)) == IQR (10 ^ n)%nat). 
                      {
                        assert (n = n - m + m)%nat. { omega. }
                        rewrite H10 at 2. rewrite Nat.pow_add_r. rewrite mult_comm.
                        rewrite !INQ_IQR_INR.
                        rewrite <- mult_INR. ring.
                      }
                      rewrite !Rmult_assoc. rewrite !H10.
                      apply Same_Ipart_pow10n. apply H1.
                      intro.
                      destruct H1. specialize (H1 m0). destruct H1.
                      destruct (classic (m0 <= n)%nat).
                      + specialize (H1 H13).
                        destruct (H m0).
                        * left. apply H1. auto.
                        * right. apply H1. auto.
                      + left. apply H12. omega.
                 }
                 destruct H10. destruct H10 , H11 , H12.
                 assert (x1 = x3)%nat. { apply (Ipart_unique (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)) ; split ; auto. }
                 assert (x2 = x3)%nat. { apply (Ipart_unique (IQR x0 * IQR (10 ^ m)%nat)) ; split ; auto. }
                 subst ; auto.
             *** subst. assert (l = 1)%nat. { apply (H0 (S n)) ; auto. }
                 subst. destruct H1. clear H5. 
                 specialize (H1 (S n)). destruct H1.
                 assert (S n > n)%nat. { omega. }
                 specialize (H5 H6). clear H1 H3 H6.
                 hnf in *.
                 destruct H5 , H1 , H1.
                 destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ S n)%nat)).
                 rewrite <- mult_IQR in *.
                 apply Rle_ge. rewrite <- IQR_R0.
                 apply IQR_le. rewrite Qmult_plus_distr_l.
                 apply le_IQR in H1. apply Qle_trans with x1.
                 rewrite <- INQ_Qeq_0. apply INQ_le. omega.
                 rewrite <- Qplus_0_r. apply Qle_Qplus_Qle ; auto.
                 unfold Qdiv. rewrite INQ_Qeq_1. rewrite Qmult_1_l.
                 rewrite Qmult_comm. rewrite Qmult_inv_r ; try (lra).
                 intro. apply (Qlt_irrefl 0). rewrite <- H6 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.  
                 exists x2. split ; auto.
                 destruct H6.
                 rewrite <- mult_IQR in *. apply le_IQR in H6. apply lt_IQR in H7.
                 apply le_IQR in H1. apply lt_IQR in H5.
                 rewrite Qmult_plus_distr_l in *. 
                 assert (1%nat / (10 ^ S n)%nat * (10 ^ S n)%nat == INQ (1))%Q.
                 { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
                   rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
                 }
                 rewrite H8 in H7 , H6.
                 clear H8.
                 rewrite <- (Qplus_le_l _ _ (INQ(1))) in H1.
                 rewrite <- (Qplus_lt_l _ _ (INQ(1))) in H5.
                 rewrite INQ_plus in *.
                 assert (x1 + 1 = x2)%nat. 
                 {
                    apply NNPP. intro. apply nat_total_order in H8.
                    destruct H8 ; apply lt_le_S in H8 ; rewrite <- Nat.add_1_r in H8 ; apply INQ_le in H8 ;
                    apply (Qlt_irrefl (x0 * (10 ^ S n)%nat + 1%nat)).
                    - apply Qlt_le_trans with (INQ (x1+1+1)) ; auto.
                      apply Qle_trans with (INQ x2); auto. 
                    - apply Qlt_le_trans with (INQ (x2 + 1)) ; auto.
                      apply Qle_trans with (INQ (x1 + 1));  auto.
                 }
                 subst. rewrite Nat.add_mod ; auto.
                 rewrite <- H3. auto. 
             *** subst.
                 apply H1 in H4; auto. hnf in *.
                 destruct H4 , H4 , H4.
                 destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)).
                 rewrite <- mult_IQR in *.
                 apply Rle_ge. rewrite <- IQR_R0.
                 apply IQR_le. rewrite Qmult_plus_distr_l.
                 apply le_IQR in H4. apply Qle_trans with x1.
                 rewrite <- INQ_Qeq_0. apply INQ_le. omega.
                 rewrite <- Qplus_0_r. apply Qle_Qplus_Qle ; auto.
                 unfold Qdiv. rewrite INQ_Qeq_1. rewrite Qmult_1_l.
                 rewrite Qmult_comm. apply Qmult_le_0_compat.
                 rewrite <- INQ_Qeq_0. apply INQ_le. omega.
                 apply Qinv_le_0_compat. rewrite <- INQ_Qeq_0. apply INQ_le. omega.
                 exists x2. split ; auto. destruct H8.
                 assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat) ((IQR x0 * IQR (10 ^ m)%nat))).
                 {  apply  (Same_Ipart_mult _ _ (10 ^ (n - m))).
                    - apply Max_powan_0 ; omega.
                    - apply Same_Ipart_comm.
                      rewrite plus_IQR.
                      assert (IQR (10 ^ m)%nat * INR (10 ^ (n - m))%nat == IQR (10 ^ n)%nat). 
                      {
                        assert (n = n - m + m)%nat. { omega. }
                        rewrite H10 at 2. rewrite Nat.pow_add_r. rewrite mult_comm.
                        rewrite !INQ_IQR_INR.
                        rewrite <- mult_INR. ring.
                      }
                      rewrite !Rmult_assoc. rewrite !H10.
                      apply Same_Ipart_pow10n. apply H1.
                      intro.
                      destruct H1. specialize (H1 m0). destruct H1.
                      destruct (classic (m0 <= n)%nat).
                      + specialize (H1 H13).
                        destruct (H m0).
                        * left. apply H1. auto.
                        * right. apply H1. auto.
                      + left. apply H12. omega.
                 }
                 destruct H10. destruct H10 , H11 , H12.
                 assert (x2 = x3)%nat. { apply (Ipart_unique (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)) ; split ; auto. }
                 assert (x1 = x3)%nat. { apply (Ipart_unique (IQR x0 * IQR (10 ^ m)%nat)) ; split ; auto. }
                 subst ; auto.
          ** apply Nat.lt_succ_l in H3 as goal. destruct H1. clear H4.
             specialize (H1 m). destruct H1. specialize (H4 goal).
             clear H1 goal H2.
             hnf in *.
             destruct H4 , H1 , H1.
             destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)).
             rewrite <- mult_IQR in *.
             apply Rle_ge. rewrite <- IQR_R0.
             apply IQR_le. rewrite Qmult_plus_distr_l.
             apply le_IQR in H1. apply Qle_trans with x1.
             rewrite <- INQ_Qeq_0. apply INQ_le. omega.
             rewrite <- Qplus_0_r. apply Qle_Qplus_Qle ; auto.
             unfold Qdiv. rewrite INQ_Qeq_1. rewrite Qmult_1_l.
             rewrite Qmult_comm. apply Qmult_le_0_compat.
             rewrite <- INQ_Qeq_0. apply INQ_le. omega.
             apply Qinv_le_0_compat. rewrite <- INQ_Qeq_0. apply INQ_le. omega.
             exists x2. split ; auto. destruct H5.
             rewrite <- mult_IQR in *. apply le_IQR in H5. apply lt_IQR in H6.
             apply le_IQR in H1. apply lt_IQR in H4.
             rewrite Qmult_plus_distr_l in *. 
             assert (1%nat / (10 ^ S n)%nat * (10 ^ m)%nat == INQ (10 ^ (m - S n)))%Q.
             {
               assert (m = m - S n + S n)%nat. { omega. }
               rewrite H7 at 1. rewrite Nat.pow_add_r. rewrite <- INQ_mult. 
               rewrite Qmult_comm. rewrite <- Qmult_assoc. unfold Qdiv.
               rewrite INQ_Qeq_1. field.
               intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
               rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
             }
             rewrite H7 in *. clear H7.
             rewrite <- (Qplus_le_l _ _ (INQ(10 ^ (m - S n)))) in H1.
             rewrite <- (Qplus_lt_l _ _ (INQ(10 ^ (m - S n)))) in H4.
             rewrite INQ_plus in *.
             assert (x1 + 1 + 10 ^ (m - S n) = x1 + 10 ^ (m - S n) + 1)%nat. { omega. }
             rewrite H7 in *. clear H7.
             assert (x1 + 10 ^ (m - S n) = x2)%nat. 
             {
               apply NNPP. intro. apply nat_total_order in H7.
               destruct H7 ; apply lt_le_S in H7 ; rewrite <- Nat.add_1_r in H7 ; apply INQ_le in H7 ;
               apply (Qlt_irrefl (x0 * (10 ^ m)%nat + (10 ^ (m - S n))%nat)).
               - apply Qlt_le_trans with (INQ (x1+ 10 ^ (m - S n) +1)) ; auto.
                 apply Qle_trans with (INQ x2); auto. 
               - apply Qlt_le_trans with (INQ (x2 + 1)) ; auto.
                 apply Qle_trans with (INQ (x1 + 10 ^ (m - S n)));  auto.
             }
             subst. rewrite Nat.add_mod ; auto.
             rewrite <- H2. rewrite Nat.add_0_l. rewrite Nat.mod_mod ; auto.
             assert (m - S n = m - S n - 1 + 1)%nat. { omega. }
             rewrite H7. clear H7. rewrite Nat.pow_add_r.
             rewrite Nat.mul_mod ; auto.
             assert (10 ^ 1 mod 10 = 0)%nat. { auto. }
             rewrite H7. rewrite mult_0_r. auto.
        * destruct H1 , H3.
          split. 
          ** apply Rge_le in H3. apply Rle_ge.
             apply Rle_trans with (IQR x0) ; auto.
             apply IQR_le. rewrite <- Qplus_0_r at 1.
             apply Qplus_le_r.  apply Qle_shift_div_l.
             *** rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
             *** rewrite Qmult_0_l. rewrite INQ_Qeq_1. lra.
          ** assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat)) (IQR x0)).
             {  apply  (Same_Ipart_mult _ _ (10 ^ n)).
                - apply Max_powan_0 ; omega.
                - apply Same_Ipart_comm.
                  rewrite plus_IQR.
                  rewrite <- INQ_IQR_INR.
                  apply Same_Ipart_pow10n. split ; auto.
                  intro.
                  specialize (H1 m). destruct H1.
                  destruct (classic (m <= n)%nat).
                  + specialize (H1 H6).
                    destruct (H m).
                    * left. apply H1. auto.
                    * right. apply H1. auto.
                  + left. apply H5. omega.
             }
             destruct H5 , H5 , H6 , H7.
             assert (x1 + 1 <= 10)%nat.
             {
                apply NNPP.
                intro. 
                apply not_le in H9.
                assert (x1 >= 10)%nat. {omega. }
                apply (Rlt_irrefl (IQR (INQ 10))).
                apply Rle_lt_trans with (IQR x0) ; auto.
                apply Rle_trans with (IQR x1) ; auto.
                apply IQR_le. apply INQ_le. auto.
             }
             apply Rlt_le_trans with (IQR (x1 + 1)%nat) ; auto.
             apply IQR_le. apply INQ_le. auto.
  Qed.
  
  Theorem partial_functional_NNP_T_NQP : forall (x : nat -> nat -> Prop) ,
                  InDec x -> forall (a : nat) (b1 b2 : Q), 
                              NNP_T_NQP x a b1 -> NNP_T_NQP x a b2 -> (b1 == b2)%Q.
  Proof.
    intros.
    hnf; intros.
    destruct H0. destruct H1.
    apply eq_IQR. apply Dec_R_eq ; auto.
    intros.
    specialize (H0 j). destruct H0.
    specialize (H1 j). destruct H1.
    destruct (classic (j <= a)%nat).
    - rewrite H0 ; auto. rewrite H1 ; auto. reflexivity.
    - apply Nat.nle_gt in H6. 
      specialize (H4 H6). specialize (H5 H6).
      split ; intros.
      + assert (m = 0)%nat. { apply (partial_functional_Dec_R (IQR b1) j) ; auto. }
        subst. auto.
      + assert (m = 0)%nat. { apply (partial_functional_Dec_R (IQR b2) j) ; auto. }
        subst. auto.
  Qed.
  
  Theorem is_function_NNP_T_NQP : forall (x : nat -> nat -> Prop) , InDec x -> is_function eq Qeq (NNP_T_NQP x).
  Proof.
    intros.
    repeat split ; intros ; try(subst; rewrite <- H1 in *; apply H2 ; auto) ; 
    try(subst; rewrite H1 in *; apply H2 ; auto) .
    - intro. apply image_defined_NNP_T_NQP. auto.
    - intro. apply partial_functional_NNP_T_NQP. auto.
  Qed.
  
  Theorem is_function_NQP_T_NRP : forall (x : nat -> Q -> Prop) , is_function eq Qeq x -> is_function eq Req (NQP_T_NRP x).
  Proof.
    intros. destruct H.
    destruct H0.
    repeat split ; hnf ; intros ; try (subst; rewrite H3 in *; auto).
    + destruct (H a). exists (IQR x0). exists x0. auto with real.
    + repeat destruct H2 , H3. rewrite <- H2 , <- H3. apply IQR_eq. 
      apply (H0 a); auto.
  Qed.
  
  Theorem Uncv_eqb_Uncv' : forall (x : nat -> Q -> Prop)(r : R) , is_function eq Qeq x -> Un_cv' x r <-> Un_cv (NQP_T_NRP x) r.
  Proof.
    split ; hnf in * ; intros.
    * repeat destruct H.
      split ; hnf in * ; intros.
      - apply is_function_NQP_T_NRP. apply H0.
      - destruct H0.
        specialize (H3 eps H2).
        destruct H3.
        exists x0. intros. destruct H5. destruct H5.
        specialize (H3 _ _ H4 H6).
        rewrite H5 in *. auto.
    * repeat destruct H0.
      split ; hnf; intros.
      - auto.
      - specialize (H1 eps H3).
        destruct H1.
        exists x0. intros.
        apply (H1 m) ; auto.
        exists q ; auto with real. 
  Qed.
  
  Definition mono_up_Q (X : nat -> Q -> Prop) : Prop := is_function eq Qeq X /\ mono_up (NQP_T_NRP X). 
  Definition mono_down_Q (X : nat -> Q -> Prop) : Prop := is_function eq Qeq X /\  mono_down (NQP_T_NRP X).
  Definition mono_Q (X : nat -> Q -> Prop) : Prop := mono_up_Q X \/ mono_down_Q X.
  Definition upper_bound_Q (X : nat -> Q -> Prop) (U : R) : Prop := upper_bound (NQP_T_NRP X) U.
  Definition Sup_Q (X : nat -> Q -> Prop) (sup : R) : Prop := Sup (NQP_T_NRP X) sup.
  Definition lower_bound_Q (X : nat -> Q -> Prop) (L : R) : Prop := lower_bound (NQP_T_NRP X) L.
  Definition Inf_Q (X : nat -> Q -> Prop) (inf : R) : Prop := Inf (NQP_T_NRP X) inf.
  Definition bound_Q (X : nat -> Q -> Prop) : Prop := bound (NQP_T_NRP X).

  Theorem Sup_pro_Q : forall (X : nat -> Q -> Prop) (sup : R) , is_function eq Qeq X -> Sup_Q X sup -> forall y : R , (y < sup -> 
                              (exists n : nat , forall q : Q , X n q -> ( IQR q <= sup /\ y < IQR q))).
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
    hnf in H6.
    destruct H6.
    destruct H6.
    destruct H3.
    assert (x == x0)%Q.
    { destruct H4. apply (H4 n) ; auto.  apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply (H5 n) ; auto.
      hnf. exists x ; split ; auto with real.  
    - apply Rnot_gt_le. apply IQR_eq in H8. rewrite <- H6 , H8. auto.  
  Qed.
  
  Theorem Inf_pro_Q : forall (X : nat -> Q -> Prop) (inf : R) , is_function eq Qeq X -> Inf_Q X inf -> forall y : R , (y > inf -> 
                              (exists n : nat , forall q : Q , X n q -> (IQR q >= inf /\ y > IQR q))).
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
    destruct H3.
    destruct H6. destruct H6.
    assert (x0 == x)%Q.
    { destruct H4. apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply Rle_ge. apply (H5 n); auto.
      hnf. exists x0 ; split ; auto with real. 
    - apply Rnot_gt_le. apply IQR_eq in H8. rewrite <- H6 , H8. auto.
  Qed.

  Theorem upper_bound_T_lower_bound_Q : forall (X P : nat -> Q -> Prop) , is_function eq Qeq X -> is_function eq Qeq P
                                                                     -> (forall n r , X n r <-> P n (-r)%Q) 
                                                                      -> forall r , upper_bound_Q X r <-> lower_bound_Q P (-r).
  Proof.
    intros.
    split ; intros.
    - hnf. intros.
      destruct H3. destruct H3.
      specialize (H1 n (-x)%Q).
      assert (IQR (- - x) == - - q).
      { rewrite Ropp_involutive. rewrite <- H3. apply IQR_eq. lra. }
      destruct (H2 n (IQR (-x))). 
      + hnf. exists (-x)%Q. split ; auto with real.
        apply H1. destruct H0. 
        rewrite <- H3 in H5. rewrite Ropp_involutive in H5. 
        apply eq_IQR in H5. destruct H6.
        specialize (H7 n n).
        apply H7 with x ; auto.
      + rewrite opp_IQR in H6. rewrite H3 in H6.
        apply Rlt_le in H6.
        rewrite <- (Ropp_involutive q).
        apply Rle_opp_eqb. rewrite Ropp_involutive. auto.
      + rewrite <- H6. rewrite <- opp_IQR. rewrite <- H3.
        apply IQR_le. lra.
    - hnf. intros.
      destruct H3. destruct H3.
      specialize (H1 n x).
      rewrite H1 in H4.
      assert (NQP_T_NRP P n (IQR (- x))).
      { hnf. exists (-x)%Q. auto with real. }
      specialize (H2 n (IQR (-x)) H5).
      rewrite opp_IQR in H2.
      rewrite H3 in H2. auto with real.
  Qed.
  
  Theorem upper_bound_exists_Sup_Q : forall (X : nat -> Q -> Prop) , is_function eq Qeq X -> (exists r : R , upper_bound_Q X r) ->
                                          (exists sup : R , Sup_Q X sup).
  Proof.
    intros.
    assert (exists sup : R , Sup (NQP_T_NRP X) sup).
    {
      destruct H.
      apply upper_bound_exists_Sup.
      - repeat split; hnf ; intros.
        + destruct (H a). exists (IQR x). exists x ; auto with real.
        + repeat destruct H2 , H3. rewrite <- H2 , <- H3. apply IQR_eq. destruct H1. apply (H1 a) ; auto.
        + subst. rewrite H3 in *. auto.
        + subst. rewrite H3 in *. auto.
      - destruct H0.
        exists x.
        hnf ; intros.
        repeat destruct H2.
        apply (H0 n). exists x0 ; auto.
    }
    auto.
  Qed.
  
  Theorem lower_bound_exists_Inf_Q : forall (X : nat -> Q -> Prop) , is_function eq Qeq X -> (exists r : R , lower_bound_Q X r) ->
                                          (exists inf : R , Inf_Q X inf).
  Proof.
   intros.
    assert (exists inf : R , Inf (NQP_T_NRP X) inf).
    {
      destruct H.
      apply lower_bound_exists_Inf.
      - repeat split; hnf ; intros.
        + destruct (H a). exists (IQR x). exists x ; auto with real.
        + repeat destruct H2 , H3. rewrite <- H2 , <- H3. apply IQR_eq. destruct H1. apply (H1 a) ; auto.
        + subst. rewrite H3 in *. auto.
        + subst. rewrite H3 in *. auto.
      - destruct H0.
        exists x.
        hnf ; intros.
        repeat destruct H2.
        apply (H0 n). exists x0 ; auto.
    }
    auto.
  Qed.
  
  Theorem Sup_unique_Q : forall (X : nat -> Q -> Prop) (r1 r2 : R), Sup_Q X r1 -> Sup_Q X r2 -> r1 == r2.
  Proof. 
    intros.
    unfold Sup_Q in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with real.
  Qed.

  Theorem Inf_unique_Q : forall (X : nat -> Q -> Prop) (r1 r2 : R), Inf_Q X r1 -> Inf_Q X r2 -> r1 == r2.
  Proof.
    intros.
    unfold Inf_Q in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with real.
  Qed.

  Theorem mono_up_upper_bound_seq_has_limit_Q : forall (X : nat -> Q -> Prop) , mono_up_Q X -> (exists r : R , upper_bound_Q X r) -> exists r : R ,Un_cv' X r.
  Proof. 
    intros. destruct H.
    pose proof mono_up_upper_bound_seq_has_limit (NQP_T_NRP X) H1 H0.
    destruct H2.
    exists x.
    apply Uncv_eqb_Uncv' ; auto.
  Qed. 
  
  Theorem mono_up_limit_sup_Q : forall (X : nat -> Q -> Prop) , mono_up_Q X -> (exists r : R , upper_bound_Q X r) -> forall r : R , Un_cv' X r -> Sup_Q X r.
  Proof.
    intros. 
    destruct H.
    apply (mono_up_limit_sup (NQP_T_NRP X) H2 H0 r).
    apply Uncv_eqb_Uncv'; auto.
  Qed.
  
  Theorem mono_down_lower_bound_seq_has_limit_Q : forall (X : nat -> Q -> Prop) , mono_down_Q X -> (exists r : R , lower_bound_Q X r) -> exists r : R , Un_cv' X r.
  Proof.
    intros. destruct H.
    pose proof mono_down_lower_bound_seq_has_limit (NQP_T_NRP X) H1 H0.
    destruct H2.
    exists x.
    apply Uncv_eqb_Uncv' ; auto.
  Qed. 

  Theorem mono_bound_seq_has_limit_Q : forall (X : nat -> Q -> Prop) , bound_Q X -> mono_Q X -> exists r : R , Un_cv' X r.
  Proof.
    intros.
    unfold bound_Q in *.
    destruct H.
    destruct H0.
    - apply mono_up_upper_bound_seq_has_limit_Q ; auto.
    - apply mono_down_lower_bound_seq_has_limit_Q ; auto.
  Qed.
  
  Theorem Dec_R2_bound : forall (x : nat -> nat -> Prop) , InDec x -> upper_bound (NQP_T_NRP (NNP_T_NQP x)) 2.
  Proof.
    intros. hnf. intros.
    destruct H. destruct H0. destruct H0. subst.
    destruct H2.
    left.
    apply Dec_R_lt.
    * rewrite H0 in *. apply H3.
    * split.
      - apply Rle_ge. apply Rlt_le. auto with real.
      - apply R2_Rlt_R10.
    * exists O.
      split ; intros.
      - pose proof Two_Dec.
        assert (m2 = 2 %nat). { apply (partial_functional_Dec_R 2 O) ; auto. }
        subst.
        specialize (H2 O). destruct H2.
        assert (0 <= n)%nat. { omega. }
        specialize (H2 H8). rewrite <- H0 in *. 
        apply H2 in H4.
        destruct (H O).
        + assert (m1 = 0)%nat. { apply (H1 O) ; auto. }
          subst. auto.
        + assert (m1 = 1)%nat. { apply (H1 O) ; auto. }
          subst. auto.
      - omega.
  Qed.
   
  Theorem Dec_upper_bound : forall (D : Dec) , exists r : R , upper_bound_Q (NNP_T_NQP (proj1_sig D)) r.
  Proof.
    destruct D.
    simpl.
    exists 2.
    apply Dec_R2_bound. 
    auto.
  Qed.
  
  Theorem Dec_mono_up : forall (D : Dec) , mono_up_Q (NNP_T_NQP (proj1_sig D)).
  Proof.
    destruct D , i.
    assert (forall n1 x1 x2 , (NNP_T_NQP x) n1 x1 -> (NNP_T_NQP x) n1 x2 -> (x1 == x2)%Q).
    {
      intros.
      apply eq_IQR. apply Dec_R_eq ; intros.
      - apply H.
      - apply H0.
      - destruct H , H0. clear H1 H2. destruct (H j) , (H0 j).
        destruct (Nat.le_gt_cases j n1).
        * rewrite (H1 H5). rewrite (H3 H5). reflexivity.
        * specialize (H2 H5).
          specialize (H4 H5).
          destruct (Nat.eq_dec m 0) ; subst ; split ; intros ; auto.
          + exfalso. apply n. apply (partial_functional_Dec_R (IQR x1) j) ; auto.
          + exfalso. apply n. apply (partial_functional_Dec_R (IQR x2) j) ; auto.
    }
    split ; intros.
    - repeat split ; hnf ; simpl in * ; intros ; try (subst ; apply IQR_eq in H1 ; rewrite <- H1 in *;
        apply H2 ; auto) ; try (subst ; apply IQR_eq in H1 ; rewrite H1 in * ; apply H2 ; auto).
      + assert (exists q , (NNP_T_NQP x) a q). { apply image_defined_NNP_T_NQP . split ; auto. }
        destruct H0. exists x0. auto.
      + repeat destruct H0 , H1.
        apply (H a) ; hnf ; simpl in * ; auto with real. 
    - simpl in *.
      split ; intros.
      + apply is_function_NQP_T_NRP. apply is_function_NNP_T_NQP. split ; auto.
      + repeat destruct H0 , H1.
        apply Rle_ge. rewrite <- H0 , <- H1. clear H0 H1. 
        apply IQR_le.
        destruct (classic (x1 <= x0)%Q) ; auto.
        apply Qnot_le_lt in H0.
        exfalso.
        apply IQR_lt in H0.
        apply Dec_R_lt in H0.
        repeat destruct H0.
        destruct H3 , H4. clear H5 H6.
        specialize (H3 x2).
        destruct H3.
        specialize (H4 x2).
        destruct H4.
        destruct (o x2) ; destruct (classic (x2 <= n1)%nat).
        ++ specialize (H4 H8 O).
          pose proof (le_trans x2 n1 n H8 H2).
          specialize (H3 H9 O).
          apply (lt_irrefl O).
          apply H0.
          * rewrite H3 ; auto.
          * rewrite H4 ; auto.
        ++ apply not_le in H8.
          specialize (H6 H8).
          clear H4.
          destruct (classic (x2 <= n)%nat).
          * specialize (H3 H4 O).
            rewrite <- H3 in H7.
            specialize (H0 O 0%nat H7 H6).
            inversion H0.
          * apply not_le in H4.
            specialize (H5 H4).
            apply (lt_irrefl O).
            apply H0 ; auto.
        ++ specialize (H4 H8 1%nat).
          pose proof (le_trans x2 n1 n H8 H2).
          specialize (H3 H9 1%nat).
          apply (lt_irrefl 1%nat).
          apply H0.
          * rewrite H3 ; auto.
          * rewrite H4 ; auto.
        ++ apply not_le in H8.
          specialize (H6 H8).
          clear H4.
          destruct (classic (x2 <= n)%nat).
          * specialize (H3 H4 1%nat).
            rewrite <- H3 in H7.
            specialize (H0 1%nat 0%nat H7 H6).
            inversion H0.
          * apply not_le in H4.
            specialize (H5 H4).
            apply (lt_irrefl O).
            apply H0 ; auto.
        ++ apply H3.
        ++ apply H4.
  Qed.

  Theorem Un_cv'_Dec : forall (x : nat -> nat -> Prop) (r : R) , InDec x -> Un_cv' (NNP_T_NQP x) r ->
          forall (n m : nat) , Dec_R r n m <-> x n m.
  Proof.
    intros.
    assert (mono_up_Q (NNP_T_NQP x)). { apply (Dec_mono_up (NNP_Dec x H)). }
    assert (exists r : R , upper_bound_Q (NNP_T_NQP x) r). { apply (Dec_upper_bound (NNP_Dec x H)). }
    pose proof mono_up_limit_sup_Q (NNP_T_NQP x) H1 H2 r H0.
    clear H2. 
    destruct H0 , H0.
    assert (IQR (INQ (1) / INQ (10 ^ (S n))) > R0).
    { rewrite <- IQR_R0. apply IQR_lt. apply Qlt_shift_div_l.
      - rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
      - rewrite Qmult_0_l. rewrite INQ_Qeq_1. lra.
    }
    specialize (H2 (IQR (INQ (1) / INQ (10 ^ (S n)))) H5).
    clear H5. destruct H2.
    remember (max x0 (S n)) as p.
    destruct (H0 p).
    assert (p >= x0)%nat. { subst. apply Nat.le_max_l. }
    specialize (H2 p x1 H6 H5).
    destruct H1 , H3.
    hnf in H8.
    assert (IQR x1 <= r). { apply (H8 p). exists x1. auto with real. }
    apply Rle_ge in H9 as goal.
    rewrite Rle_neg_eqb in goal.
    apply Rabs_neg in goal.
    rewrite Ropp_minus_distr' in goal.
    rewrite goal in H2. clear goal.
    apply Rlt_Rminus_Rplus in H2.
    destruct H5. pose proof H10 as pH1. clear H10.
    assert (pH : 0 <= r). { apply Rle_trans with (IQR x1) ; auto. apply Rge_le. apply pH1. }
    pose proof (H5 n).
    pose proof (H5 (S n)).
    destruct H10 , H11.
    assert (S n <= p)%nat. {subst . apply Nat.le_max_r. } 
    assert (n <= p)%nat. { omega. }
    specialize (H10 H15). specialize (H11 H14). 
    clear H14 H15 H13 H12 H3 H8 H7.
    destruct H. rewrite <- plus_IQR in *.
    destruct (archimedean_exists (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat)).
    apply Rle_ge. apply Rmult_le_pos.
    apply Rle_trans with r ; auto with real.
    rewrite INQ_IQR_INR. auto with real.
    destruct H7 .
    destruct (archimedean_exists (IQR x1 * IQR (10 ^ n)%nat)). 
    apply Rle_ge. apply Rmult_le_pos.
    apply Rge_le. apply pH1. rewrite INQ_IQR_INR. auto with real.
    destruct H12.
    assert (Same_Ipart (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat) ((IQR x1 * IQR (10 ^ n)%nat))).
    {
       rewrite plus_IQR.
       apply Same_Ipart_comm.
       apply Same_Ipart_pow10n. auto.
       intro. specialize (H5 m0). destruct H5.
       destruct (classic (m0 <= p)%nat).
       + specialize (H5 H15).
         destruct (H m0).
         * left. apply H5. auto.
         * right. apply H5. auto.
      + left. apply H14. omega.
    }
    destruct H14.
    rewrite <- H10.
    destruct H14 , H15 ,  H16.
    assert (IQR x4 <= r * IQR (10 ^ n)%nat).
    {
      apply Rle_trans with (IQR x1 * IQR (10 ^ n)%nat) ; auto.
      apply Rmult_le_r ; auto.
      rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0.
      apply INQ_lt. apply Max_powan_0. omega.
    }
    assert (r * IQR(10 ^ n)%nat < IQR (x4 + 1)%nat).
    {
      apply Rlt_trans with (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat) ; auto.
      apply Rmult_lt_r ; auto.
      rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0.
      apply INQ_lt. apply Max_powan_0. omega.
    }
    clear H0 H4 H2 H1 H5 H9 H10 H11 H7 H8 H12 H13.
    split ; intros ; hnf in *  ; destruct H0 , H0, H0.
    - destruct (archimedean_exists (IQR x1 * IQR (10 ^ n)%nat)). 
      apply Rle_ge. apply Rmult_le_pos.
      apply Rge_le. apply pH1. rewrite INQ_IQR_INR. auto with real.
      exists x6. split ; auto.
      destruct H4.
      assert (x4 = x5)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; split ; auto. }
      assert (x4 = x6)%nat. { apply (Ipart_unique (IQR x1 * IQR (10 ^ n)%nat)) ; split ; auto. }
      subst ; auto.
    - destruct (archimedean_exists (r * IQR (10 ^ n)%nat)). 
      apply Rle_ge. apply Rmult_le_pos ; auto with real.
      rewrite INQ_IQR_INR. auto with real.
      exists x6. split ; auto.
      destruct H4.
      assert (x4 = x6)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; split ;auto. }
      assert (x4 = x5)%nat. { apply (Ipart_unique (IQR x1 * IQR (10 ^ n)%nat)) ; split ; auto. }
      subst ; auto.
  Qed.
  
  Theorem image_defined_Dec_r : image_defined Dec_r.
  Proof. 
    unfold image_defined.
    intros.
    assert (mono_up_Q (NNP_T_NQP (proj1_sig a))).
    { apply Dec_mono_up. }
    assert (exists r : R , upper_bound_Q (NNP_T_NQP (proj1_sig a)) r).
    { apply Dec_upper_bound. }
    repeat destruct a.
    set (NNP_T_NQP x).
    pose proof mono_up_upper_bound_seq_has_limit_Q P H H0.
    destruct H1.
    exists x0.
    split ; intros.
    - apply Un_cv'_Dec ;  auto. 
    - simpl in *.
      pose proof mono_up_limit_sup_Q P H H0 _ H1.
      destruct H2.
      assert (upper_bound (NQP_T_NRP P) 2).
      {
        apply Dec_R2_bound. auto.
      }
      split .
      + subst P.
        destruct H1 , H1 , (H1 O).
        assert ((NQP_T_NRP (NNP_T_NQP x)) O (IQR x1)).
        {
          exists x1. auto with real.
        }
        specialize (H3 O (IQR x1) H8).
        apply Rle_ge.
        apply Rle_trans with (IQR x1) ; auto.
        destruct H7 , H9.
        apply Rge_le. auto.
     + apply Rle_lt_trans with 2.
       * apply Rge_le. apply H2. auto.
       * apply R2_Rlt_R10.
  Qed.

  Theorem partial_functional_Dec_r : partial_functional Req Dec_r.
  Proof. 
    unfold partial_functional ,  Dec_r .
    intros.
    destruct H , H0.
    apply Dec_R_eq ; intros ; auto.
    pose proof H j m.
    pose proof H0 j m.
    tauto.
  Qed.

  Theorem injective_Dec_r : injective eq Dec_r.
  Proof. 
    hnf in *. intros.
    hnf in *.
    destruct a1 , a2.
    destruct H , H0.
    assert (x = x0).
    { apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      apply propositional_extensionality.
      pose proof H x1 x2.
      pose proof H0 x1 x2.
      rewrite H3 in H4.
      auto.
    }
    subst.
    assert (i = i0). { apply proof_irrelevance. }
    subst.
    auto.
  Qed.
  
  Theorem Equiv_R_DecR : Countable R Req -> Countable Dec eq.
  Proof.
    intros.
    destruct X.
    pose proof image_defined_Dec_r.
    pose proof partial_functional_Dec_r.
    pose proof injective_Dec_r.
    set (fun (D : Dec) (n : nat) => exists r : R , Dec_r D r /\ inj_R r n).
    exists P ; subst P ; hnf in *; intros.
    - hnf. intros. subst. reflexivity.
    - destruct (H a).
      destruct (im_inj x).
      exists x0 , x. split ; auto.
    - destruct H2 , H3. destruct H2 , H3.
      assert (x == x0).  { apply (H0 a); auto. }
      specialize (wd_inj _ _ H6). apply (wd_inj b1 b1) in H4 ; auto.
      apply (pf_inj x0) ; auto.
    -  destruct H2 , H3. destruct H2 , H3.
       assert (x == x0).  { apply (in_inj _ _ b) ; auto. }
       subst .
       apply (H1 _ _ x0) ; auto.
       rewrite <- H6. auto.
  Qed.
  
  Theorem UnCountable_DecR : Countable Dec eq -> False.
  Proof.
    intros.
    destruct X.
    set (fun (n m : nat) => ((m = 0)%nat /\ 
          ((exists D : Dec , inj_R D n /\ forall D : Dec , inj_R D n -> ~ (proj1_sig D n 0%nat)) \/ 
        (forall D : Dec , ~ inj_R D n)))
      \/ ((exists D : Dec , inj_R D n /\ forall D : Dec , inj_R D n -> proj1_sig D n 0%nat) /\ (m = 1)%nat)).
    assert (InDec P).
    {
      subst P.
      split ; intros.
      * destruct (classic (exists D : Dec , inj_R D x)).
        - destruct H.
          destruct x0 ,i , (o x) ;
          remember (exist (fun R : nat -> nat -> Prop => InDec R) x0
         (conj o e)) as p.
          + right. right. split ; auto.   
            exists p. split ; intros ; auto.
            specialize (in_inj p D x H H1).
            subst. auto.   
          + left. left. split ; auto.
            left. exists p. split ; intros ; auto.
            unfold not. intros.
            specialize (in_inj p D x H H1).
            subst.
            assert ((0 = 1)%nat). { apply (e x) ; auto. }
            inversion H3.
        - left. left. split ; auto.
          right. 
          apply not_ex_all_not. auto.
      * repeat destruct H , H0 ;  subst ; auto ; exfalso.
        + destruct H1 , H.
          ++ destruct H0 , H0.
             assert (x0 = x1 % nat). { apply (in_inj x0 x1 x); auto. }
             subst. 
             pose proof H1 x1 H.
             pose proof H2 x1 H.
             auto.
          ++ apply (H0 x0). auto. 
        + destruct H , H2.
          ++ destruct H1 , H1.
             assert (x0 = x1 % nat). { apply (in_inj x0 x1 x); auto. }
             subst.
             pose proof H0 x1 H.
             pose proof H2 x1 H.
             auto.
          ++ apply (H1 x0). auto.
   }
   set (NNP_Dec P H).
   destruct (im_inj d).
   assert (P x 0%nat \/ P x 1%nat).
   {
     intros.
     subst P.
     destruct (classic (proj1_sig d x 0%nat)).
     - right. right. split ; auto.
       exists d. split ; auto.
       intros.
       assert (D = d). { apply (in_inj _ _ x) ; auto. }
       subst ; auto.
     - left. left. split ; auto. left.
       exists d. split ; auto.
       intros.
       assert (D = d). { apply (in_inj _ _ x) ; auto. }
       subst ; auto.
   }
   assert (forall m : nat ,P x m%nat -> proj1_sig d x m%nat). { auto. }
   destruct H1.
   - pose proof H2 0%nat H1. clear H2. 
     repeat destruct H1.
     + destruct H2.
       * destruct H1,H1.
         assert (x0 = d). { apply (in_inj _ _ x) ; auto. }
         subst.
         pose proof H2 d H1.
         auto.
       * apply (H1 d). auto.
     + inversion H2.
  - pose proof H2 1%nat H1. clear H2. 
    destruct H1.
    + destruct H1.  inversion H1. 
    + repeat destruct H1.
      assert (x0 = d). { apply (in_inj _ _ x) ; auto. }
      subst.
      pose proof H4 _ H1.
      destruct H.
      assert ((1 = 0) % nat).
      { apply (e x) ; auto. }
      inversion H.
  Qed.
  
  Theorem UnCountable_R : Countable R Req -> False.
  Proof.
    intros.
    apply UnCountable_DecR.
    apply Equiv_R_DecR ; auto.
  Qed.
  
  Theorem Dec_Q : forall (q : Q) (n:nat) , (R0 <= IQR q) -> {Dec_R (IQR q) n 0} + {~Dec_R (IQR q) n 0}.
  Proof.
    intros.
    set (Z.to_nat (Qfloor (q * INQ (10 ^ n)))).
    assert (archimedean n0 (IQR q * IQR (10 ^ n)%nat)).
    {
      rewrite <- mult_IQR.
      remember (q * (10 ^ n)%nat)%Q as q0.
      assert (q0 < inject_Z (Qfloor q0 + 1))%Q. { apply Qlt_floor. }
      split.
      + apply IQR_le. subst n0.
        unfold INQ. rewrite Z2Nat.id.
        apply Qfloor_le.
        assert (Qfloor 0%Q = 0)%Z. { auto. }
        rewrite <- H1.
        apply Qfloor_resp_le.
        rewrite <- IQR_R0 in H. apply le_IQR in H.
        apply Qle_trans with q ; auto. 
        subst. rewrite <- Qmult_1_r at 1.
        apply Qle_lt_or_eq in H. destruct H.
        * apply Qmult_le_l ; auto.
           rewrite <- INQ_Qeq_1. apply INQ_le. apply Max_powan_0. omega.
        * rewrite <- H. lra.
      + apply IQR_lt. apply Qlt_le_trans with (inject_Z (Qfloor q0 + 1)) ; auto.
        subst n0.
        apply Qle_trans with (Z.to_nat (Qfloor q0 + 1)).
        * apply Z_to_nat_le.
        * rewrite Z2Nat.inj_add ; try (omega).
          apply INQ_le. auto.
          assert (Qfloor 0%Q = 0)%Z. { auto. }
          rewrite <- H1.
          apply Qfloor_resp_le.
          rewrite <- IQR_R0 in H. apply le_IQR in H.
          apply Qle_trans with q ; auto. 
          subst. rewrite <- Qmult_1_r at 1.
          apply Qle_lt_or_eq in H. destruct H.
          - apply Qmult_le_l ; auto.
             rewrite <- INQ_Qeq_1. apply INQ_le. apply Max_powan_0. omega.
          - rewrite <- H. lra.
    }
    destruct (n0 mod 10) eqn : En.
    - left. exists n0.
      split ; auto.
    - right. intro.
      destruct H1 , H1 , H1 , H0.
      rewrite <- mult_IQR in *.
      assert (n0 = x). { apply (Ipart_unique (IQR (q * (10 ^ n)%nat))) ; split ; auto. }
      subst.
      rewrite En in H2.
      inversion H2.
  Qed.
  
  Theorem Dec_Q_nine : forall (q : Q) (n:nat) , (R0 <= IQR q) -> {Dec_R (IQR q) n 9} + {~Dec_R (IQR q) n 9}.
  Proof.
    intros.
    set (Z.to_nat (Qfloor (q * INQ (10 ^ n)))).
    assert (archimedean n0 (IQR q * IQR (10 ^ n)%nat)).
    {
      rewrite <- mult_IQR.
      remember (q * (10 ^ n)%nat)%Q as q0.
      assert (q0 < inject_Z (Qfloor q0 + 1))%Q. { apply Qlt_floor. }
      split.
      + apply IQR_le. subst n0.
        unfold INQ. rewrite Z2Nat.id.
        apply Qfloor_le.
        assert (Qfloor 0%Q = 0)%Z. { auto. }
        rewrite <- H1.
        apply Qfloor_resp_le.
        rewrite <- IQR_R0 in H. apply le_IQR in H.
        apply Qle_trans with q ; auto. 
        subst. rewrite <- Qmult_1_r at 1.
        apply Qle_lt_or_eq in H. destruct H.
        * apply Qmult_le_l ; auto.
           rewrite <- INQ_Qeq_1. apply INQ_le. apply Max_powan_0. omega.
        * rewrite <- H. lra.
      + apply IQR_lt. apply Qlt_le_trans with (inject_Z (Qfloor q0 + 1)) ; auto.
        subst n0.
        apply Qle_trans with (Z.to_nat (Qfloor q0 + 1)).
        * apply Z_to_nat_le.
        * rewrite Z2Nat.inj_add ; try (omega).
          apply INQ_le. auto.
          assert (Qfloor 0%Q = 0)%Z. { auto. }
          rewrite <- H1.
          apply Qfloor_resp_le.
          rewrite <- IQR_R0 in H. apply le_IQR in H.
          apply Qle_trans with q ; auto. 
          subst. rewrite <- Qmult_1_r at 1.
          apply Qle_lt_or_eq in H. destruct H.
          - apply Qmult_le_l ; auto.
             rewrite <- INQ_Qeq_1. apply INQ_le. apply Max_powan_0. omega.
          - rewrite <- H. lra.
    }
    destruct (Nat.eq_dec (n0 mod 10) 9).
    - left. exists n0.
      split ; auto.
    - right. intro.
      destruct H1 , H1 , H1 , H0.
      rewrite <- mult_IQR in *.
      assert (n0 = x). { apply (Ipart_unique (IQR (q * (10 ^ n)%nat))) ; split; auto. }
      subst.
      rewrite <- H2 in n1. omega.
  Qed.

  Theorem Dec_R_nine_same : forall (r : R)(n : nat) , r >=0 -> ~ Dec_R r (S n) 9 -> Same_Ipart_n r n.
  Proof.
    intros r n pH. intros.
    destruct (image_Defined_Dec_R r (S n)). auto.
    assert (x <> 9)%nat. { intro. subst. auto. }
    clear H.
    assert (x < 10)%nat. { apply (Dec_R_pro1 r (S n)) ; auto. }
    assert (x < 9)%nat. { omega. }
    clear H H1.
    destruct H0 , H , H.
    destruct (archimedean_exists (r * IQR (10 ^ n)%nat)). 
    apply Rle_ge. apply Rmult_le_pos.
    apply Rge_le. auto. rewrite INQ_IQR_INR. auto with real. 
    destruct H3.
    exists x1.
    rewrite <- !INQ_IQR_INR in *.
    repeat split ; auto .
    - rewrite Rmult_plus_distr_r.
      apply Rle_trans with (r * IQR (10 ^ n)%nat) ; auto.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat ; auto with real. unfold Rdiv.
      rewrite !INQ_IQR_INR. rewrite INR_R1. rewrite Rmult_1_l.
      apply Rmult_le_pos ; auto with real.
      apply Rlt_le. apply Rinv_0_lt_compat. auto with real.
      rewrite <- INR_R0. apply lt_INR. apply Max_powan_0. omega.
    - symmetry in H0.
      apply mod_exists in H0 ; auto.
      destruct H0.
      assert (forall n : nat , IQR (10 ^ n)%nat > R0).
      { intros. rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
      assert (forall n : nat , ~ (10 ^ n)%nat == 0)%Q.
      { intros. intro. rewrite <- INQ_Qeq_0 in H6.
        apply Qeq_INQ_eq in H6. apply (lt_irrefl O). rewrite <- H6 at 2. apply Max_powan_0. omega. }
      apply Rmult_le_r with (r3 := IQR (10 ^ 1)%nat) in H3 ; auto.
      apply Rmult_lt_r with (r3 := IQR (10 ^ 1)%nat) in H4 ; auto.
      apply Rmult_lt_r with (r3 := IQR (10 ^ 1)%nat) ; auto.
      assert (IQR (10 ^ n)%nat * IQR (10 ^ 1)%nat == IQR (10 ^ (S n))%nat).
      { apply NNPP. intro.
        apply Rdichotomy in H7.
        destruct H7 ; rewrite <- mult_IQR in H7 ; apply lt_IQR in H7 ; rewrite INQ_mult in H7 ; apply INQ_lt in H7 ; 
        simpl in H7 ; rewrite mult_comm in H7 ; rewrite <- Nat.pow_succ_r' in H7 ; apply lt_irrefl in H7 ; auto.
      }
      rewrite Rmult_assoc in *.
      rewrite H7 in *. rewrite Rmult_plus_distr_r.
      clear H7.
      assert (IQR 1%nat / IQR (10 ^ S n)%nat * IQR (10 ^ S n)%nat == IQR 1%nat).
      {
        field. rewrite INQ_IQR_INR.
        apply Rgt_not_eq. rewrite <- INR_R0. apply lt_INR. apply Max_powan_0. omega.
      }
      rewrite H7 in *. clear H7.
      rewrite <- mult_IQR in *.
      subst x0.
      assert (x1 * (10 ^ 1)%nat < 10 * x2 + x + 1)%nat.
      { apply INQ_lt. rewrite <- INQ_mult. apply lt_IQR. apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto. }
      assert (10 * x2 + x < (x1 + 1) * (10 ^ 1))%nat.
      { apply INQ_lt. rewrite <- INQ_mult. apply lt_IQR. apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto. }
      assert (10 ^ 1 = 10)%nat. { auto. }
      rewrite H8 in *. clear H8.
      assert (x2 = x1)%nat. { omega. }
      apply Rplus_lt_compat_r with (r := IQR 1%nat) in H1.
      apply Rlt_le_trans with (IQR (10 * x2 + x + 1)%nat + IQR 1%nat) ; auto.
      rewrite <- plus_IQR.
      apply IQR_le. rewrite INQ_plus. rewrite INQ_mult. apply INQ_le. omega.
  Qed.

  Theorem Dec_R_eps_same : forall (r1 r2 : R)(n : nat) ,
                                      Rabs (r1 - r2) < IQR 1 / IQR (10 ^ n)%nat ->
                                     Same_Ipart_n r1 (n - 1) -> Same_Ipart_n r2 (n - 1) -> forall m : nat , (m < n)%nat -> 
                                     (forall l : nat , Dec_R r1 m l <-> Dec_R r2 m l).
  Proof.
    intros.
    apply Rabs_tri in H.
    destruct H.
    apply Rlt_Rminus_Rplus in H3.
    rewrite Rplus_comm in H3.
    hnf in H0.
    assert (forall m : nat , IQR (10 ^ m)%nat > R0). 
    { intros. rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
    assert (forall m : nat , (m < n)%nat -> (IQR (10 ^ m)%nat * INR (10 ^ (n - 1 - m))%nat) == IQR (10 ^ (n - 1))%nat).
    { intros.
      assert (n - 1 = n - 1 - m0 + m0)%nat. { omega. }
      rewrite !INQ_IQR_INR. rewrite <- mult_INR.
      rewrite <- Nat.pow_add_r.
      rewrite plus_comm. rewrite H6 at 2. auto with real.
    }
    assert (~ INQ (10 ^ S (n - 1)) == 0)%Q.
    { intro.
      apply (Qlt_irrefl 0%Q).
      rewrite <- H6 at 2.
      rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
    }
    hnf in H1.
    assert (IQR (1%nat / (10 ^ (S (n - 1)))%nat) == IQR 1 / IQR (10 ^ (S (n - 1)))%nat).
    { unfold Rdiv.  
      rewrite IQR_inv ; auto. rewrite <- mult_IQR. unfold Qdiv ;  auto with real.
    }
    assert (Same_Ipart (r1 * IQR (10 ^ m)%nat) (r2 * IQR (10 ^ m)%nat)).
    {
      apply Same_Ipart_mult with (10 ^ (n - 1 - m))%nat.
      - apply Max_powan_0. omega.
      - rewrite !Rmult_assoc. 
        rewrite H5 ; auto.
        destruct H0 , H0 , H8 , H9.
        destruct H1 , H1 , H11 , H12.
        apply Rmult_lt_r with (r3 := IQR (10 ^ (n-1))%nat) in H ; auto.
        apply Rmult_lt_r with (r3 := IQR (10 ^ (n-1))%nat) in H3 ; auto.
        assert (S (n - 1) = n)%nat. { omega. }
        rewrite H14 in *.
        exists x. repeat split ; rewrite <- !INQ_IQR_INR in * ; auto with real.
        + pose proof (Rle_lt_trans _ _ _ H0 H).
          assert (x <= x0)%nat.
          { apply NNPP. intro.
            assert (x0 + 1 <= x)%nat. { omega. }
            apply INQ_le in H17. apply IQR_le in H17.
            apply (Rlt_irrefl (IQR (x0 + 1)%nat)).
            apply Rlt_trans with ((r2 + IQR 1 / IQR (10 ^ n)%nat) * IQR (10 ^ (n - 1))%nat) ; auto.
            apply Rle_lt_trans with (IQR x) ; auto.
          } 
          apply INQ_le in H16. apply IQR_le in H16.
          apply Rle_trans with (IQR x0) ; auto.
        + apply Rlt_trans with ((r1 + IQR 1 / IQR (10 ^ n)%nat) * IQR (10 ^ (n - 1))%nat) ; auto.
   }
   destruct H8 , H8 , H9 , H10.
   split ; intros ; destruct H12 , H12 , H12 ; exists x0 ; split ; auto.
   - assert (x0 = x)%nat. { apply (Ipart_unique (r1 * IQR (10 ^ m)%nat)) ; split ; auto. }
     subst. split ; auto.
   - assert (x0 = x)%nat. { apply (Ipart_unique (r2 * IQR (10 ^ m)%nat)) ; split ; auto. }
     subst. split ; auto.
  Qed.
  
  Theorem Dec_Q_Dec_R_lemma : forall (r : R)(q : Q)(n : nat) , (q >= 0)%Q -> Rabs(IQR q - r) < IQR 1 / IQR (10 ^ (S n))%nat
                                               -> InDecR r -> Dec_R (IQR q) (S n) 9 -> 
                                               Dec_R r (S n) 0.
  Proof.
    intros.
    apply NNPP. intro.
    destruct (H1 (S n)) ; auto.
    clear H3.
    destruct H4 , H3 , H3.
    destruct H2 , H2 , H2.
    apply Rabs_tri in H0. destruct H0.
    apply Rlt_Rminus_Rplus in H8. rewrite Rplus_comm in H8.
    symmetry in H6 , H4.
    apply mod_exists in H6 ; try (omega).
    apply mod_exists in H4 ; try (omega).
    destruct H4 , H6.
    assert (IQR (10 ^ S n)%nat > R0). 
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H0 ; auto.
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H8 ; auto.
    clear H1.
    rewrite Rmult_plus_distr_r in *.
    assert (IQR 1 / IQR (10 ^ S n)%nat * IQR (10 ^ S n)%nat == IQR 1). { field. apply Rgt_not_eq. auto. }
    rewrite H1 in *. clear H1.
    assert (x0 < x + 1 + 1)%nat.
    { apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (IQR q * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (r * IQR (10 ^ S n)%nat + IQR 1); auto.
      apply Rplus_lt_compat_r. auto.
    }
    assert (x < x0 + 1 + 1)%nat.
    { apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (IQR q * IQR (10 ^ S n)%nat + IQR 1); auto.
      apply Rplus_lt_compat_r. auto.
    }
    omega.
  Qed.
  
  Theorem Dec_R_lemma : forall (r : R)(n m x0: nat) , archimedean x0 (r * IQR (10 ^ n)%nat) -> Dec_R r (S n) m -> 
                                                      archimedean (x0 * 10 + m) (r * IQR (10 ^ (S n))%nat) .
  Proof.
    intros.
    destruct H.
    assert (m < 10)%nat. { apply (Dec_R_pro1 r (S n)). auto. }
    destruct H0 , H0 , H0.
    symmetry in H3.
    apply mod_exists in H3 ; auto.
    destruct H3.
    assert (IQR (10)%nat > R0). 
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. omega. }
    apply Rmult_le_r with (r3 := IQR (10)%nat) in H ; auto.
    apply Rmult_lt_r with (r3 := IQR (10)%nat) in H1 ; auto.
    assert (IQR (10 ^ n)%nat * IQR (10)%nat == IQR (10 ^ (S n))%nat).
    { apply NNPP. intro.
      apply Rdichotomy in H6.
      destruct H6 ; rewrite <- mult_IQR in H6 ; apply lt_IQR in H6 ; rewrite INQ_mult in H6; apply INQ_lt in H6 ; 
      rewrite Nat.pow_succ_r' in H6 ; omega.
    }
    rewrite Rmult_assoc in *. rewrite H6 in *. clear H6.
    rewrite <- mult_IQR in *.
    assert (x0 * 10 < x + 1)%nat.
    { apply INQ_lt. rewrite <- INQ_mult. apply lt_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto.
    }
    assert (x < (x0 + 1) * 10)%nat.
    { apply INQ_lt. rewrite <- INQ_mult. apply lt_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto.
    }
    assert (x1 = x0)%nat. { omega. }
    subst. rewrite mult_comm.
    split ; auto.
  Qed.
  
  Theorem Dec_Q_Dec_R_lemma2 : forall (r : R)(q: Q) (n : nat), Rabs(IQR q - r) < IQR 1 / IQR (10 ^ (S n))%nat
                              -> Dec_R r (S n) 0 -> Dec_R (IQR q) (S n) 9 -> Dec_R (IQR q) n 0 
                              -> ~ Dec_R r n 0.
  Proof.
    intros. intro. 
    apply Rabs_tri in H. destruct H.
    apply Rlt_Rminus_Rplus in H4. rewrite Rplus_comm in H4.
    inversion H0. inversion H1. inversion H2. inversion H3.
    destruct H5 , H6 , H7 , H8.
    symmetry in H9 , H10 , H11 , H12.
    apply mod_exists in H9 ; try (omega).
    apply mod_exists in H10 ; try (omega).
    apply mod_exists in H11 ; try (omega).
    apply mod_exists in H12 ; try (omega).
    destruct H9 , H10 , H11 , H12.
    assert (x = x2 * 10 + 0)%nat.
    { apply (Ipart_unique (r * IQR (10 ^ S n)%nat)) ; auto.
      apply Dec_R_lemma ; auto.
    }
    assert (x0 = x1 * 10  + 9)%nat.
    { apply (Ipart_unique (IQR q * IQR (10 ^ S n)%nat)) ; auto.
      apply Dec_R_lemma ; auto.
    }
    assert (x4 = x1)%nat. { omega. }
    assert (x3 = x2)%nat. { omega. }
    rewrite plus_0_r in *.
    subst x4. subst x3. 
    clear H0 H1 H2 H3.
    assert (IQR (10 ^ S n)%nat > R0). 
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H ; auto.
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H4 ; auto.
    rewrite Rmult_plus_distr_r in *.
    assert (IQR 1 / IQR (10 ^ S n)%nat * IQR (10 ^ S n)%nat == IQR 1).
    { field. apply Rgt_not_eq. auto. }
    rewrite H1 in *. clear H1.
    destruct H5 , H6 , H7 , H8.
    assert (x0 < x + 1 + 1)%nat.
    { apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (IQR q * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (r * IQR (10 ^ S n)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    assert (x < x0 + 1 + 1)%nat.
    { apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (IQR q * IQR (10 ^ S n)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    omega.
  Qed.
  
  Theorem Dec_Q_Dec_R_lemma3 : forall (r : R) (q : Q) , In_Search r -> Rabs (IQR q - r) < IQR 1 / IQR (10 ^ 1)%nat
                                                        -> InDecR r -> Dec_R (IQR q) 1 9
                                                        -> Dec_R r 1 0 -> Dec_R (IQR q) 0 9 -> False.
  Proof.
    intros r q a. intros.
    apply Rabs_tri in H. destruct H.
    apply Rlt_Rminus_Rplus in H4. rewrite Rplus_comm in H4.
    inversion H1. inversion H2. inversion H3. 
    destruct H5 , H6 , H7.
    assert (x = x1 * 10 + 9)%nat.
    { apply (Ipart_unique (IQR q * IQR (10 ^ 1)%nat)) ; auto.
      apply Dec_R_lemma ; auto.
    }
    assert (IQR (10 ^ 1)%nat > R0). 
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
    apply Rmult_lt_r with (r3 := IQR (10 ^ 1)%nat) in H ; auto.
    apply Rmult_lt_r with (r3 := IQR (10 ^ 1)%nat) in H4 ; auto.
    rewrite Rmult_plus_distr_r in *.
    assert (IQR 1 / IQR (10 ^ 1)%nat * IQR (10 ^ 1)%nat == IQR 1).
    { field. apply Rgt_not_eq.  auto. }
    rewrite H13 in *. clear H13.
    assert (x < x0 + 1 + 1)%nat.
    { destruct H5 , H6.
      apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (IQR q * IQR (10 ^ 1)%nat) ; auto.
      apply Rlt_trans with (r * IQR (10 ^ 1)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    assert (x0 < x + 1 + 1)%nat.
    { destruct H5 , H6.
      apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ 1)%nat) ; auto.
      apply Rlt_trans with (IQR q * IQR (10 ^ 1)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    destruct (H0 O) ; inversion H15 ; destruct H16.
    - assert (x0 = x2 * 10 + 0)%nat.
      { apply (Ipart_unique (r * IQR (10 ^ 1)%nat)) ; auto.
        apply Dec_R_lemma ; auto.
      }
      symmetry in H8 , H9 , H10 , H17.
      apply mod_exists in H8 ; try (omega).
      apply mod_exists in H9 ; try (omega). 
      apply mod_exists in H10 ; try (omega).
      apply mod_exists in H17 ; try (omega).
      destruct H8 ,H9, H10 , H17.
      assert (x2 < 10)%nat. 
      { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with r ; auto.
        destruct H16. assert (IQR (10 ^ 0)%nat == 1). { auto with real. }
        rewrite H20 in H16. rewrite Rmult_1_r in H16. auto.
        apply a.
      }  
      omega.
    - assert (x0 = x2 * 10 + 0)%nat.
      { apply (Ipart_unique (r * IQR (10 ^ 1)%nat)) ; auto.
        apply Dec_R_lemma ; auto.
      }
      symmetry in H8 , H9 , H10 , H17.
      apply mod_exists in H8 ; try (omega).
      apply mod_exists in H9 ; try (omega). 
      apply mod_exists in H10 ; try (omega).
      apply mod_exists in H17 ; try (omega).
      destruct H8 ,H9, H10 , H17.
      assert (x2 < 10)%nat. 
      { apply INQ_lt. apply lt_IQR. apply Rle_lt_trans with r ; auto.
        destruct H16. assert (IQR (10 ^ 0)%nat == 1). { auto with real. }
        rewrite H20 in H16. rewrite Rmult_1_r in H16. auto.
        apply a.
      }  
      omega.  
  Qed.
  
  Theorem Dec_Q_Dec_R_lemma4 : forall (r : R) (q : Q) (n : nat) , (q >= 0)%Q -> Rabs (IQR q - r) < IQR 1 / IQR (10 ^ (S n))%nat
                                                        -> InDecR r -> Dec_R (IQR q) (S n) 9
                                                        -> Dec_R r (S n) 0 -> ~ Dec_R (IQR q) n 9 
                                                        -> ~ Dec_R (IQR q) n 0 -> False.
  Proof.
    intros r q n pH. intros. 
    destruct (image_Defined_Dec_R (IQR q) n).
    apply Rle_ge. rewrite <- IQR_R0. apply IQR_le. auto.
    assert (x <> 9 /\ x <> 0)%nat. { split ; intro ; subst ; auto. }
    assert (x < 10)%nat. {  apply (Dec_R_pro1 (IQR q) n) ; auto. }
    assert ( x < 9 /\ x > 0)%nat. { omega. }
    clear H3 H4 H6 H7.
    apply Rabs_tri in H. destruct H.
    apply Rlt_Rminus_Rplus in H3. rewrite Rplus_comm in H3.
    inversion H1. inversion H2. inversion H5. 
    destruct H4 , H6 , H7.
    assert (x0 = x2 * 10 + 9)%nat.
    { apply (Ipart_unique (IQR q * IQR (10 ^ S n)%nat)) ; auto.
      apply Dec_R_lemma ; auto.
    }
    assert (IQR (10 ^ S n)%nat > R0). 
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega. }
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H ; auto.
    apply Rmult_lt_r with (r3 := IQR (10 ^ S n)%nat) in H3 ; auto.
    rewrite Rmult_plus_distr_r in *.
    assert (IQR 1 / IQR (10 ^ S n)%nat * IQR (10 ^ S n)%nat == IQR 1).
    { field. apply Rgt_not_eq. auto. }
    rewrite H14 in *. clear H14.
    assert (x0 < x1 + 1 + 1)%nat.
    { destruct H4 , H6.
      apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (IQR q * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (r * IQR (10 ^ S n)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    assert (x1 < x0 + 1 + 1)%nat.
    { destruct H4 , H6.
      apply INQ_lt. rewrite <- INQ_plus. apply lt_IQR. rewrite plus_IQR.
      apply Rle_lt_trans with (r * IQR (10 ^ S n)%nat) ; auto.
      apply Rlt_trans with (IQR q * IQR (10 ^ S n)%nat + IQR 1) ; auto.
      apply Rplus_lt_compat_r. auto.
    }
    destruct (H0 n) ; inversion H16 ; destruct H17.
    - assert (x1 = x3 * 10 + 0)%nat.
      { apply (Ipart_unique (r * IQR (10 ^ S n)%nat)) ; auto.
        apply Dec_R_lemma ; auto.
      }
      symmetry in H11 , H9 , H10 , H18.
      apply mod_exists in H11 ; try (omega).
      apply mod_exists in H9 ; try (omega). 
      apply mod_exists in H10 ; try (omega).
      apply mod_exists in H18 ; try (omega).
      destruct H11 ,H9, H10 , H18. 
      omega.
    - assert (x1 = x3 * 10 + 0)%nat.
      { apply (Ipart_unique (r * IQR (10 ^ S n)%nat)) ; auto.
        apply Dec_R_lemma ; auto.
      }
      symmetry in H11 , H9 , H10 , H18.
      apply mod_exists in H11 ; try (omega).
      apply mod_exists in H9 ; try (omega). 
      apply mod_exists in H10 ; try (omega).
      apply mod_exists in H18 ; try (omega).
      destruct H11 ,H9, H10 , H18. 
      omega.
  Qed.
  
  Theorem Dec_Q_Dec_R_same : forall (r : R)(q : Q)(n : nat) , In_Search r ->
                            (q >= 0)%Q -> Rabs(IQR q - r) < IQR 1 / IQR (10 ^ (S n))%nat
                                               -> InDecR r -> Dec_R (IQR q) (S n) 9 -> 
                                               {Dec_R r n 0} + {Dec_R r n 1}.
  Proof.
    intros r q n a. intros.
    pose proof Dec_Q_Dec_R_lemma r q n H H0 H1 H2.
    destruct (Dec_Q q n).
    - rewrite <- IQR_R0. apply IQR_le. auto.
    - right. apply NNPP. intro.
      destruct (H1 n) ; auto.
      apply (Dec_Q_Dec_R_lemma2 r q n) ; auto.
    - destruct (Dec_Q_nine q n).
      + rewrite <- IQR_R0. apply IQR_le. auto.
      + induction n.
        * exfalso. apply (Dec_Q_Dec_R_lemma3 r q) ; auto.
        * left. apply (Dec_Q_Dec_R_lemma r q n) ; auto.
          apply Rlt_trans with (IQR 1 / IQR (10 ^ S (S n))%nat) ; auto.
          unfold Rdiv. rewrite IQR_R1. rewrite ! Rmult_1_l.
          assert (forall n : nat , ~ ((10 ^ n)%nat == 0))%Q.
          { intro. intro.
            apply (Qlt_irrefl 0%Q).
            rewrite <- H4 at 2. rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
          }
          rewrite !IQR_inv ; auto.
          apply IQR_lt.
          apply Qlt_shift_inv_r.
          ** rewrite <- INQ_Qeq_0. apply INQ_lt. apply Max_powan_0. omega.
          ** rewrite Qmult_comm. rewrite Nat.pow_succ_r'. rewrite <- INQ_mult. 
             rewrite <- Qmult_assoc. rewrite Qmult_inv_r ; auto.
             rewrite <- INQ_Qeq_1. rewrite INQ_mult. apply INQ_lt. omega.
     + exfalso. 
       apply (Dec_Q_Dec_R_lemma4 r q n) ; auto.
  Qed.
  
End DEC_R.