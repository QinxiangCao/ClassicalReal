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
From CReal Require Import INR_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import Uncomputable.ComRealBase.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.

Module DEC_R (R : VIR_R).
  Module RLemmas := VirRLemmas (R).
  Import R RLemmas.
  Local Open Scope R_scope. 
  
  Definition In_Search : R -> Prop.
    intros.
    apply ( X >= R0 /\ X < IQR( INR 10)).
  Defined.
  
  Theorem R2_Rlt_R10 : R2 < IQR ( INR 10).
  Proof.
    unfold R2 ; rewrite <- IQR_R1 ; rewrite IQR_plus.
    apply IQR_lt. rewrite <- INR_Qeq_1. rewrite INR_plus. apply INR_lt. omega.
  Qed.
  
  Theorem In_Search_R0 : In_Search R0.
  Proof.
    split.
    - apply Rle_refl.
    - rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0. apply INR_lt. omega.
  Qed.
  Definition Dec_R : R -> nat -> nat -> Prop .
    intros r x y.
    apply (exists x0 : nat , (archimedean  x0 (r * IQR (INR (10 ^ x)))) /\ (y = x0 mod 10)%nat).
  Defined.

  Definition Un_cv'(A : nat -> Q -> Prop) (r : R) : Prop := 
     is_function A /\ (forall eps : R , eps > R0 -> (exists n : nat , 
          forall (m : nat) (q : Q) , (m >= n)%nat -> A m q -> Rabs(IQR q - r) < eps)).

  Definition InDec (R : nat -> nat -> Prop) : Prop := (forall x , R x 0%nat \/ R x 1%nat) /\
        (forall x y z , R x y -> R x z -> y = z).
  Definition Indec (R : nat -> nat ) : Prop := forall x , R x = 0%nat \/ R x = 1%nat.
  
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
  
  Definition Dec : Type := {R : nat -> nat -> Prop | InDec R}.
  Definition NNP_Dec (P : nat -> nat -> Prop)
   (H : InDec P): Dec.
    exists P. apply H.
  Defined.

  Definition Dec_r (D : Dec) (r : R) : Prop := (forall n m : nat , Dec_R r n m <-> proj1_sig D n m) /\ In_Search r.

  Definition NNP_T_NQP (x : nat -> nat -> Prop) : nat -> Q -> Prop.
    intros n q.
    apply ((forall m : nat , ((m <= n)%nat -> forall l : nat , Dec_R (IQR q) m l <-> x m l)
                                               /\ ((m > n)%nat -> Dec_R (IQR q) m 0%nat)) /\ (In_Search (IQR q))).
  Defined.

  Definition NQP_T_NRP (x : nat -> Q -> Prop) : nat -> R -> Prop.
    intros n r.
    apply (exists q : Q , IQR q = r /\ x n q).
  Defined.

  Theorem Same_Ipart_Dec_0 : forall r1 r2 : R , Same_Ipart r1 r2 -> forall l : nat , Dec_R r1 0 l <-> Dec_R r2 0 l.
  Proof. 
    intros.
    hnf in H.
    destruct H , H , H0 , H1.
    assert (10 ^ 0 = 1)%nat. { auto. }
    assert (IQR 1%nat = R1). { rewrite <- IQR_R1. apply IQR_eq. reflexivity. }
    split ; intros ; hnf in H5 ; hnf ; rewrite H3 in * ; rewrite H4 in * ; rewrite Rmult_1_r in * ;
    destruct (archimedean_exists r1), H6 ; destruct (archimedean_exists r2) , H8 ; destruct H5 , H5 , H5.
    - assert (x0 = x)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      assert (x2 = x0)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      assert (x1 = x)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      subst. exists x. split ; auto. split; auto.  
    - assert (x0 = x)%nat. { apply (Ipart_unique r1) ; split ; auto. }
      assert (x1 = x)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      assert (x2 = x1)%nat. { apply (Ipart_unique r2) ; split ; auto. }
      subst. exists x. split ; auto. split ; auto.
  Qed.

  Theorem partial_functional_Dec_R : forall (r : R) (n m1 m2 : nat) , Dec_R r n m1 -> Dec_R r n m2 -> m1 = m2.
  Proof.
    intros.
    hnf in *.
    destruct H , H0 , H , H0.
    assert (x = x0)%nat.  { apply (Ipart_unique (r * IQR(10^n)%nat)) ; auto. }
    subst ; auto.
  Qed.
  
  Theorem image_Defined_Dec_R : forall (r : R) (n : nat) , exists m : nat , Dec_R r n m.
  Proof.
    intros.
    destruct (archimedean_exists (r * IQR (INR (10 ^ n)))).
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
    rewrite INR_Qeq_0. lra.
    rewrite INR_Qeq_1. lra.
  Qed.
  
  Theorem Two_Dec : Dec_R R2 0 2.
  Proof.
    hnf ; intros.
    exists 2%nat.
    split ; auto.
    split .
    - simpl. unfold R2.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      rewrite IQR_plus. apply IQR_le. 
      rewrite INR_plus. apply INR_le. omega.
    - simpl. unfold R2.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      rewrite IQR_plus. apply IQR_lt. 
      rewrite INR_plus. apply INR_lt. omega.
  Qed.
  
  Theorem Dec_R_eq_Same_Ipart : forall (r1 r2 :R)(n :nat) , In_Search r1 -> In_Search r2 -> (forall (j : nat) ,(j <= n)%nat -> 
               (forall m : nat , Dec_R r1 j m <-> Dec_R r2 j m)) -> (forall (j : nat) , (j <= n)%nat -> Same_Ipart (r1 * IQR (10^j)%nat) (r2 * IQR(10^j)%nat)).
  Proof.
    intros.
    generalize dependent n.
    induction j ; intros.
    - simpl in *.
      destruct (image_Defined_Dec_R r1 O).
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
        { apply INR_lt. apply IQR_lt. apply Rle_lt_trans with (r1 * IQR 1%nat); auto.
          rewrite IQR_R1_same. rewrite Rmult_1_r. apply H.
        }
        assert (x2 = 0)%nat. { omega. }
        assert (x0 < 10)%nat.
        { apply INR_lt. apply IQR_lt. apply Rle_lt_trans with (r2 * IQR 1%nat); auto.
          rewrite IQR_R1_same. rewrite Rmult_1_r. apply H0.
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
          apply INR_le in H9. apply IQR_le in H9.
          apply Rlt_le_trans with (IQR (10 * S x)%nat) ; auto.
          apply Rle_lt_trans with (r1 * IQR (10 ^ j)%nat * IQR (10)%nat).
          + destruct H. destruct H.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
              rewrite Nat.pow_succ_r'. omega.
            * subst. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. lra.
        - apply lt_le_S in H6.
          apply (mult_le_compat_l _ _ 10) in H6.
          assert( 10 * x3 + x0 + 1 <= 10 * S x3)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x3 + x0 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H9 H6 ). clear H6 H9.
          apply INR_le in H12. apply IQR_le in H12.
          apply Rle_trans with (IQR (10 * x)%nat) ; auto.
          apply Rle_trans with (IQR x * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite IQR_mult.
            apply IQR_le. rewrite INR_mult. lra.
          + apply Rle_trans with (r1 * IQR (10^j)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H. destruct H.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** subst. rewrite !Rmult_0_l. apply Rle_refl.
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
          apply INR_le in H12. apply IQR_le in H12.
          apply Rlt_le_trans with (IQR (10 * S x)%nat) ; auto.
          apply Rle_lt_trans with (r2 * IQR (10 ^ j)%nat * IQR (10)%nat).
          + destruct H0. destruct H0.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
              rewrite Nat.pow_succ_r'. omega.
            * subst. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. lra.
        - apply lt_le_S in H9.
          apply (mult_le_compat_l _ _ 10) in H9.
          assert( 10 * x4 + x0 + 1 <= 10 * S x4)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S j)%nat)).
          apply Rlt_le_trans with (IQR (10 * x4 + x0 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H12 H9 ). clear H12 H9.
          apply INR_le in H13. apply IQR_le in H13.
          apply Rle_trans with (IQR (10 * x)%nat) ; auto.
          apply Rle_trans with (IQR x * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite IQR_mult.
            apply IQR_le. rewrite INR_mult. lra.
          + apply Rle_trans with (r2 * IQR (10^j)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H0. destruct H0.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** subst. rewrite !Rmult_0_l. apply Rle_refl.
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
             destruct H.
             *** rewrite IQR_R1_same. apply Rle_refl.
             *** subst. rewrite !Rmult_0_l. apply Rle_refl.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite IQR_plus. apply IQR_le.
                 rewrite INR_plus. lra.
             *** apply Rle_trans with (r2 + IQR 1%nat).
                 **** apply Rle_Rplus_r. apply Rle_trans with (r2 * IQR 1%nat) ; auto.
                      rewrite <- Rmult_1_r. destruct H0. destruct H0.
                      ++ rewrite IQR_R1_same. apply Rle_refl.
                      ++ subst. rewrite !Rmult_0_l. apply Rle_refl.
                 **** rewrite Rmult_1_l. apply Rle_Rplus_l. apply Rle_ge.
                      apply Rmult_ge_divr.
                      ++ rewrite <- IQR_R0. apply IQR_lt. rewrite INR_Qeq_1. lra.
                      ++ rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. omega.
      + apply Rlt_Rminus_Rplus. apply Rmult_lt_l with (R1).
        * rewrite <- IQR_R0. rewrite <- IQR_R1. apply IQR_lt. lra.
        * apply Rlt_le_trans with (IQR (x + 1)%nat).
          ** apply Rle_lt_trans with (r2 * IQR 1%nat) ; auto.
             rewrite Rmult_comm. destruct H0.
             destruct H0.
             *** rewrite IQR_R1_same. apply Rle_refl.
             *** subst. rewrite !Rmult_0_l. apply Rle_refl.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite IQR_plus. apply IQR_le.
                 rewrite INR_plus. lra.
             *** apply Rle_trans with (r1 + IQR 1%nat).
                 **** apply Rle_Rplus_r. apply Rle_trans with (r1 * IQR 1%nat) ; auto.
                      rewrite <- Rmult_1_r. destruct H. destruct H.
                      ++ rewrite IQR_R1_same. apply Rle_refl.
                      ++ subst. rewrite !Rmult_0_l. apply Rle_refl.
                 **** rewrite Rmult_1_l. rewrite Rplus_comm. apply Rle_Rplus_r.
                      apply Rle_ge. apply Rmult_ge_divr.
                      ++ rewrite <- IQR_R0. apply IQR_lt. rewrite INR_Qeq_1. lra.
                      ++ rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. omega.
    - assert (forall j : nat, (j <= n)%nat -> forall m : nat, Dec_R r1 j m <-> Dec_R r2 j m).
      {  intros. apply H1. omega. }
      assert (S n <= S n)%nat. { omega. }
      pose proof Dec_R_eq_Same_Ipart r1 r2 _ H H0 H1 (S n) H3.
      destruct H4 , H4 , H5 ,H6. clear H3 H2 IHn.
      apply Rabs_tri. split.
      + apply Rmult_lt_l with (IQR(10 ^ S n)%nat).
        * rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
        * apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
          ** rewrite Rmult_comm. auto.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite IQR_plus. apply IQR_le.
                 rewrite INR_plus. lra.
             *** apply Rle_trans with (IQR (10 ^ S n)%nat * r2 + IQR 1%nat).
                 **** apply Rle_Rplus_r. rewrite Rmult_comm. auto.
                 **** rewrite Rmult_plus_distr_l. apply Rle_Rplus_l.
                      unfold Rdiv.
                      rewrite (Rmult_comm (IQR 1%nat) (/ IQR (10 ^ S n)%nat)).
                      rewrite <- Rmult_assoc.
                      rewrite Rinv_self. 
                      ++ rewrite Rmult_1_l. apply Rle_refl.
                      ++ unfold not. intros.
                         apply (Rlt_irrefl R0). rewrite <- H2 at 2.
                         rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0.
                         apply INR_lt. apply Max_powan_0. omega.
      + apply Rlt_Rminus_Rplus.
        apply Rmult_lt_l with (IQR(10 ^ S n)%nat).
        * rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
        * apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
          ** rewrite Rmult_comm. auto.
          ** apply Rle_trans with (IQR x + IQR 1%nat).
             *** rewrite IQR_plus. apply IQR_le.
                 rewrite INR_plus. lra.
             *** apply Rle_trans with (IQR (10 ^ S n)%nat * r1 + IQR 1%nat).
                 **** apply Rle_Rplus_r. rewrite Rmult_comm. auto.
                 **** rewrite Rmult_plus_distr_l. rewrite Rplus_comm. apply Rle_Rplus_r.
                      unfold Rdiv.
                      rewrite (Rmult_comm (IQR 1%nat) (/ IQR (10 ^ S n)%nat)).
                      rewrite <- Rmult_assoc.
                      rewrite Rinv_self. 
                      ++ rewrite Rmult_1_l. apply Rle_refl.
                      ++ unfold not. intros.
                         apply (Rlt_irrefl R0). rewrite <- H2 at 2.
                         rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0.
                         apply INR_lt. apply Max_powan_0. omega.
  Qed.
  
  Theorem Dec_R_eq  : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 = r2 <-> (forall (j : nat) , forall m : nat , Dec_R r1 j m <-> Dec_R r2 j m).
  Proof.
    split ; intros ; subst ; try (reflexivity).
    apply Req_same.
    intros.
    apply eps_gt_10n in H2.
    destruct H2.
    apply Rlt_trans with (IQR 1 * / IQR (10 ^ x)%nat) ; auto.
    apply Dec_R_eq_lemma ; auto.
  Qed.
  
  Theorem Dec_R_not_eq : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 <> r2 <-> exists (j : nat), (forall m : nat,  Dec_R r1 j m -> ~ Dec_R r2 j m).
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
      unfold not.
      intros.
      subst.
      pose proof image_Defined_Dec_R r2 x.
      destruct H2.
      specialize (H1 x0 H2). auto. 
  Qed.
  
  Theorem Dec_R_lt_lemma :forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> (exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 < m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2 -> (m1 = m2)%nat))) -> r1 < r2.
  Proof.
    intros.
    destruct H1. destruct H1.
    destruct x.
    + destruct (image_Defined_Dec_R r1 O).
      destruct (image_Defined_Dec_R r2 O).
      assert (x < x0)%nat. { apply H1 ; auto. }
      destruct H3 , H3 , H3.
      destruct H4 , H4 , H4.
      simpl in H3 , H4 , H7 , H9.
      symmetry in H6 , H8.
      assert (x0 < 10)%nat. { rewrite <- H8. apply Nat.mod_upper_bound. auto. }
      apply mod_exists in H6 ; try (omega).
      apply mod_exists in H8 ; auto.
      destruct H6, H8.
      assert (x1 < 10)%nat.
      { apply INR_lt. apply IQR_lt. apply Rle_lt_trans with (r1 * IQR 1%nat); auto.
        rewrite IQR_R1_same. rewrite Rmult_1_r. apply H.
      }
      assert (x3 = 0)%nat. { omega. }
      assert (x2 < 10)%nat.
      { apply INR_lt. apply IQR_lt. apply Rle_lt_trans with (r2 * IQR 1%nat); auto.
        rewrite IQR_R1_same. rewrite Rmult_1_r. apply H0.
      }
      assert (x4 = 0)%nat. { omega. }
      subst. simpl in *.
      apply lt_le_S in H5. rewrite <- Nat.add_1_r in H5.
      rewrite <- Rmult_1_r. rewrite <- Rmult_1_r at 1.
      rewrite IQR_R1_same in *.
      apply Rlt_le_trans with (IQR (x + 1)%nat) ; auto.
      apply Rle_trans with (IQR x0) ; auto.
      apply IQR_le. apply INR_le. auto.
    + pose proof Dec_R_eq_Same_Ipart _ _ x H H0.
      assert (forall j : nat, (j <= x)%nat -> forall m : nat,  Dec_R r1 j m <-> Dec_R r2 j m).
      { split ; intros.
        - destruct (image_Defined_Dec_R r2 j).
          assert (m = x0)%nat. { apply (H2 j) ; auto. omega. }
          subst ; auto.
        - destruct (image_Defined_Dec_R r1 j).
          assert (x0 = m)%nat. { apply (H2 j) ; auto. omega. }
          subst ; auto.
      }
      assert (x <= x)%nat. { omega. }
      specialize (H3 H4 x H5). clear H4 H5.
      destruct H3 , H3 , H4 , H5.
      destruct (image_Defined_Dec_R r1 (S x)).
      destruct (image_Defined_Dec_R r2 (S x)).
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
          apply INR_le in H2. apply IQR_le in H2.
          apply Rlt_le_trans with (IQR (10 * S x0)%nat) ; auto.
          apply Rle_lt_trans with (r1 * IQR (10 ^ x)%nat * IQR (10)%nat).
          + destruct H. destruct H.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
              rewrite Nat.pow_succ_r'. omega.
            * subst. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x0 + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. lra.
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * x5 + x1 + 1 <= 10 * S x5)%nat. { omega. }
          apply (Rlt_irrefl (r1 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x5 + x1 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H2 H1 ). clear H2 H1.
          apply INR_le in H10. apply IQR_le in H10.
          apply Rle_trans with (IQR (10 * x0)%nat) ; auto.
          apply Rle_trans with (IQR x0 * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite IQR_mult.
            apply IQR_le. rewrite INR_mult. lra.
          + apply Rle_trans with (r1 * IQR (10^x)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H. destruct H.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** subst. rewrite !Rmult_0_l. apply Rle_refl.
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
          apply INR_le in H2. apply IQR_le in H2.
          apply Rlt_le_trans with (IQR (10 * S x0)%nat) ; auto.
          apply Rle_lt_trans with (r2 * IQR (10 ^ x)%nat * IQR (10)%nat).
          + destruct H0. destruct H0.
            * rewrite Rmult_assoc. apply Rmult_le_l ; auto.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
              rewrite Nat.pow_succ_r'. omega.
            * subst. rewrite !Rmult_0_l. apply Rle_refl.
          + apply Rlt_le_trans with (IQR (x0 + 1)%nat * IQR 10%nat).
            * apply Rmult_lt_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * rewrite Nat.add_1_r. rewrite Rmult_comm.
              rewrite IQR_mult. apply IQR_le. rewrite INR_mult. lra.
        - apply lt_le_S in H1.
          apply (mult_le_compat_l _ _ 10) in H1.
          assert( 10 * x6 + x2 + 1 <= 10 * S x6)%nat. { omega. }
          apply (Rlt_irrefl (r2 * IQR (10 ^ S x)%nat)).
          apply Rlt_le_trans with (IQR (10 * x6 + x2 + 1)%nat) ; auto.
          pose proof (le_trans _ _ _ H2 H1 ). clear H2 H1.
          apply INR_le in H10. apply IQR_le in H10.
          apply Rle_trans with (IQR (10 * x0)%nat) ; auto.
          apply Rle_trans with (IQR x0 * IQR (10)%nat).
          + rewrite Rmult_comm. rewrite IQR_mult.
            apply IQR_le. rewrite INR_mult. lra.
          + apply Rle_trans with (r2 * IQR (10^x)%nat * IQR 10%nat).
            * apply Rmult_le_r ; auto. destruct H. apply Rle_ge in H.
              apply Rle_lt_trans with r1 ; auto.
            * destruct H0. destruct H0.
              ** rewrite Rmult_assoc. apply Rmult_le_l ; auto.
                 rewrite IQR_mult. apply IQR_le. rewrite INR_mult. apply INR_le. 
                 rewrite Nat.pow_succ_r'. omega.
              ** subst. rewrite !Rmult_0_l. apply Rle_refl.
      }
      subst.
      assert (10 * x6 + x1 < 10 * x6 + x2)%nat. { omega. }
      apply lt_le_S in H1. rewrite <- Nat.add_1_r in H1.
      apply INR_le in H1. apply IQR_le in H1.
      apply Rmult_lt_r with (IQR (10 ^ S x)%nat).
      - rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0.
        apply INR_lt. apply Max_powan_0. omega.
      - apply Rlt_le_trans with (IQR (10 * x6 + x1 + 1)%nat) ; auto.
        apply Rle_trans with (IQR (10 * x6 + x2)%nat) ; auto.
  Qed.
  
  Theorem Dec_R_lt_same : forall (r1 r2 : R) , In_Search r1 -> In_Search r2 -> r1 < r2 <-> 
                       exists (j : nat), (forall m1 m2 : nat ,Dec_R r1 j m1 -> Dec_R r2 j m2 -> (m1 < m2)%nat) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (forall m1 m2 : nat , Dec_R r1 k m1 -> Dec_R r2 k m2 -> (m1 = m2)%nat)).
  Proof.
    split ; intros.
    - assert (r1 <> r2). { apply Rnot_eq_lt. right ; auto. }
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
  
  Theorem image_defined_NNP_T_NQP : forall (x : nat -> nat -> Prop) , 
                  InDec x -> forall n : nat , exists q : Q , (NNP_T_NQP x) n q.
  Proof.
    intros.
    destruct H.
    induction n.
    - destruct (H O).
      + exists (INR O).
        split ; intros. 
        * split ; intros. 
          ** apply le_n_0_eq in H2. subst.
             split ; intros ; hnf in * .
             *** destruct H2 , H2 , H2.
                 rewrite IQR_mult in *. simpl in H2 , H4.
                 apply IQR_le in H2. apply IQR_lt in H4.
                 rewrite INR_mult in *. rewrite mult_1_r in *.
                 apply INR_le in H2. apply INR_lt in H4.
                 assert (x0 = O). { omega. } subst.
                 assert (0 mod 10 = 0)%nat. { auto. }
                 rewrite H3. auto.
             *** exists O.
                 assert (l = 0)%nat. { apply (H0 O); auto. }
                 split ; auto.
                 split ; rewrite IQR_mult ; try (apply IQR_lt) ; try (apply IQR_le);
                 rewrite INR_mult ; try (apply INR_le) ; try (apply INR_lt) ; omega.
          ** hnf.
             exists O. split ; auto.
             split ; rewrite IQR_mult ; try (apply IQR_lt) ; try (apply IQR_le);
             rewrite INR_mult ; try (apply INR_le) ; try (apply INR_lt) ; omega.
        * split.
          ** rewrite <- IQR_R0. apply IQR_le.
             rewrite INR_Qeq_0. lra.
          ** apply IQR_lt. apply INR_lt. omega.
      + exists (INR (1)).
        hnf. split ; intros.
        * split ; intros.
          ** assert (m = O). { omega. } subst.
             split ; intros ; hnf in *. 
             *** destruct H3 , H3 , H3.
                 rewrite IQR_mult in *. simpl in H3 , H5.
                 apply IQR_le in H3. apply IQR_lt in H5.
                 rewrite INR_mult in *. rewrite mult_1_l in *.
                 apply INR_le in H3. apply INR_lt in H5.
                 assert (x0 = 1)%nat. { omega. } subst.
                 assert (1 mod 10 = 1)%nat. { auto. }
                 rewrite H4. auto.
             *** exists 1%nat.
                 assert (1 = l)%nat. { apply (H0 O) ; auto. }
                 subst.
                 split ; auto.
                 split ; rewrite IQR_mult ; try (apply IQR_lt) ; try (apply IQR_le);
                 rewrite INR_mult ; simpl ; try (apply INR_le ; omega);  try (apply INR_lt ; omega). 
          ** hnf. destruct (archimedean_exists (IQR 1%nat * IQR (10 ^ m)%nat)).
             exists x0. split ; auto. destruct H3.
             rewrite IQR_mult in * ; apply IQR_le in H3 ; apply IQR_lt in H4 ;
             rewrite INR_mult in * ; rewrite mult_1_l in * ; apply INR_le in H3 ; apply INR_lt in H4.
             assert (x0 = 10 ^ m)%nat. {omega. }
             subst.
             assert (m = m - 1 + 1)%nat. { omega. }
             rewrite H5. rewrite Nat.pow_add_r. 
             rewrite Nat.mul_mod ; auto.
             assert (10 ^ 1 mod 10 = 0)%nat. { auto. }
             rewrite H6. rewrite mult_0_r. auto.
        * split.
          ** rewrite <- IQR_R0. apply Rle_ge. apply IQR_le.
             rewrite <- INR_Qeq_0. apply INR_le. omega.
          ** apply IQR_lt. apply INR_lt. omega. 
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
      + exists (x0 + INR (1) / INR (10 ^ S n))%Q.
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
                    rewrite IQR_mult in *. apply IQR_le in H4. apply IQR_lt in H7.
                    apply IQR_le in H1. apply IQR_lt in H5.
                    rewrite Qmult_plus_distr_l in *. 
                    assert (1%nat / (10 ^ S n)%nat * (10 ^ S n)%nat == INR (1))%Q.
                    { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
                      rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
                    }
                    rewrite H8 in H7 , H4.
                    clear H8.
                    rewrite <- (Qplus_le_l _ _ (INR(1))) in H1.
                    rewrite <- (Qplus_lt_l _ _ (INR(1))) in H5.
                    rewrite INR_plus in *.
                    assert (x1 + 1 = x2)%nat. 
                    {
                      apply NNPP. intro. apply nat_total_order in H8.
                      destruct H8 ; apply lt_le_S in H8 ; rewrite <- Nat.add_1_r in H8 ; apply INR_le in H8 ;
                      apply (Qlt_irrefl (x0 * (10 ^ S n)%nat + 1%nat)).
                      - apply Qlt_le_trans with (INR (x1+1+1)) ; auto.
                        apply Qle_trans with (INR x2); auto. 
                      - apply Qlt_le_trans with (INR (x2 + 1)) ; auto.
                        apply Qle_trans with (INR (x1 + 1));  auto.
                    }
                    subst. rewrite Nat.add_mod ; auto.
                    rewrite <- H3. auto. 
                 }
                 subst. auto.
             *** subst.
                 apply H1 ; auto. hnf in *.
                 destruct H4 , H4 , H4.
                 destruct (archimedean_exists (IQR x0 * IQR (10 ^ m)%nat)) .
                 exists x2. split ; auto. destruct H8.
                 assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat) ((IQR x0 * IQR (10 ^ m)%nat))).
                 {  apply  (Same_Ipart_mult _ _ (10 ^ (n - m))).
                    - apply Max_powan_0 ; omega.
                    - destruct (archimedean_exists (IQR (x0 * INR (10 ^ n)))) , H10.
                      exists x3.
                      assert ((10 ^ m) * (10 ^ (n - m)) = 10 ^ n)%nat. 
                      {
                        assert (n = n - m + m)%nat. { omega. }
                        rewrite H12 at 2. rewrite Nat.pow_add_r. apply mult_comm. 
                      }
                      repeat split ; repeat rewrite IQR_mult in * ; try (apply IQR_le) ; try (apply IQR_lt);
                      apply IQR_le in H10 ; apply IQR_lt in H11 ;
                      rewrite <- Qmult_assoc in * ; rewrite INR_mult in * ; rewrite H12 in * ; auto ;
                      rewrite Qmult_plus_distr_l in *.
                      + apply Qle_trans with (x0 * (INR (10 ^ n)))%Q ; auto.
                        rewrite <- Qplus_0_r at 1.
                        apply Qplus_le_r.
                        rewrite INR_Qeq_1. unfold Qdiv. 
                        rewrite Qmult_1_l. apply Qmult_le_0_compat.
                        * apply Qinv_le_0_compat. rewrite <- INR_Qeq_0.
                          apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                        * rewrite <- INR_Qeq_0.
                          apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                      + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
                        assert (INR(1) / INR(10^S n) * INR (10 ^ n) == INR (1) / INR(10) )%Q. 
                        { 
                          apply (Qmult_inj_r _ _ (INR 10)).
                          - intro. rewrite <- INR_Qeq_0 in H14. apply Qeq_INR_eq in H14. inversion H14.
                          - rewrite <- Qmult_assoc. rewrite INR_mult.  rewrite <- H13.
                            field. split ; intro.
                            + rewrite <- INR_Qeq_0 in H14. apply Qeq_INR_eq in H14. inversion H14.
                            + apply (Qlt_irrefl 0%Q). rewrite <- H14 at 2.
                              rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0 ; omega.
                        }
                        rewrite H14. destruct H1. clear H15. 
                        specialize (H1 (S n)). destruct H1.
                        assert (S n > n)%nat. { omega. }
                        specialize (H15 H16). clear H16 H1.
                        hnf in H15. rewrite IQR_mult in *.
                        destruct H15,H1,H1.
                        apply IQR_le in H1. apply IQR_lt in H16.
                        symmetry in H15.
                        apply mod_exists in H15 ; try (omega) .
                        destruct H15.
                        rewrite plus_0_r in H15.
                        rewrite H13 in H1 , H16. rewrite <- INR_mult in *.
                        rewrite Qmult_assoc in *.
                        subst x4.
                        rewrite mult_comm in H1. rewrite mult_comm in H16.
                        rewrite <- INR_plus in H16.
                        rewrite <- INR_mult in *.
                        assert (INR(10) > 0)%Q. { rewrite <- INR_Qeq_0. apply INR_lt. omega. }
                        apply Qmult_lt_0_le_reg_r in H1 ; auto.
                        assert (INR(1) == INR(1) / INR(10) * INR(10))%Q. { field. intro. rewrite H17 in H15. apply Qlt_irrefl in H15. auto. }
                        rewrite H17 in H16.
                        rewrite <- Qmult_plus_distr_l in H16.
                        apply Qmult_lt_r in H16 ; auto.
                        assert (x0 * (10 ^ n)%nat < x5 + 1%nat)%Q.
                        { apply Qlt_trans with (x5 + 1%nat / 10%nat)%Q ; auto.
                        apply Qplus_lt_r. rewrite INR_Qeq_1.
                        unfold Qdiv. rewrite Qmult_1_l.
                        apply Qlt_shift_inv_r ; auto.
                        }
                        assert (x3 = x5).
                        {
                          apply (Ipart_unique (IQR (x0 * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
                          rewrite <- INR_plus. auto.
                        }
                        subst.
                        apply Qlt_trans with (x5 + 1%nat / 10%nat + 1%nat / 10%nat)%Q.
                        * apply Qplus_lt_l. auto.
                        * rewrite <- INR_plus. rewrite <- Qplus_assoc.
                          apply Qplus_lt_r.
                          unfold Qdiv. rewrite <- Qmult_plus_distr_l.
                          rewrite INR_plus. simpl. rewrite INR_Qeq_1.
                          apply Qmult_lt_r with (INR (10)) ; auto.
                 }
                 destruct H10. destruct H10 , H11 , H12.
                 assert (x1 = x3)%nat. { apply (Ipart_unique (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)) ; auto. }
                 assert (x2 = x3)%nat. { apply (Ipart_unique (IQR x0 * IQR (10 ^ m)%nat)) ; auto. }
                 subst ; auto.
             *** subst. assert (l = 1)%nat. { apply (H0 (S n)) ; auto. }
                 subst. destruct H1. clear H5. 
                 specialize (H1 (S n)). destruct H1.
                 assert (S n > n)%nat. { omega. }
                 specialize (H5 H6). clear H1 H3 H6.
                 hnf in *.
                 destruct H5 , H1 , H1.
                 destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ S n)%nat)).
                 exists x2. split ; auto.
                 destruct H6.
                 rewrite IQR_mult in *. apply IQR_le in H6. apply IQR_lt in H7.
                 apply IQR_le in H1. apply IQR_lt in H5.
                 rewrite Qmult_plus_distr_l in *. 
                 assert (1%nat / (10 ^ S n)%nat * (10 ^ S n)%nat == INR (1))%Q.
                 { field. intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
                   rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
                 }
                 rewrite H8 in H7 , H6.
                 clear H8.
                 rewrite <- (Qplus_le_l _ _ (INR(1))) in H1.
                 rewrite <- (Qplus_lt_l _ _ (INR(1))) in H5.
                 rewrite INR_plus in *.
                 assert (x1 + 1 = x2)%nat. 
                 {
                    apply NNPP. intro. apply nat_total_order in H8.
                    destruct H8 ; apply lt_le_S in H8 ; rewrite <- Nat.add_1_r in H8 ; apply INR_le in H8 ;
                    apply (Qlt_irrefl (x0 * (10 ^ S n)%nat + 1%nat)).
                    - apply Qlt_le_trans with (INR (x1+1+1)) ; auto.
                      apply Qle_trans with (INR x2); auto. 
                    - apply Qlt_le_trans with (INR (x2 + 1)) ; auto.
                      apply Qle_trans with (INR (x1 + 1));  auto.
                 }
                 subst. rewrite Nat.add_mod ; auto.
                 rewrite <- H3. auto. 
             *** subst.
                 apply H1 in H4; auto. hnf in *.
                 destruct H4 , H4 , H4.
                 destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)).
                 exists x2. split ; auto. destruct H8.
                 assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat) ((IQR x0 * IQR (10 ^ m)%nat))).
                 {  apply  (Same_Ipart_mult _ _ (10 ^ (n - m))).
                    - apply Max_powan_0 ; omega.
                    - destruct (archimedean_exists (IQR (x0 * INR (10 ^ n)))) , H10.
                      exists x3.
                      assert ((10 ^ m) * (10 ^ (n - m)) = 10 ^ n)%nat. 
                      {
                        assert (n = n - m + m)%nat. { omega. }
                        rewrite H12 at 2. rewrite Nat.pow_add_r. apply mult_comm. 
                      }
                      repeat split ; repeat rewrite IQR_mult in * ; try (apply IQR_le) ; try (apply IQR_lt);
                      apply IQR_le in H10 ; apply IQR_lt in H11 ;
                      rewrite <- Qmult_assoc in * ; rewrite INR_mult in * ; rewrite H12 in * ; auto ;
                      rewrite Qmult_plus_distr_l in *.
                      + apply Qle_trans with (x0 * (INR (10 ^ n)))%Q ; auto.
                        rewrite <- Qplus_0_r at 1.
                        apply Qplus_le_r.
                        rewrite INR_Qeq_1. unfold Qdiv. 
                        rewrite Qmult_1_l. apply Qmult_le_0_compat.
                        * apply Qinv_le_0_compat. rewrite <- INR_Qeq_0.
                          apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                        * rewrite <- INR_Qeq_0.
                          apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                      + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
                        assert (INR(1) / INR(10^S n) * INR (10 ^ n) == INR (1) / INR(10) )%Q. 
                        { 
                          apply (Qmult_inj_r _ _ (INR 10)).
                          - intro. rewrite <- INR_Qeq_0 in H14. apply Qeq_INR_eq in H14. inversion H14.
                          - rewrite <- Qmult_assoc. rewrite INR_mult.  rewrite <- H13.
                            field. split ; intro.
                            + rewrite <- INR_Qeq_0 in H14. apply Qeq_INR_eq in H14. inversion H14.
                            + apply (Qlt_irrefl 0%Q). rewrite <- H14 at 2.
                              rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0 ; omega.
                        }
                        rewrite H14. destruct H1. clear H15. 
                        specialize (H1 (S n)). destruct H1.
                        assert (S n > n)%nat. { omega. }
                        specialize (H15 H16). clear H16 H1.
                        hnf in H15. rewrite IQR_mult in *.
                        destruct H15,H1,H1.
                        apply IQR_le in H1. apply IQR_lt in H16.
                        symmetry in H15.
                        apply mod_exists in H15 ; try (omega) .
                        destruct H15.
                        rewrite plus_0_r in H15.
                        rewrite H13 in H1 , H16. rewrite <- INR_mult in *.
                        rewrite Qmult_assoc in *.
                        subst x4.
                        rewrite mult_comm in H1. rewrite mult_comm in H16.
                        rewrite <- INR_plus in H16.
                        rewrite <- INR_mult in *.
                        assert (INR(10) > 0)%Q. { rewrite <- INR_Qeq_0. apply INR_lt. omega. }
                        apply Qmult_lt_0_le_reg_r in H1 ; auto.
                        assert (INR(1) == INR(1) / INR(10) * INR(10))%Q. { field. intro. rewrite H17 in H15. apply Qlt_irrefl in H15. auto. }
                        rewrite H17 in H16.
                        rewrite <- Qmult_plus_distr_l in H16.
                        apply Qmult_lt_r in H16 ; auto.
                        assert (x0 * (10 ^ n)%nat < x5 + 1%nat)%Q.
                        { apply Qlt_trans with (x5 + 1%nat / 10%nat)%Q ; auto.
                          apply Qplus_lt_r. rewrite INR_Qeq_1.
                          unfold Qdiv. rewrite Qmult_1_l.
                          apply Qlt_shift_inv_r ; auto.
                        }
                        assert (x3 = x5).
                        {
                          apply (Ipart_unique (IQR (x0 * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
                          rewrite <- INR_plus. auto.
                        }
                        subst.
                        apply Qlt_trans with (x5 + 1%nat / 10%nat + 1%nat / 10%nat)%Q.
                        * apply Qplus_lt_l. auto.
                        * rewrite <- INR_plus. rewrite <- Qplus_assoc.
                          apply Qplus_lt_r.
                          unfold Qdiv. rewrite <- Qmult_plus_distr_l.
                          rewrite INR_plus. simpl. rewrite INR_Qeq_1.
                          apply Qmult_lt_r with (INR (10)) ; auto.
                 }
                 destruct H10. destruct H10 , H11 , H12.
                 assert (x2 = x3)%nat. { apply (Ipart_unique (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)) ;auto. }
                 assert (x1 = x3)%nat. { apply (Ipart_unique (IQR x0 * IQR (10 ^ m)%nat)) ; auto. }
                 subst ; auto.
          ** apply Nat.lt_succ_l in H3 as goal. destruct H1. clear H4.
             specialize (H1 m). destruct H1. specialize (H4 goal).
             clear H1 goal H2.
             hnf in *.
             destruct H4 , H1 , H1.
             destruct (archimedean_exists (IQR (x0 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ m)%nat)).
             exists x2. split ; auto. destruct H5.
             rewrite IQR_mult in *. apply IQR_le in H5. apply IQR_lt in H6.
             apply IQR_le in H1. apply IQR_lt in H4.
             rewrite Qmult_plus_distr_l in *. 
             assert (1%nat / (10 ^ S n)%nat * (10 ^ m)%nat == INR (10 ^ (m - S n)))%Q.
             {
               assert (m = m - S n + S n)%nat. { omega. }
               rewrite H7 at 1. rewrite Nat.pow_add_r. rewrite <- INR_mult. 
               rewrite Qmult_comm. rewrite <- Qmult_assoc. unfold Qdiv.
               rewrite INR_Qeq_1. field.
               intro. apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
               rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
             }
             rewrite H7 in *. clear H7.
             rewrite <- (Qplus_le_l _ _ (INR(10 ^ (m - S n)))) in H1.
             rewrite <- (Qplus_lt_l _ _ (INR(10 ^ (m - S n)))) in H4.
             rewrite INR_plus in *.
             assert (x1 + 1 + 10 ^ (m - S n) = x1 + 10 ^ (m - S n) + 1)%nat. { omega. }
             rewrite H7 in *. clear H7.
             assert (x1 + 10 ^ (m - S n) = x2)%nat. 
             {
               apply NNPP. intro. apply nat_total_order in H7.
               destruct H7 ; apply lt_le_S in H7 ; rewrite <- Nat.add_1_r in H7 ; apply INR_le in H7 ;
               apply (Qlt_irrefl (x0 * (10 ^ m)%nat + (10 ^ (m - S n))%nat)).
               - apply Qlt_le_trans with (INR (x1+ 10 ^ (m - S n) +1)) ; auto.
                 apply Qle_trans with (INR x2); auto. 
               - apply Qlt_le_trans with (INR (x2 + 1)) ; auto.
                 apply Qle_trans with (INR (x1 + 10 ^ (m - S n)));  auto.
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
          ** apply Rle_ge in H3. apply Rle_ge.
             apply Rle_trans with (IQR x0) ; auto.
             apply IQR_le. rewrite <- Qplus_0_r at 1.
             apply Qplus_le_r.  apply Qle_shift_div_l.
             *** rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
             *** rewrite Qmult_0_l. rewrite INR_Qeq_1. lra.
          ** assert (Same_Ipart (IQR (x0 + 1%nat / (10 ^ S n)%nat)) (IQR x0)).
             {  apply  (Same_Ipart_mult _ _ (10 ^ n)).
                - apply Max_powan_0 ; omega.
                - destruct (archimedean_exists (IQR (x0 * INR (10 ^ n)))), H5.
                  exists x1.
                  repeat split ; repeat rewrite IQR_mult in * ; try (apply IQR_le) ; try (apply IQR_lt);
                  apply IQR_le in H5 ; apply IQR_lt in H6 ; auto ;
                  rewrite Qmult_plus_distr_l in * .
                  + apply Qle_trans with (x0 * (INR (10 ^ n)))%Q ; auto.
                    rewrite <- Qplus_0_r at 1.
                    apply Qplus_le_r.
                    rewrite INR_Qeq_1. unfold Qdiv. 
                    rewrite Qmult_1_l. apply Qmult_le_0_compat.
                    * apply Qinv_le_0_compat. rewrite <- INR_Qeq_0.
                      apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                    * rewrite <- INR_Qeq_0.
                      apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
                  + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
                    assert (INR(1) / INR(10^S n) * INR (10 ^ n) == INR (1) / INR(10) )%Q. 
                    { 
                      apply (Qmult_inj_r _ _ (INR 10)).
                      - intro. rewrite <- INR_Qeq_0 in H8. apply Qeq_INR_eq in H8. inversion H8.
                      - rewrite <- Qmult_assoc. rewrite INR_mult.  rewrite <- H7.
                        field. split ; intro.
                        + rewrite <- INR_Qeq_0 in H8. apply Qeq_INR_eq in H8. inversion H8.
                        + apply (Qlt_irrefl 0%Q). rewrite <- H8 at 2.
                          rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0 ; omega.
                    }
                    rewrite H8. 
                    specialize (H1 (S n)). destruct H1.
                    assert (S n > n)%nat. { omega. }
                    specialize (H9 H10). clear H10 H1.
                    hnf in H9. rewrite IQR_mult in *.
                    destruct H9,H1,H1.
                    apply IQR_le in H1. apply IQR_lt in H10.
                    symmetry in H9.
                    apply mod_exists in H9 ; try (omega) .
                    destruct H9.  rewrite plus_0_r in H9.
                    rewrite H7 in *. rewrite <- INR_mult in *.
                    rewrite Qmult_assoc in *.
                    subst x2.
                    rewrite mult_comm in *.
                    rewrite <- INR_plus in H10.
                    rewrite <- INR_mult in *.
                    assert (INR(10) > 0)%Q. { rewrite <- INR_Qeq_0. apply INR_lt. omega. }
                    apply Qmult_lt_0_le_reg_r in H1 ; auto.
                    assert (INR(1) == INR(1) / INR(10) * INR(10))%Q. { field. intro. rewrite H11 in H9. apply Qlt_irrefl in H9. auto. }
                    rewrite H11 in H10.
                    rewrite <- Qmult_plus_distr_l in H10.
                    apply Qmult_lt_r in H10 ; auto.
                    assert (x0 * (10 ^ n)%nat < x3 + 1%nat)%Q.
                    { apply Qlt_trans with (x3 + 1%nat / 10%nat)%Q ; auto.
                      apply Qplus_lt_r. rewrite INR_Qeq_1.
                      unfold Qdiv. rewrite Qmult_1_l.
                      apply Qlt_shift_inv_r ; auto.
                    }
                    assert (x3 = x1).
                    {
                      apply (Ipart_unique (IQR (x0 * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
                      rewrite <- INR_plus. auto.
                    }
                    subst.
                    apply Qlt_trans with (x1 + 1%nat / 10%nat + 1%nat / 10%nat)%Q.
                    * apply Qplus_lt_l. auto.
                    * rewrite <- INR_plus. rewrite <- Qplus_assoc.
                      apply Qplus_lt_r.
                      unfold Qdiv. rewrite <- Qmult_plus_distr_l.
                      rewrite INR_plus. simpl. rewrite INR_Qeq_1.
                      apply Qmult_lt_r with (INR (10)) ; auto.
             }
             destruct H5 , H5 , H6 , H7.
             assert (x1 + 1 <= 10)%nat.
             {
                apply NNPP.
                intro. 
                apply not_le in H9.
                assert (x1 >= 10)%nat. {omega. }
                apply (Rlt_irrefl (IQR (INR 10))).
                apply Rle_lt_trans with (IQR x0) ; auto.
                apply Rle_trans with (IQR x1) ; auto.
                apply IQR_le. apply INR_le. auto.
             }
             apply Rlt_le_trans with (IQR (x1 + 1)%nat) ; auto.
             apply IQR_le. apply INR_le. auto.
  Qed.
  
  Theorem partial_functional_NNP_T_NQP : forall (x : nat -> nat -> Prop) ,
                  InDec x -> partial_functional (NNP_T_NQP x).
  Proof.
    intros.
    hnf ; intros.
    destruct H0. destruct H1.
    apply IQR_eq. apply Dec_R_eq ; auto.
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
  
  Theorem Uncv_eqb_Uncv' : forall (x : nat -> Q -> Prop)(r : R) , Un_cv' x r <-> Un_cv (NQP_T_NRP x) r.
  Proof.
    split ; hnf in * ; intros.
    * repeat destruct H.
      split ; hnf ; intros.
      - split ; hnf ; intros.
        + destruct (H a). exists (IQR x0). hnf. exists x0 ; auto.
        + repeat destruct H2 , H3.
          apply IQR_eq. 
          apply (H1 a x0 x1) ; auto.
      - specialize (H0 eps H2).
        destruct H0.
        exists x0. intros.
        repeat destruct H4.
        apply (H0 m x1 H3 H5).
    * repeat destruct H.
      split ; hnf; intros.
      - split ; hnf ; intros.
        + destruct (H a). repeat destruct H2. exists x1. auto.
        + apply IQR_eq.
          apply (H1 a (IQR b1) (IQR b2)). 
          exists b1 ; auto.
          exists b2 ; auto.
      - specialize (H0 eps H2).
        destruct H0.
        exists x0. intros.
        apply (H0 m) ; auto.
        exists q ; auto.
  Qed.
  
  Definition mono_up_Q (X : nat -> Q -> Prop) : Prop := mono_up (NQP_T_NRP X). 
  Definition mono_down_Q (X : nat -> Q -> Prop) : Prop := mono_down (NQP_T_NRP X).
  Definition mono_Q (X : nat -> Q -> Prop) : Prop := mono_up_Q X \/ mono_down_Q X.
  Definition upper_bound_Q (X : nat -> Q -> Prop) (U : R) : Prop := upper_bound (NQP_T_NRP X) U.
  Definition Sup_Q (X : nat -> Q -> Prop) (sup : R) : Prop := Sup (NQP_T_NRP X) sup.
  Definition lower_bound_Q (X : nat -> Q -> Prop) (L : R) : Prop := lower_bound (NQP_T_NRP X) L.
  Definition Inf_Q (X : nat -> Q -> Prop) (inf : R) : Prop := Inf (NQP_T_NRP X) inf.
  Definition bound_Q (X : nat -> Q -> Prop) : Prop := bound (NQP_T_NRP X).

  Theorem Sup_pro_Q : forall (X : nat -> Q -> Prop) (sup : R) , is_function X -> Sup_Q X sup -> forall y : R , (y < sup -> 
                              (exists n : nat , forall q : Q , X n q -> ( IQR q <= sup /\ y < IQR q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0.
    apply Rlt_not_ge in H1.
    apply H1.
    apply Rle_ge.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    hnf in H6.
    destruct H6.
    destruct H6.
    destruct H3.
    assert (x = x0).
    { apply (H4 n) ; auto.  apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply (H5 n) ; auto.
      hnf. exists x0 ; auto.
    - apply Rle_not_gt. auto. 
  Qed.
  
  Theorem Inf_pro_Q : forall (X : nat -> Q -> Prop) (inf : R) , is_function X -> Inf_Q X inf -> forall y : R , (y > inf -> 
                              (exists n : nat , forall q : Q , X n q -> (IQR q >= inf /\ y > IQR q))).
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
    destruct H3.
    destruct H6. destruct H6.
    assert (x = x0).
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply Rle_ge. apply (H5 n); auto.
      hnf. exists x0 ; auto.
    - apply Rle_not_gt. auto.
  Qed.

  Theorem upper_bound_T_lower_bound_Q : forall (X P : nat -> Q -> Prop) , is_function X -> is_function P
                                                                     -> (forall n r , X n r <-> P n (-r)%Q) 
                                                                      -> forall r , upper_bound_Q X r <-> lower_bound_Q P (-r).
  Proof.
    intros.
    split ; intros.
    - hnf. intros.
      destruct H3. destruct H3.
      specialize (H1 n (-x)%Q).
      assert (IQR (- - x) = - - q).
      { rewrite <- !Ropp_IQR. rewrite H3. auto. }
      rewrite <- Ropp_opp in H5.
      destruct (H2 n (IQR (-x))). 
      + hnf. exists (-x)%Q. split ; auto.
        apply H1. 
        rewrite <- H3 in H5. 
        apply IQR_eq in H5.
        rewrite H5; auto.
      + rewrite <- Ropp_IQR in H6. rewrite H3 in H6.
        apply Rle_lt_weak in H6.
        rewrite Ropp_opp.
        apply Rle_opp_eqb. rewrite <- Ropp_opp. auto.
      + rewrite <-H6. rewrite <- H5.
        rewrite Ropp_IQR. apply Rle_refl.
    - hnf. intros.
      destruct H3. destruct H3.
      specialize (H1 n x).
      rewrite H1 in H4.
      assert (NQP_T_NRP P n (IQR (- x))).
      { hnf. exists (-x)%Q. auto. }
      specialize (H2 n (IQR (-x)) H5).
      rewrite <- Ropp_IQR in H2.
      rewrite H3 in H2.
      rewrite Ropp_opp. apply Rle_opp_eqb ; auto.
  Qed.
  
  Theorem upper_bound_exists_Sup_Q : forall (X : nat -> Q -> Prop) , is_function X -> (exists r : R , upper_bound_Q X r) ->
                                          (exists sup : R , Sup_Q X sup).
  Proof.
    intros.
    assert (exists sup : R , Sup (NQP_T_NRP X) sup).
    {
      destruct H.
      apply upper_bound_exists_Sup.
      - split; hnf ; intros.
        + destruct (H a). exists (IQR x). exists x ; auto.
        + repeat destruct H2 , H3. apply IQR_eq. apply (H1 a) ; auto.
      - destruct H0.
        exists x.
        hnf ; intros.
        repeat destruct H2.
        apply (H0 n). exists x0 ; auto.
    }
    auto.
  Qed.
  
  Theorem lower_bound_exists_Inf_Q : forall (X : nat -> Q -> Prop) , is_function X -> (exists r : R , lower_bound_Q X r) ->
                                          (exists inf : R , Inf_Q X inf).
  Proof.
   intros.
    assert (exists inf : R , Inf (NQP_T_NRP X) inf).
    {
      destruct H.
      apply lower_bound_exists_Inf.
      - split; hnf ; intros.
        + destruct (H a). exists (IQR x). exists x ; auto.
        + repeat destruct H2 , H3. apply IQR_eq. apply (H1 a) ; auto.
      - destruct H0.
        exists x.
        hnf ; intros.
        repeat destruct H2.
        apply (H0 n). exists x0 ; auto.
    }
    auto.
  Qed.
  
  Theorem Sup_unique_Q : forall (X : nat -> Q -> Prop) (r1 r2 : R), Sup_Q X r1 -> Sup_Q X r2 -> r1 = r2.
  Proof. 
    intros.
    unfold Sup_Q in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; apply Rle_ge ; auto.
  Qed.

  Theorem Inf_unique_Q : forall (X : nat -> Q -> Prop) (r1 r2 : R), Inf_Q X r1 -> Inf_Q X r2 -> r1 = r2.
  Proof.
    intros.
    unfold Inf_Q in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; auto.
  Qed.

  Theorem mono_up_upper_bound_seq_has_limit_Q : forall (X : nat -> Q -> Prop) , mono_up_Q X -> (exists r : R , upper_bound_Q X r) -> exists r : R ,Un_cv' X r.
  Proof. 
    intros.
    pose proof mono_up_upper_bound_seq_has_limit (NQP_T_NRP X) H H0.
    destruct H1.
    exists x.
    apply Uncv_eqb_Uncv' ; auto.
  Qed. 
  
  Theorem mono_up_limit_sup_Q : forall (X : nat -> Q -> Prop) , mono_up_Q X -> (exists r : R , upper_bound_Q X r) -> forall r : R , Un_cv' X r -> Sup_Q X r.
  Proof.
    intros.
    apply (mono_up_limit_sup (NQP_T_NRP X) H H0 r).
    apply Uncv_eqb_Uncv'. auto.
  Qed.
  
  Theorem mono_down_lower_bound_seq_has_limit_Q : forall (X : nat -> Q -> Prop) , mono_down_Q X -> (exists r : R , lower_bound_Q X r) -> exists r : R , Un_cv' X r.
  Proof.
    intros.
    pose proof mono_down_lower_bound_seq_has_limit (NQP_T_NRP X) H H0.
    destruct H1.
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
  
  Theorem Dec_R2_bound : forall (x : nat -> nat -> Prop) , InDec x -> upper_bound (NQP_T_NRP (NNP_T_NQP x)) R2.
  Proof.
    intros. hnf. intros.
    destruct H. destruct H0. destruct H0. subst.
    destruct H2.
    left.
    apply Dec_R_lt.
    * apply H2.
    * split.
      - unfold R2 ; rewrite <- IQR_R1 ; rewrite IQR_plus. rewrite <- IQR_R0. apply Rle_ge. apply IQR_le.  lra.
      - apply R2_Rlt_R10.
    * exists O.
      split ; intros.
      - pose proof Two_Dec.
        assert (m2 = 2 %nat). { apply (partial_functional_Dec_R R2 O) ; auto. }
        subst. 
        specialize (H0 O). destruct H0.
        assert (0 <= n)%nat. { omega. }
        specialize (H0 H7).
        apply H0 in H3.
        destruct (H O).
        + assert (m1 = 0)%nat. { apply (H1 O) ; auto. }
          subst. auto.
        + assert (m1 = 1)%nat. { apply (H1 O) ; auto. }
          subst. auto.
      - inversion H3.
  Qed.
   
  Theorem Dec_upper_bound : forall (D : Dec) , exists r : R , upper_bound_Q (NNP_T_NQP (proj1_sig D)) r.
  Proof.
    destruct D.
    simpl.
    exists R2.
    apply Dec_R2_bound. 
    auto.
  Qed.
  
  Theorem Dec_mono_up : forall (D : Dec) , mono_up_Q (NNP_T_NQP (proj1_sig D)).
  Proof.
    destruct D , i.
    assert (forall n1 x1 x2 , (NNP_T_NQP x) n1 x1 -> (NNP_T_NQP x) n1 x2 -> x1 = x2).
    {
      intros.
      apply IQR_eq. apply Dec_R_eq ; intros.
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
    - split ; hnf ; simpl in * ; intros.
      + assert (exists q , (NNP_T_NQP x) a q). { apply image_defined_NNP_T_NQP . split ; auto. }
        destruct H0. exists (IQR x0). exists x0. auto.
      + repeat destruct H0 , H1.
        apply IQR_eq.
        apply (H a) ; auto.
    - simpl in *.
      repeat destruct H0 , H1.
      apply Rle_ge.
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
      + specialize (H4 H8 O).
        pose proof (le_trans x2 n1 n H8 H2).
        specialize (H3 H9 O).
        apply (lt_irrefl O).
        apply H0.
        * rewrite H3 ; auto.
        * rewrite H4 ; auto.
      + apply not_le in H8.
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
      + specialize (H4 H8 1%nat).
        pose proof (le_trans x2 n1 n H8 H2).
        specialize (H3 H9 1%nat).
        apply (lt_irrefl 1%nat).
        apply H0.
        * rewrite H3 ; auto.
        * rewrite H4 ; auto.
      + apply not_le in H8.
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
      + apply H3.
      + apply H4.
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
    assert (IQR (INR (1) / INR (10 ^ (S n))) > R0).
    { rewrite <- IQR_R0. apply IQR_lt. apply Qlt_shift_div_l.
      - rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
      - rewrite Qmult_0_l. rewrite INR_Qeq_1. lra.
    }
    specialize (H2 (IQR (INR (1) / INR (10 ^ (S n)))) H5).
    clear H5. destruct H2.
    remember (max x0 (S n)) as p.
    destruct (H0 p).
    assert (p >= x0)%nat. { subst. apply Nat.le_max_l. }
    specialize (H2 p x1 H6 H5).
    destruct H1 , H3.
    hnf in H8.
    assert (IQR x1 <= r). { apply (H8 p). exists x1. split ; auto. }
    apply Rle_ge in H9 as goal.
    rewrite Rle_neg_eqb in goal.
    apply Rabs_neg in goal.
    rewrite Ropp_minus in goal.
    rewrite goal in H2. clear goal.
    apply Rlt_Rminus_Rplus in H2.
    destruct H5. clear H10.
    pose proof (H5 n).
    pose proof (H5 (S n)).
    destruct H10 , H11.
    assert (S n <= p)%nat. {subst . apply Nat.le_max_r. } 
    assert (n <= p)%nat. { omega. }
    specialize (H10 H15). specialize (H11 H14). 
    clear H14 H15 H13 H12 H3 H8 H7.
    destruct H. rewrite IQR_plus in *.
    destruct (archimedean_exists (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat)) , H7 .
    destruct (archimedean_exists (IQR x1 * IQR (10 ^ n)%nat)) , H12.
    assert (Same_Ipart (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat) ((IQR x1 * IQR (10 ^ n)%nat))).
    {
       exists x3.
       repeat split ; repeat rewrite IQR_mult in * ; try (apply IQR_le) ; try (apply IQR_lt);
       apply IQR_le in H12 ; apply IQR_lt in H13 ; auto ;
       rewrite Qmult_plus_distr_l in *.
       + apply Qle_trans with (x1 * (INR (10 ^ n)))%Q ; auto.
         rewrite <- Qplus_0_r at 1.
         apply Qplus_le_r.
         rewrite INR_Qeq_1. unfold Qdiv. 
         rewrite Qmult_1_l. apply Qmult_le_0_compat.
         * apply Qinv_le_0_compat. rewrite <- INR_Qeq_0.
           apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
         * rewrite <- INR_Qeq_0.
           apply INR_le. apply Nat.lt_le_incl. apply Max_powan_0 ; omega.
       + assert (10 ^ S n = 10 ^ n * 10)%nat. { rewrite mult_comm. apply Nat.pow_succ_r. omega. }
         assert (INR(1) / INR(10^S n) * INR (10 ^ n) == INR (1) / INR(10) )%Q. 
         { 
           apply (Qmult_inj_r _ _ (INR 10)).
           - intro. rewrite <- INR_Qeq_0 in H15. apply Qeq_INR_eq in H15. inversion H15.
           - rewrite <- Qmult_assoc. rewrite INR_mult.  rewrite <- H14.
             field. split ; intro.
             + rewrite <- INR_Qeq_0 in H15. apply Qeq_INR_eq in H15. inversion H15.
             + apply (Qlt_irrefl 0%Q). rewrite <- H15 at 2. 
               rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0 ; omega.
         }
         rewrite H15. clear H15 H1 H0.
         specialize (H (S n)).
         destruct H ; rewrite <- H11 in H ; destruct H , H , H ;  rewrite IQR_mult in *;
         apply IQR_le in H ; apply IQR_lt in H1; symmetry in H0 ; apply mod_exists in H0 ; try (omega);
         destruct H0.
         - rewrite plus_0_r in H0.
           rewrite H14 in H , H1. rewrite <- INR_mult in *.
           rewrite Qmult_assoc in *.
           subst x4.
           rewrite mult_comm in H , H1.
           rewrite <- INR_plus in H1.
           rewrite <- INR_mult in *.
           assert (INR(10) > 0)%Q. { rewrite <- INR_Qeq_0. apply INR_lt. omega. }
           apply Qmult_lt_0_le_reg_r in H ; auto.
           assert (INR(1) == INR(1) / INR(10) * INR(10))%Q. { field. intro. rewrite H15 in H0. apply Qlt_irrefl in H0. auto. }
           rewrite H15 in H1.
           rewrite <- Qmult_plus_distr_l in H1.
           apply Qmult_lt_r in H1 ; auto.
           assert (x1 * (10 ^ n)%nat < x5 + 1%nat)%Q.
           { apply Qlt_trans with (x5 + 1%nat / 10%nat)%Q ; auto.
             apply Qplus_lt_r. rewrite INR_Qeq_1.
             unfold Qdiv. rewrite Qmult_1_l.
             apply Qlt_shift_inv_r ; auto.
           }
           assert (x3 = x5).
           {
             apply (Ipart_unique (IQR (x1 * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
             rewrite <- INR_plus. auto.
           }
           subst.
           apply Qlt_trans with (x5 + 1%nat / 10%nat + 1%nat / 10%nat)%Q.
           * apply Qplus_lt_l. auto.
           * rewrite <- INR_plus. rewrite <- Qplus_assoc.
             apply Qplus_lt_r.
             unfold Qdiv. rewrite <- Qmult_plus_distr_l.
             rewrite INR_plus. simpl. rewrite INR_Qeq_1.
             apply Qmult_lt_r with (INR (10)) ; auto.
         - rewrite H14 in H , H1. rewrite <- INR_mult in *.
           rewrite Qmult_assoc in *.
           subst x4.
           rewrite mult_comm in H , H1.
           rewrite <- plus_assoc in H1. simpl in H1.
           rewrite <- INR_plus in *.
           rewrite <- INR_mult in *.
           assert (INR(10) > 0)%Q. { rewrite <- INR_Qeq_0. apply INR_lt. omega. }
           assert (INR(1) == INR(1) / INR(10) * INR(10))%Q. { field. intro. rewrite H15 in H0. apply Qlt_irrefl in H0. auto. }
           assert (INR(2) == INR(2) / INR(10) * INR(10))%Q. { field. intro. rewrite H16 in H0. apply Qlt_irrefl in H0. auto. }
           rewrite H15 in H. rewrite H16 in H1.
           rewrite <- Qmult_plus_distr_l in H1 , H.
           apply Qmult_lt_r in H1 ; auto.
           apply Qmult_le_r in H ; auto.
           assert (x1 * (10 ^ n)%nat < x5 + 1%nat)%Q.
           { apply Qlt_trans with (x5 + 2%nat / 10%nat)%Q ; auto.
             apply Qplus_lt_r. rewrite INR_Qeq_1.
             unfold Qdiv.
             apply Qmult_lt_r with (INR (10)) ; auto.
           }
           assert (x3 = x5).
           {
             apply (Ipart_unique (IQR (x1 * (10 ^ n)%nat))) ; split ; try (apply IQR_le) ; try (apply IQR_lt) ; auto.
             - rewrite <- INR_plus. auto.
             - apply Qle_trans with (x5 + 1%nat / 10%nat)%Q ; auto.
               rewrite <- Qplus_0_r at 1.
               apply Qplus_le_r. unfold Qdiv.
               rewrite INR_Qeq_1. rewrite Qmult_1_l.
               apply Qinv_le_0_compat. apply Qlt_le_weak. auto.
             - rewrite <- INR_plus ; auto.
           }
           subst.
           apply Qlt_trans with (x5 + 2%nat / 10%nat + 1%nat / 10%nat)%Q.
           * apply Qplus_lt_l. auto.
           * rewrite <- Qplus_assoc.
             apply Qplus_lt_r.
             unfold Qdiv. rewrite <- Qmult_plus_distr_l.
             rewrite INR_plus. simpl. rewrite INR_Qeq_1.
             apply Qmult_lt_r with (INR (10)) ; auto.
    }
    destruct H14.
    rewrite <- H10.
    destruct H14 , H15 ,  H16.
    assert (IQR x4 <= r * IQR (10 ^ n)%nat).
    {
      apply Rle_trans with (IQR x1 * IQR (10 ^ n)%nat) ; auto.
      apply Rmult_le_r ; auto.
      rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0.
      apply INR_lt. apply Max_powan_0. omega.
    }
    assert (r * IQR(10 ^ n)%nat < IQR (x4 + 1)%nat).
    {
      apply Rlt_trans with (IQR (x1 + 1%nat / (10 ^ S n)%nat) * IQR (10 ^ n)%nat) ; auto.
      apply Rmult_lt_r ; auto.
      rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0.
      apply INR_lt. apply Max_powan_0. omega.
    }
    clear H0 H4 H2 H1 H5 H9 H10 H11 H7 H8 H12 H13.
    split ; intros ; hnf in *  ; destruct H0 , H0, H0.
    - destruct (archimedean_exists (IQR x1 * IQR (10 ^ n)%nat)). exists x6. split ; auto.
      assert (x4 = x5)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; auto. }
      assert (x4 = x6)%nat. { apply (Ipart_unique (IQR x1 * IQR (10 ^ n)%nat)) ; auto. }
      subst ; auto.
    - destruct (archimedean_exists (r * IQR (10 ^ n)%nat)). exists x6. split ; auto.
      assert (x4 = x6)%nat. { apply (Ipart_unique (r * IQR (10 ^ n)%nat)) ; auto. }
      assert (x4 = x5)%nat. { apply (Ipart_unique (IQR x1 * IQR (10 ^ n)%nat)) ; auto. }
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
      assert (upper_bound (NQP_T_NRP P) R2).
      {
        apply Dec_R2_bound. auto.
      }
      split .
      + subst P.
        destruct H1 , H1 , (H1 O).
        assert ((NQP_T_NRP (NNP_T_NQP x)) O (IQR x1)).
        {
          exists x1.
          split ; auto.
        }
        specialize (H3 O (IQR x1) H8).
        apply Rle_ge.
        apply Rle_trans with (IQR x1) ; auto.
        destruct H7 , H9.
        apply Rle_ge. auto.
     + apply Rle_lt_trans with R2.
       * apply Rle_ge. apply H2. auto.
       * apply R2_Rlt_R10.
  Qed.

  Theorem partial_functional_Dec_r : partial_functional Dec_r.
  Proof. 
    unfold partial_functional ,  Dec_r .
    intros.
    destruct H , H0.
    apply Dec_R_eq ; intros ; auto.
    pose proof H j m.
    pose proof H0 j m.
    tauto.
  Qed.

  Theorem injective_Dec_r : injective Dec_r.
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
  
  Theorem Equiv_R_DecR : Countable R -> Countable Dec.
  Proof.
    intros.
    destruct X.
    pose proof image_defined_Dec_r.
    pose proof partial_functional_Dec_r.
    pose proof injective_Dec_r.
    set (fun (D : Dec) (n : nat) => exists r : R , Dec_r D r /\ inj_R r n).
    exists P ; subst P ; hnf in *; intros.
    -  destruct (H a).
       destruct (im_inj x).
       exists x0 , x. split ; auto.
    -  destruct H2 , H3. destruct H2 , H3.
       assert (x = x0).  { apply (H0 a); auto. }
       subst .
       apply (pf_inj x0) ; auto.
    -  destruct H2 , H3. destruct H2 , H3.
       assert (x = x0).  { apply (in_inj _ _ b) ; auto. }
       subst .
       apply (H1 _ _ x0) ; auto.
  Qed.
  
  Theorem UnCountable_DecR : Countable Dec -> False.
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
  
  Theorem UnCountable_R : Countable R -> False.
  Proof.
    intros.
    apply UnCountable_DecR.
    apply Equiv_R_DecR ; auto.
  Qed.
  
  Theorem Dec_Q : forall (q : Q) (n:nat) , (R0 <= IQR q) -> {Dec_R (IQR q) n 0} + {~Dec_R (IQR q) n 0}.
  Proof.
    intros.
    set (Z.to_nat (Qfloor (q * INR (10 ^ n)))).
    assert (archimedean n0 (IQR q * IQR (10 ^ n)%nat)).
    {
      rewrite IQR_mult.
      remember (q * (10 ^ n)%nat)%Q as q0.
      assert (q0 < inject_Z (Qfloor q0 + 1))%Q. { apply Qlt_floor. }
      split.
      + apply IQR_le. subst n0.
        unfold INR. rewrite Z2Nat.id.
        apply Qfloor_le.
        assert (Qfloor 0%Q = 0)%Z. { auto. }
        rewrite <- H1.
        apply Qfloor_resp_le.
        rewrite <- IQR_R0 in H. apply IQR_le in H.
        apply Qle_trans with q ; auto. 
        subst. rewrite <- Qmult_1_r at 1.
        apply Qle_lt_or_eq in H. destruct H.
        * apply Qmult_le_l ; auto.
           rewrite <- INR_Qeq_1. apply INR_le. apply Max_powan_0. omega.
        * rewrite <- H. lra.
      + apply IQR_lt. apply Qlt_le_trans with (inject_Z (Qfloor q0 + 1)) ; auto.
        subst n0.
        apply Qle_trans with (Z.to_nat (Qfloor q0 + 1)).
        * apply Z_to_nat_le.
        * rewrite Z2Nat.inj_add ; try (omega).
          apply INR_le. auto.
          assert (Qfloor 0%Q = 0)%Z. { auto. }
          rewrite <- H1.
          apply Qfloor_resp_le.
          rewrite <- IQR_R0 in H. apply IQR_le in H.
          apply Qle_trans with q ; auto. 
          subst. rewrite <- Qmult_1_r at 1.
          apply Qle_lt_or_eq in H. destruct H.
          - apply Qmult_le_l ; auto.
             rewrite <- INR_Qeq_1. apply INR_le. apply Max_powan_0. omega.
          - rewrite <- H. lra.
    }
    destruct (n0 mod 10) eqn : En.
    - left. exists n0.
      split ; auto.
    - right. intro.
      destruct H1 , H1 , H1 , H0.
      rewrite IQR_mult in *.
      assert (n0 = x). { apply (Ipart_unique (IQR (q * (10 ^ n)%nat))) ; auto. }
      subst.
      rewrite En in H2.
      inversion H2.
  Qed.
  
End DEC_R.