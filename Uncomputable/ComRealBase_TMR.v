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
From CReal Require Import INR_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import Uncomputable.ComRealBase.
From CReal Require Import Uncomputable.ComRealBase_Dec.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
Import TM_u_u.

Module TMR_Set (R : VIR_R).
  Module RLemmas := VirRLemmas (R).
  Module Dec := DEC_R (R).
  Include VIR_R_EXTRA R.
  Import R RLemmas Dec.
  Local Open Scope R_scope.

  Definition limit : (nat -> Q) -> R -> Prop.
    intros.
    set (fun n q => q = H n).
    apply (Un_cv' P X).
  Defined.
  
  Definition Un_cv : (nat -> R) -> R -> Prop.
    intros.
    set (fun n r => r = X n).
    apply (Un_cv P X0).
  Defined.
  
  Definition TMR : nat -> R -> Prop.
    intros n r.
    apply ((forall m : nat , Dec_R r m (Nat.b2n(TM n m))) /\ In_Search r).
  Defined.
  
  Theorem image_Defined_TMR : image_defined TMR.
  Proof.
    hnf ; intros.
    set (fun n m => Nat.b2n (TM a n) = m).
    assert (InDec P).
    {
      subst P. split .
      - intros. destruct (TM a x) ; auto.
      - intros. subst. auto. 
    }
    set (NNP_Dec P H).
    destruct (image_defined_Dec_r d).
    destruct H0.
    exists x.
    split ; auto.
    intros.
    apply H0.
    simpl. reflexivity.
  Qed.
  
  Theorem injective_TMR : injective TMR.
  Proof.
    hnf ; intros.
    destruct H,  H0.
    apply TMuu_eqb. intros.
    specialize (H j).
    specialize (H0 j).
    apply Nat.b2n_inj. 
    apply (partial_functional_Dec_R b j) ; auto.
  Qed.
  
  Theorem partial_functional_TMR : partial_functional TMR.
  Proof.
    hnf ; intros.
    destruct H , H0.
    apply Dec_R_eq ; auto.
    intros. specialize (H j). specialize (H0 j).
    split ; intros.
    + assert (m = Nat.b2n (TM a j)). { apply (partial_functional_Dec_R b1 j) ; auto. }
      subst. auto.
    + assert (m = Nat.b2n (TM a j)). { apply (partial_functional_Dec_R b2 j) ; auto. }
      subst. auto.
  Qed.
  
  Definition Get_TMR : nat -> R.
    intros n.
    pose proof (image_Defined_TMR n).
    apply Rsinglefun.
    exists (TMR n).
    split ; intros. 
    - apply (partial_functional_TMR n) ; auto.
    - split ; auto. 
      hnf. intros. hnf in H0. subst. reflexivity.
  Defined.
  
  Theorem TMR_get : forall n : nat , TMR n (Get_TMR n).
  Proof.
    intros.
    apply (Rsinglefun_correct (TMR n)).
  Qed.
  
  Definition TMr : nat -> R -> Prop.
    intros n r.
    apply ((forall m : nat , Dec_R r m (Nat.b2n(TM m n))) /\ In_Search r).
  Defined.
  
  Theorem image_Defined_TMr : image_defined TMr.
  Proof.
    hnf ; intros.
    set (fun n m => Nat.b2n (TM n a) = m).
    assert (InDec P).
    {
      subst P. split .
      - intros. destruct (TM x a) ; auto.
      - intros. subst. auto. 
    }
    set (NNP_Dec P H).
    destruct (image_defined_Dec_r d).
    destruct H0.
    exists x.
    split ; auto.
    intros.
    apply H0.
    simpl. reflexivity.
  Qed.

  Theorem partial_functional_TMr : partial_functional TMr.
  Proof.
    hnf ; intros.
    destruct H , H0.
    apply Dec_R_eq ; auto.
    intros. specialize (H j). specialize (H0 j).
    split ; intros.
    + assert (m = Nat.b2n (TM j a)). { apply (partial_functional_Dec_R b1 j) ; auto. }
      subst. auto.
    + assert (m = Nat.b2n (TM j a)). { apply (partial_functional_Dec_R b2 j) ; auto. }
      subst. auto.
  Qed.
  
  Definition TM'r : nat -> R.
    intros n.
    pose proof (image_Defined_TMr n).
    apply Rsinglefun.
    exists (TMr n).
    split ; intros. 
    - apply (partial_functional_TMr n) ; auto.
    - split ; auto. 
      hnf. intros. hnf in H0. subst. reflexivity.
  Defined.
  
  Theorem TMr_get : forall n : nat , TMr n (TM'r n).
  Proof.
    intros.
    apply (Rsinglefun_correct (TMr n)).
  Qed.
  
  Theorem TM'r_pro : forall (n m: nat), Dec_R (TM'r n) m (Nat.b2n(TM m n)).
  Proof.
    intros.
    pose proof TMr_get n.
    destruct H. auto.
  Qed.
  
  Theorem In_Search_TM'r : forall n : nat , In_Search (TM'r n).
  Proof.
    intros.
    pose proof TMr_get n.
    destruct H. auto.
  Qed.

  Theorem Ex_limit_of_TM'r : exists r : R , Un_cv TM'r r.
  Proof.
    apply mono_up_upper_bound_seq_has_limit.
    - split ; hnf ; intros.
      + split ; hnf ; intros.
        * exists (TM'r a). auto.
        * subst. auto.
      + pose proof In_Search_TM'r. subst.
        apply Dec_R_ge ; auto.
        intros.
        pose proof TM'r_pro n n0.
        pose proof TM'r_pro n1 n0.
        assert (m1 = Nat.b2n (TM n0 n)). { apply (partial_functional_Dec_R (TM'r n) n0); auto. }
        assert (m2 = Nat.b2n (TM n0 n1)). { apply (partial_functional_Dec_R (TM'r n1) n0); auto. }
        subst. clear H H0 H3 H4.
        destruct (TM n0 n1) eqn : En.
        * assert (TM n0 n = true). { apply (Turing_mono n0 n1 n) ; auto. }
          rewrite H. omega.
        * destruct (TM n0 n) ; simpl ; omega.
    - exists (IQR (10%nat)).
      hnf. intros.
      subst. destruct (In_Search_TM'r n).  apply Rle_lt_weak. auto.
  Qed.
  
  Definition limitTM'r : R.
    apply Rsinglefun.
    exists (Un_cv TM'r).
    split ; intros.
    - unfold Un_cv in *.
      apply (Un_cv_inject (fun (n : nat) (r : R) => r = TM'r n)) ; auto.
    - split .
      + apply Ex_limit_of_TM'r.
      + hnf. intros. destruct H. reflexivity.
  Defined.
   
  Theorem limit_of_TM'r : Un_cv TM'r limitTM'r.
  Proof.
    apply (Rsinglefun_correct (Un_cv TM'r)).
  Qed.

  Theorem Sup_of_TM'r : forall n : nat , limitTM'r >= TM'r n.
  Proof.
    intro.
    set (fun (n : nat)(r : R) => r = TM'r n).
    assert (mono_up P).
    { subst P. 
      split ; hnf ; intros.
      + split ; hnf ; intros.
        * exists (TM'r a). auto.
        * subst. auto.
      + pose proof In_Search_TM'r. subst.
        apply Dec_R_ge ; auto.
        intros.
        pose proof TM'r_pro n0 n2.
        pose proof TM'r_pro n1 n2.
        assert (m1 = Nat.b2n (TM n2 n0)). { apply (partial_functional_Dec_R (TM'r n0) n2); auto. }
        assert (m2 = Nat.b2n (TM n2 n1)). { apply (partial_functional_Dec_R (TM'r n1) n2); auto. }
        subst. clear H H0 H3 H4.
        destruct (TM n2 n1) eqn : En.
        * assert (TM n2 n0 = true). { apply (Turing_mono n2 n1 n0) ; auto. }
          rewrite H. omega.
        * destruct (TM n2 n0) ; simpl ; omega.
    }
    assert (exists r : R , upper_bound P r).
    { subst P. exists (IQR (10%nat)).
      hnf. intros.
      subst. destruct (In_Search_TM'r n0).  apply Rle_lt_weak. auto.
    }
    pose proof limit_of_TM'r.
    pose proof mono_up_limit_sup P H H0 limitTM'r H1.
    destruct H2.
    hnf in H3.
    subst P. simpl in H3.
    apply Rle_ge. apply (H3 n). auto.
  Qed.
  
  Theorem TMR_proper0 : forall (n:nat) (r:R) , TMR n r -> forall (j : nat), (Dec_R r j 1 -> TM n j = true) /\ (Dec_R r j 0 -> TM n j = false).
  Proof.
    intros. 
    destruct H.
    destruct (TM n j) eqn : H1; split ; auto ; intros ; pose proof H j ; 
    rewrite H1 in H3 ;  simpl in * ; 
    assert (1 = 0)%nat ;  try (apply (partial_functional_Dec_R r j) ; auto ) ; 
    inversion H4.
  Qed.

  Theorem TMR_proper1 : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Dec_R r j 1) -> (Dec_R r k 1)).
  Proof.
    intros.
    pose proof H.
    destruct H.
    pose proof H k.
    assert (H' : TM n j = true).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n k = true).
    { apply Turing_mono with j ; auto. }
    rewrite H'' in H4. apply H4.
  Qed.

  Theorem TMR_proper1' : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Dec_R r k 0) -> (Dec_R r j 0)).
  Proof.
    intros.
    pose proof H.
    destruct H.
    pose proof H j.
     assert (H' : TM n k = false).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n j = false).
    { apply Turing_mono' with k ; auto. }
    rewrite H'' in H4. apply H4.
  Qed.

  Theorem diffR_diffTMR : forall (n1 n2 : nat) (r1 r2 : R) , TMR n1 r1 -> TMR n2 r2 -> (r1 <> r2 <-> n1 <> n2).
  Proof.
    intros.
    pose proof injective_TMR.
    pose proof partial_functional_TMR.
    hnf in *.
    unfold not.
    split.
    - intros.
      subst. apply H3.
      apply (H2 n2 r1 r2) ; auto.
    - intros.
      subst. apply H3. apply (H1 n1 n2) in H0; auto.
  Qed.
  
  Theorem TM'r_pro0 : forall (n m : nat), Dec_R (TM'r n) m 1 <-> TM m n = true.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R (TM'r n) m) ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r_pro0' : forall (n m : nat), Dec_R (TM'r n) m 0 <-> TM m n = false.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R (TM'r n) m) ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r_InDecR : forall n : nat , InDecR (TM'r n).
  Proof.
    intros. intro.
    destruct (TM n0 n) eqn : En.
    - right. apply TM'r_pro0. auto.
    - left. apply TM'r_pro0'. auto. 
  Qed.
  
  Theorem TM'r_pro1 : forall (n m : nat) , Dec_R (TM'r n) m 1 -> (forall (r : nat) , (r >= n)%nat -> Dec_R (TM'r r) m 1).
  Proof.
    intros.
    apply TM'r_pro0 in H.
    apply TM'r_pro0.
    pose proof Turing_mono m n r.
    apply H1 ; auto.
  Qed.
  
  Theorem TM'r_pro1' : forall (n m : nat) , Dec_R (TM'r n) m 0 -> (forall (r : nat) , (r <= n)%nat -> Dec_R (TM'r r) m 0).
  Proof.
    intros.
    apply TM'r_pro0' in H.
    apply TM'r_pro0'.
    pose proof Turing_mono' m n r.
    apply H1 ; auto.
  Qed.

  Theorem limitTM'r_pro0 : InDecR limitTM'r.
  Proof.
    hnf.
    apply NNPP.
    intro.
    apply not_all_ex_not in H.
    destruct H.
    apply not_or_and in H.
    destruct H.
    destruct (image_Defined_Dec_R limitTM'r x). 
    assert (x0 <> 0 /\ x0 <> 1)%nat. { split ; intro ; subst ; auto. }
    assert (x0 > 1)%nat. { omega. }
    clear H2 H H0. 
    pose proof limit_of_TM'r.
    pose proof TM'r_InDecR.
    destruct H. 
    assert (~ (10 ^ S x)%nat == 0)%Q.
    { intro. apply (Qlt_irrefl 0%Q). rewrite <- H4 at 2. rewrite <- INR_Qeq_0.
      apply INR_lt. apply Max_powan_0. omega.
    }
    assert (IQR 1 / IQR (10 ^ S x)%nat > R0).
    { unfold Rdiv. rewrite IQR_inv ; auto. rewrite IQR_mult.
      rewrite <- IQR_R0. apply IQR_lt. rewrite Qmult_1_l.
      apply Qinv_lt_0_compat.
      rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
    }
    specialize (H2 _ H5). destruct H2.
    assert (max (S x) x1 >= x1)%nat. { apply Nat.le_max_r. }
    assert (TM'r (max (S x) x1) = TM'r (max (S x) x1)). { auto. }
    specialize (H2 _ _ H6 H7).
    clear H7.
    specialize  (H0 (max (S x) x1) x).
    pose proof Sup_of_TM'r (max (S x) x1).
    remember (TM'r (max (S x) x1)) as r2.
    apply Rle_neg_eqb in H7.
    rewrite Rabs_neg in H2 ; auto.
    rewrite Ropp_minus in H2.
    apply Rle_neg_eqb in H7.
    apply Rle_ge in H7.
    assert (IQR (10 ^ x)%nat > R0).
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega. }
    apply Rmult_le_r with (r3 := IQR (10 ^ x)%nat) in H7 ; auto.
    apply Rmult_lt_r with (r3 := IQR (10 ^ x)%nat) in H2 ; auto.
    rewrite Rmult_minus_distr_r in H2.
    apply Rlt_Rminus_Rplus in H2.
    assert (IQR 1 / IQR (10 ^ S x)%nat * IQR (10 ^ x)%nat = IQR 1 / IQR (10)%nat ).
    {
      unfold Rdiv. 
      rewrite IQR_R1. rewrite !Rmult_1_l.
      assert (IQR (10 ^ S x)%nat = IQR (10 ^ x)%nat * IQR (10)%nat).
      { rewrite IQR_mult.
        apply NNPP. intro.
        apply Rnot_eq_lt in H9. 
        destruct H9 ; apply IQR_lt in H9 ; rewrite INR_mult in H9 ; apply INR_lt in H9;
        rewrite Nat.pow_succ_r' in H9 ; rewrite mult_comm in H9 ; omega.
      }
      rewrite H9.
      rewrite Rinv_mult. rewrite Rmult_comm.
      rewrite <- Rmult_assoc.
      rewrite Rinv_self. rewrite Rmult_1_l. auto.
      apply Rnot_eq_lt. auto.
    }
    rewrite H9 in *. 
    destruct H0 , H0 , H0 , H0 , H1 , H1 , H1.
    - assert (x2 <= x3)%nat.
      { apply NNPP. intro.
        assert (x3 + 1<= x2)%nat. { omega. }
        apply INR_le in H15. apply IQR_le in H15.
        apply (Rlt_irrefl (IQR x2)).
        apply Rle_lt_trans with (r2 * IQR (10 ^ x)%nat) ; auto.
        apply Rle_lt_trans with (limitTM'r * IQR (10 ^ x)%nat) ; auto.
        apply Rlt_le_trans with (IQR (x3 + 1)%nat) ; auto.
      }
      assert (x0 < 10)%nat. { rewrite H12. apply Nat.mod_upper_bound. auto. }
      symmetry in H12 , H10.
      apply mod_exists in H12 ; auto. apply mod_exists in H10 ; try (omega).
      destruct H12 , H10.
      assert (x3 >= x2 + 1 + 1)%nat. { omega. }
      pose proof Rle_lt_trans _ _ _ H1 H2.
      apply Rlt_Rplus_r with (r3 := IQR 1 / IQR 10%nat) in H11.
      pose proof Rlt_trans _ _ _ H17 H11.
      apply (Rlt_irrefl (IQR (x2 + 1)%nat + IQR 1%nat)).
      apply INR_le in H16.
      rewrite <- INR_plus in H16.
      apply IQR_le in H16.
      rewrite <- IQR_plus in H16.
      apply Rle_lt_trans with (IQR x3) ; auto.
      apply Rlt_trans with (IQR (x2 + 1)%nat + IQR 1 / IQR 10%nat) ; auto.
      apply Rlt_Rplus_l. unfold Rdiv.
      rewrite IQR_R1. rewrite Rmult_1_l.
      rewrite IQR_inv ; auto.
      apply IQR_lt.
      rewrite INR_Qeq_1.
      apply Qlt_shift_inv_r.
      rewrite <- INR_Qeq_0. apply INR_lt. omega.
      rewrite Qmult_1_l. rewrite <- INR_Qeq_1. apply INR_lt. omega.
      intro. rewrite <- INR_Qeq_0 in H19. apply Qeq_INR_eq in H19. omega.
    - assert (x2 <= x3)%nat.
      { apply NNPP. intro.
        assert (x3 + 1<= x2)%nat. { omega. }
        apply INR_le in H15. apply IQR_le in H15.
        apply (Rlt_irrefl (IQR x2)).
        apply Rle_lt_trans with (r2 * IQR (10 ^ x)%nat) ; auto.
        apply Rle_lt_trans with (limitTM'r * IQR (10 ^ x)%nat) ; auto.
        apply Rlt_le_trans with (IQR (x3 + 1)%nat) ; auto.
      }
      assert (x0 < 10)%nat. { rewrite H12. apply Nat.mod_upper_bound. auto. }
      symmetry in H12 , H10.
      apply mod_exists in H12 ; auto. apply mod_exists in H10 ; try (omega).
      destruct H12 , H10.
      assert (x3  >= x2 + 1)%nat. { omega. }
      assert (Same_Ipart (r2 * IQR (10 ^ x)%nat) (r2 * IQR (10 ^ x)%nat + IQR 1 / IQR 10%nat)).
      { rewrite <- H9. rewrite <- Rmult_plus_distr_r.
        rewrite IQR_R1. rewrite <- IQR_R1_same.
        pose proof Same_Ipart_pow10n.
        assert (IQR 1%nat / IQR (10 ^ S x)%nat = IQR (1%nat / (10 ^ S x)%nat)).
        { unfold Rdiv. rewrite IQR_inv ; auto. rewrite IQR_mult.
          apply IQR_eq. reflexivity.
        }
        rewrite H18.
        apply H17.
        subst r2.
        apply InDecR_all_n.
        apply TM'r_InDecR.
      }
      destruct H17 , H17 , H18 , H19.
      assert (x6 = x2)%nat. { apply (Ipart_unique (r2 * IQR (10 ^ x)%nat)) ; auto. }
      subst x6.
      apply (Rlt_irrefl (IQR (x2 + 1)%nat)).
      apply Rlt_trans with (r2 * IQR (10 ^ x)%nat + IQR 1 / IQR 10%nat) ; auto.
      apply Rle_lt_trans with (limitTM'r * IQR (10 ^ x)%nat) ; auto.
      apply Rle_trans with (IQR x3) ; auto.
      apply IQR_le. apply INR_le. omega.
  Qed.
  
  Theorem limitTM'r_pro : forall (n : nat) , Dec_R limitTM'r n 1 <-> exists j : nat , TM n j = true.
  Proof.
    intros.
    pose proof limit_of_TM'r.
    destruct H. 
    split ; intros.
    - assert (~ INR (10 ^ S n) == 0)%Q.
      { intro. apply (Qlt_irrefl 0%Q). rewrite <- H2 at 2.
        rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
      }
      set (eps := (IQR 1 / IQR (10 ^ S n)%nat)).
      assert (eps > R0).
      { rewrite <- IQR_R0. subst eps. unfold Rdiv. 
        rewrite IQR_inv ; auto. rewrite IQR_mult. apply IQR_lt.
        rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
      }
      specialize (H0 _ H3). destruct H0.
      assert (x >= x)%nat. { omega. }
      assert (TM'r x = TM'r x). { auto. }
      specialize (H0 _ _ H4 H5).
      exists x.
      apply TM'r_pro0. clear H4 H5.
      assert (Same_Ipart_n (TM'r x) (S n - 1)). { apply Same_Ipart_pow10n. apply InDecR_all_n. apply TM'r_InDecR. }
      assert (Same_Ipart_n limitTM'r (S n - 1)). { apply Same_Ipart_pow10n. apply InDecR_all_n. apply limitTM'r_pro0. }
      pose proof (Dec_R_eps_same (TM'r x) limitTM'r _ H0 H4 H5).
      apply H6 ; auto.
    - destruct H1.
      assert (~ INR (10 ^ S (max x n)) == 0)%Q.
      { intro. apply (Qlt_irrefl 0%Q). rewrite <- H2 at 2.
        rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
      }
      set (eps := (IQR 1 / IQR (10 ^ S (max x n))%nat)).
      assert (eps > R0).
      { rewrite <- IQR_R0. subst eps. unfold Rdiv. 
        rewrite IQR_inv ; auto. rewrite IQR_mult. apply IQR_lt.
        rewrite Qmult_1_l. apply Qinv_lt_0_compat.
        rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
      }
      specialize (H0 _ H3). destruct H0.
      assert (max x0 x >= x0)%nat. { apply Nat.le_max_l. }
      assert (TM'r (max x0 x) = TM'r (max x0 x)). { auto. }
      specialize (H0 _ _ H4 H5). clear H4 H5 H2.
      assert (max x0 x >= x)%nat. { apply Nat.le_max_r. }
      assert (Same_Ipart_n (TM'r (max x0 x)) (S (max x n) - 1)). {  apply Same_Ipart_pow10n. apply InDecR_all_n. apply TM'r_InDecR. }
      assert (Same_Ipart_n (limitTM'r) (S (max x n) - 1)). {  apply Same_Ipart_pow10n. apply InDecR_all_n. apply limitTM'r_pro0. }
      pose proof (Dec_R_eps_same (TM'r (max x0 x)) limitTM'r _ H0 H4 H5).
      apply H6 ; auto.
      unfold lt. apply le_n_S. apply Nat.le_max_r.
      rewrite TM'r_pro0.
      apply (Turing_mono _ x (max x0 x)) ; auto.
  Qed.
  
  Theorem limitTM'r_pro' : forall (n : nat) , Dec_R limitTM'r n 0 <-> forall j : nat , TM n j = false. 
  Proof.
    intros.
    pose proof limitTM'r_pro n.
    unfold not in *.
    split ; intros.
    - destruct (TM n j) eqn:En ; auto.
      assert (exists j : nat , TM n j = true). { exists j. auto. }
      apply H in H1.
      apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R limitTM'r n) ; auto.
    - destruct (limitTM'r_pro0 n ) ; auto.
      apply H in H1.
      destruct H1.
      exfalso. rewrite H0 in H1. inversion H1.
  Qed.

  Theorem limitTM'r_pro1 : (forall (n : nat) , {Dec_R limitTM'r n 0} + {Dec_R limitTM'r n 1}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof H i.
    destruct H0.
    - rewrite (limitTM'r_pro' i) in d. auto.
    - rewrite (limitTM'r_pro i) in d. auto.
  Qed.

End TMR_Set.