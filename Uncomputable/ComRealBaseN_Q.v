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
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
Import TM_N_Q.

Module CR_NQ (VirR: VIR_R) (VirRSingleton : VIR_R_SINGLETON VirR) (VirRComp: VIR_R_COMPLETE VirR).
  Import VirR VirRSingleton.
  
  Module VirRSL := VirRSingletonLemmas VirR VirRSingleton.
  Module VirRSL2 := VirRSingletonLemmas2 VirR VirRSingleton VirRComp.
  Module Dec := DEC_R VirR VirRSingleton VirRComp.
  Export VirRSL VirRSL2 Dec.
  Local Open Scope R_scope.

  Definition limit (f : nat -> Q) (r : R) : Prop :=
    forall eps : Q , (eps > 0)%Q -> exists N : nat , forall n : nat , (n >= N)%nat -> Rabs(IQR (f n) - r) < IQR eps.
  (** exists a sequence of rational number limits to r *)
  Definition CR2 (r : R) := exists f : nat -> Q, limit f r.

  Theorem limit_inject : forall (f : nat -> Q) (r1 r2 : R) , limit f r1 -> limit f r2 -> r1 == r2.
  Proof.
    intros.
    hnf in *.
    apply NNPP.
    unfold not in *.
    intros.
    apply Rdichotomy in H1.
    destruct H1 ; apply Rlt_mid in H1 ; destruct H1 ; destruct H1 ; 
      specialize (H x H1) ; specialize (H0 x H1) ; destruct H , H0 ;
      specialize (H (max x0 x1) (Nat.le_max_l x0 x1) ) ; specialize (H0 (max x0 x1) (Nat.le_max_r x0 x1))
      ; apply Rabs_tri in H ; apply Rabs_tri in H0 ; destruct H , H0 ; apply (Rlt_irrefl (IQR (f (max x0 x1)))).
    - apply Rlt_trans with (r1 + IQR x) ; auto.
      apply Rlt_trans with (r2 - IQR x) ; auto.
    - apply Rlt_trans with (r2 + IQR x) ; auto.
      apply Rlt_trans with (r1 - IQR x) ; auto.
  Qed. 
  
  Instance limit_comp : Proper (eq ==> Req ==> iff) limit.
  Proof.
    hnf ; red ; intros ; subst.
    split ; intros ; hnf in * ; intros ; specialize (H _ H1) ; destruct H;
    exists x ; intros ; specialize (H _ H2) ; rewrite H0 in * ; auto.
  Qed.
  
  Instance CR2_comp : Proper (Req ==> iff) CR2.
  Proof.
    hnf ; intros.
    split ; intros ; hnf in * ; destruct H0 ; exists x0 ;
    rewrite H in * ; auto. 
  Qed.
  
  Definition CR2_r : Type := { r : R | CR2 r}.

  Definition CR2_r_eq (x y : CR2_r) : Prop .
    destruct x , y.
    apply (x == x0).
  Defined.
  
  Instance CR2_r_eq_equiv : Equivalence CR2_r_eq.
  Proof.
    split ; hnf ; intros.
    - destruct x. hnf. auto with real.
    - destruct x , y. simpl in *. auto with real.
    - destruct x , y , z. simpl in *. rewrite H. auto.
  Qed.
  
  Theorem all_Q_CR2 : forall (q : Q) , CR2 (IQR q).
  Proof.
    intros.
    unfold CR2.
    exists (fun n => q).
    unfold limit.
    intros.
    exists O.
    intros.
    rewrite Rminus_diag_eq ; try (ring). 
    rewrite Rabs_pos.
    rewrite <- IQR_R0. apply IQR_lt. auto.
    apply Rle_refl.
   Qed.
   
  Definition NQ : Type := nat -> Q.
  Definition NQ_T_nat := NQ -> nat.
  
  Theorem NQ_nat : injection (eq(A:=NQ)) (eq(A:=nat)) .
  Proof.
    assert (injection (eq(A:=NQ)) TMNQ_eq).
    {
      exists Combine.
      apply Combine_comp.
      apply image_defined_Combine.
      apply partial_functional_Combine.
      apply injective_Combine.
    }
    pose proof Countable_TMNQ.
    unfold Countable in *.
    apply (injection_trans _ X X0).
  Qed.
  
  Definition CR2_r_NQ (r : CR2_r) (p : nat -> Q) : Prop .
    destruct r.
    apply (limit p x).
  Defined.
 
  Definition CR2_r_NQ' (r : CR2_r) (p : nat -> Q) : Prop := 
    CR2_r_NQ r p /\ forall q : nat -> Q , CR2_r_NQ r q -> 
          (forall x y : nat , NQ_nat p x -> NQ_nat q y -> (x <= y)%nat).
  
  Theorem image_defined_CR2TNQ' : image_defined CR2_r_NQ'.
  Proof.
    unfold image_defined , CR2_r_NQ' , CR2_r_NQ. 
    intros.
    destruct NQ_nat.
    destruct a.
    set (fun n : nat => exists nq : nat -> Q , limit nq x /\ inj_R nq n).
    assert (forall n : nat , P n \/ ~ P n).
    { intros. apply classic. }
    assert (exists n : nat , P n).
    {   destruct c.
        destruct (im_inj x0).
        exists x1. exists x0. auto.
    }
    pose proof (dec_inh_nat_subset_has_unique_least_element P H H0).
    repeat destruct H1.
    exists x1. split ; auto.
    intros.
    hnf in H6 , H7.
    assert (x2 = x0). { apply (pf_inj x1) ;  auto. }
    subst.
    apply H3.
    exists q ; auto.
  Qed.
  
  Theorem partial_functional_CR2TNQ' : partial_functional eq CR2_r_NQ'.
  Proof. 
    unfold partial_functional in *.
    intros.
    destruct a.
    destruct H , H0.
    pose proof (H1 b2 H0).
    pose proof (H2 b1 H).
    clear H H0 H1 H2.
    destruct NQ_nat.
    destruct (im_inj b1).
    destruct (im_inj b2).
    pose proof (H3 x0 x1 H H0).
    pose proof (H4 x1 x0 H0 H). 
    assert ((x1 = x0)%nat). { omega. }
    subst.
    apply  (in_inj b1 b2 x0) ; auto.
  Qed.
  
  Theorem injective_CR2TNQ' : injective CR2_r_eq CR2_r_NQ'.
  Proof. 
    unfold injective , CR2_r_NQ in *.
    intros.
    destruct a1 , a2. 
    repeat destruct H , H0.
    unfold CR2_r_NQ in H , H0.
    assert (x == x0). { apply (limit_inject b) ; auto. }
    simpl. auto.
  Qed.
  
  Theorem Countable_CR2 : Countable CR2_r CR2_r_eq.
  Proof.
    pose proof NQ_nat.
    unfold Countable.
    assert (injection CR2_r_eq (eq(A:=NQ))).
    { 
      exists CR2_r_NQ'.
      - split;  intros ; subst ; destruct x , y ; hnf in * ; simpl in *.
        + destruct H1 ; split ; rewrite H in *; auto.
          intros. apply (H1 q) ; auto. rewrite H in * ; auto.
        + destruct H1 ; split ; rewrite <- H in *; auto.
          intros. apply (H1 q) ; auto. rewrite H in * ; auto.
      - apply image_defined_CR2TNQ'.
      - apply partial_functional_CR2TNQ'.
      - apply injective_CR2TNQ'.
    }
    apply (injection_trans _ X0 X).
  Qed.
  
  Definition P_for_DecR (D : Dec) : Prop := forall r : R , Dec_r D r -> CR2 r.
  Definition DecR_to_CR2 (D : Dec)(r : CR2_r) : Prop.
    destruct r.
    apply (Dec_r D x).
  Defined.
  Definition R_CR2_CR2r (r : R) (H: CR2 r) : CR2_r.
    exists r ; auto.
  Defined.
  
  Instance DecR_to_CR2_comp : Proper (eq ==> CR2_r_eq ==> iff) DecR_to_CR2.
  Proof.
    hnf ; red; intros ; split ; intros ;  subst ; destruct x0 , y0; hnf in * ; simpl in *.
    - split ; intros ;  rewrite <- H0 in * ; apply H1.
    - split ; intros ; rewrite H0 in * ; apply H1.
  Qed.
  
  Theorem image_defined_DRTCR2 : (forall D : Dec , P_for_DecR D) -> image_defined DecR_to_CR2.
  Proof.
    unfold image_defined , P_for_DecR , CR2_r , DecR_to_CR2. 
    intros.
    pose proof H a.
    destruct (image_defined_Dec_r a).
    pose proof H0 x H1.
    exists (R_CR2_CR2r x H2).
    auto.
  Qed.
  
  Theorem partial_functional_DRTCR2 : (forall D : Dec , P_for_DecR D) -> partial_functional CR2_r_eq DecR_to_CR2.
  Proof. 
    pose proof partial_functional_Dec_r.
    unfold partial_functional , P_for_DecR , CR2_r , DecR_to_CR2 in *.
    intros.
    destruct b1 , b2.
    pose proof (H a x x0 H1 H2).
    simpl. auto.
  Qed.
  
  Theorem injective_DRTCR2 : (forall D : Dec , P_for_DecR D) -> injective eq DecR_to_CR2.
  Proof. 
    pose proof injective_Dec_r.
    unfold injective , P_for_DecR , CR2_r , DecR_to_CR2 in *.
    intros.
    destruct b.
    apply (H _ _ x) ; auto.
  Qed.
  
  Theorem exists_DecR_not_CR2 : exists D : Dec , ~ P_for_DecR D.
  Proof.
    apply not_all_ex_not .
    unfold not.
    intros.
    apply UnCountable_DecR.
    pose proof Countable_CR2.
    destruct X.
    pose proof partial_functional_DRTCR2 H.
    pose proof image_defined_DRTCR2 H.
    pose proof injective_DRTCR2 H.
    set (fun (d : Dec)(n : nat) => forall r : CR2_r , DecR_to_CR2 d r -> inj_R r n).
    exists P ; subst P; hnf ; intros.
    - hnf ; intros. subst. reflexivity.
    - destruct (H1 a).
      destruct (im_inj x).
      exists x0.
      intros.
      pose proof (H0 a _ _ H3 H5).
      rewrite <- H6 ; auto.
    - destruct (H1 a).
      pose proof (H3 _ H5).
      pose proof (H4 _ H5).
      apply (pf_inj x b1 b2) ; auto.
    - destruct (H1 a1).
      destruct (H1 a2).
      pose proof H3 x H5.
      pose proof H4 x0 H6.
      pose proof in_inj x x0 b H7 H8.
      apply (H2 a1 a2 x0) ; auto.
      rewrite H9 in H5. auto.
  Qed.

  Theorem limit_CN2'_NCN : (forall (Un:nat -> R->Prop) (l1:R), Un_cv Un l1 -> 
          (forall (n : nat)(r : R) , Un n r -> CR2 r) -> CR2 l1) -> False.
  Proof.
    destruct exists_DecR_not_CR2.
    intros.
    apply H.
    unfold P_for_DecR in *.
    intros.
    destruct x.
    set (NQP_T_NRP (NNP_T_NQP x)).
    assert (Un_cv P r). {
     assert (mono_up P).
     {
        pose proof Dec_mono_up (NNP_Dec x i).
        subst P. apply H2.
     }
     assert (exists r : R , upper_bound P r).
     {
        pose proof Dec_upper_bound (NNP_Dec x i).
        destruct H3. exists x0.
        subst. 
        auto.
     }
     pose proof mono_up_upper_bound_seq_has_limit P H2 H3.
     destruct H4.
     apply Uncv_eqb_Uncv' in H4.
     pose proof Un_cv'_Dec x x0 i H4.
     assert (x0 == r). 
     {
        pose proof Dec_R2_bound x i.
        apply Uncv_eqb_Uncv' in H4.
        apply Dec_R_eq.
        - pose proof mono_up_limit_sup _ H2 H3 _ H4.
          destruct H7.
          subst P.
          split.
          + destruct H2 , H2.
            destruct (H2 O).
            specialize (H8 O x1 H11).
            apply Rle_ge. apply Rle_trans with x1 ; auto.
            destruct H11.
            destruct H11 ; subst.
            destruct H12. rewrite <- H11. destruct H13.  
            auto with real.
          + apply Rle_lt_trans with 2.
            * auto with real.
            * apply R2_Rlt_R10.
        - destruct H1.
          apply H7.
        - intros. rewrite H5. destruct H1.
          rewrite H1. reflexivity.
        - apply is_function_NNP_T_NQP. auto.
     }
     subst. apply Uncv_eqb_Uncv' ; auto.
     apply is_function_NNP_T_NQP ; auto.
     rewrite <- H6. auto.
     apply is_function_NNP_T_NQP ; auto. 
    }
    assert (forall (n : nat)(r' : R), P n r' -> CR2 r').
    { intros.
      subst P.
      destruct H3 , H3.
      rewrite <- H3.
      apply all_Q_CR2.
    }
    pose proof (H0 P r H2 H3).
    auto.
  Qed.
End CR_NQ.
