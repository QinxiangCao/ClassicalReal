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

Module VirRLemmas (VirR_ex : VIR_R_EXTRA).
  Module VirR_comp := VirR_ex.VirR_Comp.
  Module VirR := VirR_comp.VirR.
  Import VirR VirR_comp VirR_ex.
  Module Lemma1 := VirRLemma1 (VirR).
  Export Lemma1.
  
  Local Open Scope R_scope.
  
  Definition Rabs : R -> R.
    intros.
    apply (Rif (X >= R0) X (- X)).
  Defined.

  Instance Rabs_comp : Proper (Req ==> Req) Rabs.
  Proof.
    hnf ; intros.
    unfold Rabs.
    assert ((x >= R0) = (y >= R0)).
    { apply propositional_extensionality. rewrite H. reflexivity. }
    rewrite H0. rewrite H. reflexivity.
  Qed.
  
  Theorem Rabs_pos : forall r1 : R , (r1 >= 0) -> Rabs r1 == r1.
  Proof.
    intros.
    unfold Rabs. apply Rif_left. auto.
  Qed.
  
  Theorem Rabs_neg : forall r1 : R , (r1 <= 0) -> Rabs r1 == (- r1).
  Proof.
    intros.
    unfold Rabs. 
    destruct H.
    - apply Rif_right. auto with real.
    - assert ((r1 >= 0) = (0 >= 0)).
      { apply propositional_extensionality. rewrite H. reflexivity. }
      rewrite H0. rewrite H.
      rewrite Ropp_0. apply Rif_left. auto with real.
  Qed.
  
  Hint Resolve Rabs_pos Rabs_neg: real.
  
  Theorem Rabs_le_0 : forall r : R , Rabs r >= 0.
  Proof.
    intros.
    destruct (Rtotal_order r 0).
    - rewrite Rabs_neg ; auto with real.
      rewrite <- Ropp_0. auto with real.
    - rewrite or_comm in H. rewrite Rabs_pos ; auto.
  Qed.
  
  Hint Resolve Rabs_le_0 : real.
  Theorem Rabs_le : forall r : R , r <= Rabs r.
  Proof.
    intros.
    destruct (Rtotal_order r 0).
    - apply Rle_trans with 0 ; auto with real.
    - rewrite or_comm in H. rewrite Rabs_pos ; auto with real.
  Qed.
  Hint Resolve Rabs_le : real.
  
  Theorem Rabs_tri : forall a b c : R , Rabs(a - b) < c <-> a < b + c /\ a > b - c.
  Proof.
    intros.
    split ; intros.
    - assert (c > 0).
      { apply Rle_lt_trans with (Rabs (a - b)) ; auto with real. }
      destruct (classic (a - b >= 0)).
      + rewrite Rabs_pos in H ; auto.
        split.
        * apply Rlt_Rminus_Rplus ; auto.
        * apply Rlt_le_trans with b.
          -- apply Rminus_gt_0_lt. 
             assert (b - (b - c) == c). { ring. }
             rewrite H2.  auto.
          -- apply Rge_le. apply Rminus_ge. auto.
      + apply Rnot_ge_lt in H1.
        rewrite Rabs_neg in H ; auto with real.
        split.
        * apply Rlt_trans with b.
          -- apply Rminus_lt. auto.
          -- rewrite <- Rplus_0_r at 1. apply Rplus_lt_compat_l. auto.
        * rewrite Ropp_minus_distr' in H.
          apply Rlt_Rminus_r. auto.
    - destruct H.
      apply Rlt_Rminus_Rplus in H.
      rewrite <- Rplus_0_l in H0 at 1.
      assert (b - b == 0). {ring. }
      rewrite <- H1 in H0. unfold Rminus in H0. 
      rewrite Rplus_assoc in H0.
      apply Rplus_lt_reg_l in H0. rewrite Rplus_comm in H0.
      destruct (Rle_dec (a - b) R0).
      + rewrite Rabs_neg ; auto.
        apply Ropp_lt_cancel ; auto.
        rewrite Ropp_involutive. auto.
      + apply Rnot_le_gt in H2.
        rewrite Rabs_pos ; auto with real.
        left. auto.
  Qed.
  
  Theorem Rabs_comm : forall a b : R , Rabs (a - b) == Rabs (b - a).
  Proof.
    intros.
    destruct (classic (a - b >= 0)).
    - rewrite Rabs_pos ; auto with real.
      rewrite Rabs_neg ; auto with real.
      apply Ropp_le_cancel.
      rewrite Ropp_0. rewrite Ropp_minus_distr'. auto with real.
    - apply Rnot_ge_lt in H.
      rewrite Rabs_neg ; auto with real.
      rewrite Rabs_pos ; auto with real.
      apply Rle_ge. apply Ropp_le_cancel.
      rewrite Ropp_0. rewrite Ropp_minus_distr'. left. auto.
  Qed.

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
    assert (x > 0)%Z. { apply Z.lt_gt. apply lt_IZR. rewrite IZR_R0. apply Rle_lt_trans with r ; auto with real. }
    split ;  rewrite INQ_IQR_INR ;  rewrite INR_IZR_INZ.  
    - rewrite Z2Nat.id ; try (omega).
      rewrite minus_IZR. rewrite IZR_R1.
      apply Rminus_le. apply Rle_minus in H1.  
      assert (IZR x - r - 1 == IZR x - 1 - r). { ring. }
      rewrite <- H3. auto.
    - rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id ; try (omega). simpl.
      assert (x - 1 + 1 = x)%Z. { ring. }
      rewrite H3. auto with real.
  Qed.
  
  Theorem Rlt_mid : forall r r1 : R , r < r1 -> exists eps : Q , (eps > 0)%Q /\ r + IQR eps < r1 - IQR eps.
  Proof.
    intros.
    apply Rlt_Rminus in H.
    assert ((r1 - r) / 2 > 0). { apply Rdiv_lt_0_compat ; auto with real. }
    assert (2 / (r1 - r) > 0). { apply Rdiv_lt_0_compat ; auto with real. }
    destruct (archimedean_exists (2 / (r1 - r))).
    - left. auto.
    - destruct H2.
      assert ((r1 - r) / 2 > / IQR (x + 1)%nat).
      { assert ((r1 - r) / 2 == / (2 / (r1 - r))).
        { field. auto with real. }
        rewrite H4. apply Rinv_lt_contravar ; auto.
        apply Rmult_lt_0_compat ; auto.
        rewrite INQ_IQR_INR.
        rewrite <- INR_R0. apply lt_INR. omega.
      }
      rewrite IQR_inv in H4.
      + exists (/ (INQ (x + 1)%nat))%Q.
        split.
        * apply Qinv_lt_0_compat. rewrite <- INQ_Qeq_0.
          apply INQ_lt. omega.
        * apply Rlt_trans with (r + (r1 - r) / 2).
          apply Rplus_lt_compat_l ; auto.
          assert (r + (r1 - r) / 2 == r1 - (r1 - r) / 2).
          { field. }
          rewrite H5.
          unfold Rminus. apply Rplus_lt_compat_l.
          apply Ropp_lt_contravar.
          auto.
      + intro.
        apply (Qlt_irrefl 0%Q).
        rewrite <- H5 at 2.
        rewrite <- INQ_Qeq_0. apply INQ_lt. omega.
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
    assert (INR 1 == 1). { auto with real. }
    rewrite H3 in *. clear H3.
    rewrite INR_IZR_INZ in *.
    assert (r - 1 + 1 == r). { ring. }
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
    { apply lt_INR in H. auto with real. }
    apply Rmult_le_divr in H0; auto.
    apply Rmult_le_divr in H1; auto.
    apply Rmult_gt_divr in H2; auto.
    apply Rmult_gt_divr in H3; auto.
    destruct (archimedean_exists (INR x / INR k)).
    apply Rmult_ge_divr ; auto. rewrite Rmult_0_l. auto with real.
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
    is_function eq Req A /\ (
    forall eps : R , eps > R0 -> (exists n : nat , 
          forall (m : nat) (r1 : R) , (m >= n)%nat -> A m r1 -> Rabs(r1 - r) < eps)).
  
  Theorem Un_cv_inject : forall (X : nat -> R -> Prop) (r1 r2 : R) , Un_cv X r1 -> Un_cv X r2 -> r1 == r2.
  Proof. 
    intros.
    hnf in *.
    apply NNPP.
    intro.
    apply Rdichotomy in H1. destruct H , H0.
    destruct H , H0. destruct H4 , H5. clear H7 H6.
    destruct H1 ; apply Rlt_mid in H1 ; destruct H1 ; destruct H1 ;
    apply IQR_lt in H1 ; rewrite IQR_R0 in H1; 
    specialize (H2 (IQR x) H1) ; specialize (H3 (IQR x) H1) ; destruct H2 , H3 ; destruct (H (max x0 x1));
    destruct (H0 (max x0 x1)) ; 
    specialize (H2 (max x0 x1) x2 (Nat.le_max_l x0 x1) H7 ) ; specialize (H3 (max x0 x1) x3 (Nat.le_max_r x0 x1) H8); 
    apply Rabs_tri in H2 ; apply Rabs_tri in H3 ; destruct H2 , H3 ; specialize (H4 (max x0 x1) x2 x3 H7 H8) ; rewrite H4 in * ;
    apply (Rlt_irrefl x3). 
    - apply Rlt_trans with (r1 + IQR x) ; auto.
      apply Rlt_trans with (r2 - IQR x) ; auto.
    - apply Rlt_trans with (r2 + IQR x) ; auto.
      apply Rlt_trans with (r1 - IQR x) ; auto.
  Qed.
  
  Definition mono_up (X : nat -> R -> Prop) : Prop := is_function eq Req X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q >= q1).
  Definition mono_down (X : nat -> R -> Prop) : Prop := is_function eq Req X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q <= q1).
  Definition mono (X : nat -> R -> Prop) : Prop := mono_up X \/ mono_down X.
  Definition upper_bound (X : nat -> R -> Prop) (U : R) : Prop := forall (n : nat)(q : R) , X n q -> q <= U.
  Definition Sup (X : nat -> R -> Prop) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.

  Theorem upper_bound_exists_Sup : forall (X : nat -> R -> Prop) , is_function eq Req X -> (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).
  Proof.
    intros.
    pose proof completeness.
    set (fun r => exists n : nat , X n r).
    assert (bound P).
    { hnf.
      destruct H0.
      exists x.
      hnf. intros.
      subst P. destruct H2.
      apply (H0 _ _ H2).
    }
    assert (exists x : R , P x).
    { destruct H. destruct (H O).
      exists x. exists O. auto.
    }
    specialize (H1 P H2 H3).
    subst P. simpl in *.
    destruct H1. destruct H1.
    exists x.
    split.
    - intros.
      apply Rle_ge.
      apply H4.
      hnf. intros.
      destruct H6.
      hnf in H5. apply (H5 _ _ H6).
    - hnf. intros.
      apply H1. exists n. auto.
  Qed.
  
  Definition lower_bound (X : nat -> R -> Prop) (L : R) : Prop := forall (n : nat)(q : R) , X n q -> L <= q.
  Definition Inf (X : nat -> R -> Prop) (inf : R) : Prop := (forall r : R , lower_bound X r -> r <= inf) /\ lower_bound X inf.
  Definition bound (X : nat -> R -> Prop) : Prop := (exists n1 : R , upper_bound X n1) /\ (exists n2 : R ,lower_bound X n2).
  Instance lower_bound_comp : Proper (eq ==> Req ==> iff) lower_bound.
  Proof. 
    hnf ; red ; intros.
    subst. split ; intros ; hnf in *.
    - intros. rewrite <- H0. apply (H _ _ H1).
    - intros. rewrite H0. apply (H _ _ H1).
  Qed.
  
  Instance upper_bound_comp : Proper (eq ==> Req ==> iff) upper_bound.
  Proof.
    hnf ; red ; intros.
    subst. split ; intros ; hnf in *.
    - intros. rewrite <- H0. apply (H _ _ H1).
    - intros. rewrite H0. apply (H _ _ H1).
  Qed.
  
  Instance Sup_comp : Proper (eq ==> Req ==> iff) Sup.
  Proof.
    hnf ; red ; intros.
    subst. split ; intros ; hnf in *.
    - split .
      + intros. rewrite <- H0. apply H. auto.
      + rewrite <- H0. apply H.
    - split.
      + intros. rewrite H0. apply H. auto.
      + rewrite H0. apply H.
  Qed.

  Instance Inf_comp : Proper (eq ==> Req ==> iff) Inf.
  Proof.
    hnf ; red ; intros.
    subst. split ; intros ; hnf in *.
    - split .
      + intros. rewrite <- H0. apply H. auto.
      + rewrite <- H0. apply H.
    - split.
      + intros. rewrite H0. apply H. auto.
      + rewrite H0. apply H. 
  Qed.
  
  Theorem Sup_pro : forall (X : nat -> R -> Prop) (sup : R) , is_function eq Req X -> Sup X sup -> forall y : R , (y < sup -> 
                              (exists n : nat , forall q : R , X n q -> ( q <= sup /\ y < q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0 , H4.
    apply Rlt_not_ge in H1.
    apply H1.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q == q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    rewrite H8 in *. 
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply (H5 n) ; auto.
    - apply Rnot_lt_ge in H3. auto with real. 
  Qed.
  
  Theorem Inf_pro : forall (X : nat -> R -> Prop) (inf : R) , is_function eq Req X -> Inf X inf -> forall y : R , (y > inf -> 
                              (exists n : nat , forall q : R , X n q -> (q >= inf /\ y > q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0 , H4.
    apply Rlt_not_ge in H1.
    apply H1. apply Rle_ge.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q == q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    rewrite H8 in *.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply Rle_ge. apply (H5 n); auto. 
    - apply Rnot_gt_le in H3. auto.
  Qed.

  Theorem upper_bound_T_lower_bound : forall (X P : nat -> R -> Prop) , is_function eq Req X -> is_function eq Req P
                                                                     -> (forall n r , X n r <-> P n (-r)) 
                                                                      -> forall r , upper_bound X r <-> lower_bound P (-r).
  Proof.
    intros.
    split ; intros.
    - hnf. intros.
      specialize (H1 n (-q)). destruct H , H0 , H4 ,H5.
      assert (P n (--q)). {
        assert (n = n). { auto. }
        specialize (H7 n n H8). hnf in H7.
        apply H7 with q ; auto with real.
      } clear H3. 
      rewrite <- H1 in H8.
      specialize (H2 n (-q) H8).
      rewrite <- (Ropp_involutive q). rewrite <- (Ropp_involutive r) in H2.
      apply Rle_opp_eqb ; auto.
    - hnf. intros.
      specialize (H1 n q).
      rewrite H1 in H3.
      specialize (H2 n (-q) H3).
      auto with real.
  Qed.
  
  Theorem lower_bound_exists_Inf : forall (X : nat -> R -> Prop) , is_function eq Req X -> (exists r : R , lower_bound X r) ->
                                          (exists inf : R , Inf X inf).
  Proof.
    intros.
    destruct H0.
    set (fun (n : nat)(r : R) => X n (-r)).
    assert (is_function eq Req P).
    {
      destruct H.
      repeat split.
      - intro. destruct (H a). exists (-x0).
        subst P. simpl.
        destruct H1. assert (a = a). { auto. }
        specialize (H3 _ _ H4 x0 (--x0)).
        apply H3 ; auto with real.
      - intro. intros. destruct H1.
        specialize (H1 a (-b1) (-b2) H2 H3).
        apply Ropp_eq_compat in H1.
        rewrite !Ropp_involutive in H1.
        auto.
      - intros. subst P. simpl in *.
        destruct H1.
        apply Ropp_eq_compat in H3.
        apply (H5 _ _ H2 _ _ H3). auto.
      - intros. subst P. simpl in *.
        destruct H1. apply Ropp_eq_compat in H3.
        apply (H5 _ _ H2 _ _ H3). auto.
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
  
  Theorem Sup_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Sup X r1 -> Sup X r2 -> r1 == r2.
  Proof. 
    intros.
    unfold Sup in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with real.
  Qed.

  Theorem Inf_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Inf X r1 -> Inf X r2 -> r1 == r2.
  Proof.
    intros.
    unfold Inf in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    auto with real.
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
    { rewrite <- (Rplus_0_r x) at 2.
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
    assert (r == x).
    {
      apply (Un_cv_inject X) ; auto.
      unfold Un_cv , mono_up in *.
      split ; auto.
      intros.
      assert (x - eps < x).
      { rewrite <- (Rplus_0_r x) at 2.
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
    rewrite H0. auto.
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
    { rewrite <- (Rplus_0_r x) at 2.
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
    set (fun (n : nat)(r : R) => r == INR n * r2).
    assert (is_function eq Req P).
    {
      subst P.
      repeat split ; hnf ; intros.
      - exists (INR a * r2). auto with real.
      - rewrite H2 , H3. auto with real.
      - subst. rewrite H3 in *. auto.
      - subst. rewrite H3 in *. auto. 
    }
    assert (upper_bound P r1).
    { hnf ; intros.
      subst P.
      simpl in *.
      rewrite H3.
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
      assert (x - x == 0). { ring. }
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
      simpl in *. rewrite (S_INR x0).
      rewrite H9. ring.
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
  
  Theorem Req_same : forall r1 r2 : R , r1 == r2 <-> forall eps : R , eps > R0 -> Rabs(r1 - r2) < eps.
  Proof.
    intros.
    split; intros ; subst ; try (reflexivity).
    - unfold Rminus. rewrite H. rewrite Rplus_opp_r. rewrite Rabs_pos. apply Rlt_gt. auto.
      apply Rle_refl.
    - apply NNPP.
      intro.
      apply Rdichotomy in H0.
      destruct H0.
      + apply Rlt_neg_eqb in H0.
        assert (r1 - r2 <= R0). { auto with real. }
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
        assert (r1 - r2 >= R0). { apply Rle_ge. auto with real. }
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

  Theorem Z_same_R' : forall z1 z2 : Z , (z1 <> z2)%Z <-> ~ IZR z1 == IZR z2.
  Proof. split ; intros ; auto with real.
    apply Rdichotomy in H.
    destruct H ; apply lt_IZR in H ; omega.
  Qed.
  
  Theorem Ex_Z_R' : forall z : Z , (z <> 0)%Z <-> ~ IZR z == R0.
  Proof.
    split ; intros ; auto with real.
    rewrite <- IZR_R0 in H.
    apply Rdichotomy in H. destruct H ; apply lt_IZR in H ; omega.
  Qed.

End VirRLemmas.
