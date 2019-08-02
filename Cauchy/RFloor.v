From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Export Field.
From CReal Require Import QArith_ext.QArith_base_ext.
From CReal.Cauchy Require Import RBase.
From CReal.Cauchy Require Import RArith.
From CReal.Cauchy Require Import RSign.
From CReal.Cauchy Require Import ROrder.

Definition Rfloor (A:Real)(z:Z):Prop := (inject_Q (inject_Z z) <= A)%R
 /\ (inject_Q ((inject_Z z) + 1) > A)%R.

Theorem Rfloor_exists: forall A:Real, exists z, Rfloor A z.
Proof. intros. destruct A as [A HA].
  destruct (Cauchy_def _ HA (1#4)) as [n Hn]. reflexivity.
  destruct (Cauchy_exists _ HA (S n)) as [qn Hqn].
  remember (Qfloor qn) as zqn.
  destruct (classic (inject_Q (inject_Z zqn) <= (Real_intro A HA))%R).
  - destruct (classic (inject_Q (inject_Z (zqn + 1)%Z) <= (Real_intro A HA))%R).
  + exists (zqn + 1)%Z. hnf. split.
    auto. hnf. exists (1#2). split. reflexivity.
    exists (S n). intros. hnf in H2. unfold Cauchy_opp in H2.
    destruct (Cauchy_exists _ HA n0) as [qn0 Hqn0].
    assert (q == inject_Z (zqn+ 2) - qn0).
    { apply H2. assert (Et: 1 == inject_Z 1) by ring.
      rewrite Et. rewrite <- inject_Z_plus.
      assert (Et1: (zqn + 2 = zqn + 1 + 1)%Z) by omega.
      rewrite Et1. reflexivity.
      intros. rewrite (Cauchy_unique _ HA _ _ _ Hqn0 H3). reflexivity. }
    assert (H4: inject_Z (zqn +1) > qn).
    { rewrite Heqzqn. apply Qlt_floor. }
    assert (H5: Qabs (qn - qn0) < 1#4).
    { apply (Hn (S n) n0). auto. auto. auto. auto. }
    apply (Qle_trans _  (-(1#4)+1)).
    { assert (-(1#4)+1==3#4). { ring. }
      rewrite H6. intros C. simpl in C. discriminate C. }
    rewrite H3. unfold Qminus.
    assert (H7: inject_Z (zqn + 1) - qn0 > -(1#4)).
    { apply (Qlt_trans _ (qn-qn0)). apply Qabs_Qlt_condition in H5. destruct H5.
      auto. unfold Qminus. apply (proj2 (Qplus_lt_l _ _ (- qn0))). auto. }
    assert (H8: inject_Z (zqn + 2) + - qn0 == inject_Z (zqn + 1) - qn0 + 1).
    { unfold Qminus. rewrite <-(Qplus_assoc). rewrite (Qplus_comm _ 1).
      rewrite Qplus_assoc. assert (1==inject_Z 1) by ring.
      rewrite H6. rewrite <- inject_Z_plus.
      assert (zqn + 1 + 1 = zqn + 2)%Z by omega. rewrite H8. reflexivity. }
    rewrite H8. apply Qplus_le_compat.
    apply Qlt_le_weak. auto. apply Qle_refl.
  + exists zqn. hnf. split.
    auto. apply Rnot_le_lt in H0.
    assert ((inject_Q (inject_Z (zqn + 1)) ==(inject_Q (inject_Z zqn + 1)))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. rewrite inject_Z_plus. ring. }
      rewrite H5. auto. }
    rewrite <- H1. auto.
  - destruct (classic (inject_Q (inject_Z zqn - 1) <= (Real_intro A HA))%R).
  + exists (zqn-1)%Z. split.
    assert (T:((inject_Q (inject_Z (zqn - 1)) ==(inject_Q (inject_Z zqn -1)))%R)).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite T. auto.
    apply Rnot_le_lt in H.
    assert ((inject_Q (inject_Z (zqn-1)+1) ==(inject_Q (inject_Z zqn )))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite H1. auto.
  + apply Rnot_le_lt in H. apply Rnot_le_lt in H0. exists (zqn-2)%Z.
    hnf. split.
  * hnf. left. hnf. exists (1#2). split. reflexivity.
    exists (S n). intros. hnf in H2. unfold Cauchy_opp in H2.
    destruct (Cauchy_exists _ HA n0) as [qn0 Hqn0].
    assert (q == qn0 - inject_Z (zqn - 2)).
    { apply H2. auto. intros. rewrite H3. reflexivity. }
    assert (H4: inject_Z (zqn ) <= qn).
    { rewrite Heqzqn. apply Qfloor_le. }
    assert (H5: Qabs (qn0 - qn) < 1#4).
    { apply (Hn n0 (S n)). auto. auto. auto. auto. }
    apply (Qle_trans _  (-(1#4)+(inject_Z 2))).
    { assert (-(1#4)+(inject_Z 2)==7#4). { ring. }
      rewrite H6. intros C. simpl in C. discriminate C. }
    rewrite H3. unfold Qminus.
    assert (H7: qn0 -inject_Z (zqn) > -(1#4)).
    { apply Qabs_Qlt_condition in H5. destruct H5.
      apply (Qlt_le_trans _ (qn0 - qn)).
      auto. unfold Qminus. apply (proj2 (Qplus_le_r _ _ (qn0))).
      apply Qopp_le_compat. auto. }
    assert (H8: qn0 + - inject_Z (zqn - 2) == (qn0 - (inject_Z zqn)) + (inject_Z 2)).
    { unfold Qminus. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
    rewrite H8. apply Qplus_le_compat.
    apply Qlt_le_weak. auto. apply Qle_refl.
  * assert (T:(inject_Q (inject_Z zqn - 1) ==(inject_Q (inject_Z (zqn - 2) + 1)))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite <- T. auto.
Qed.


Theorem Rfloor_unique: forall (A:Real) (z1 z2:Z), Rfloor A z1 -> Rfloor A z2 -> z1 = z2.
Proof. intros. hnf in *. destruct H as [H1 H2], H0 as [H3 H4].
destruct (Ztrichotomy_inf z1 z2) as [[Z1|Z2]|Z3].
- assert (E:(z1+1<=z2)%Z) by omega.
  rewrite Zle_Qle in E. apply Qle_Rle in E.
  assert (foo: (A < A)%R).
  { apply (Rlt_le_trans _ _ _ H2). apply (Rle_trans _ (inject_Q (inject_Z z2))).
    assert (Et: (inject_Q (inject_Z z1 + 1) == (inject_Q (inject_Z (z1 + 1))))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H5,H6.  rewrite inject_Z_plus. ring. }
      rewrite H7. auto. }
    rewrite Et. auto. auto. }
  apply Rlt_irrefl in foo. destruct foo.
- auto.
- assert (E:(z2+1<=z1)%Z) by omega.
  rewrite Zle_Qle in E. apply Qle_Rle in E.
  assert (foo: (A < A)%R).
  { apply (Rlt_le_trans _ _ _ H4). apply (Rle_trans _ (inject_Q (inject_Z z1))).
    assert (Et: (inject_Q (inject_Z z2 + 1) == (inject_Q (inject_Z (z2 + 1))))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H5,H6.  rewrite inject_Z_plus. ring. }
      rewrite H7. auto. }
    rewrite Et. auto. auto. }
  apply Rlt_irrefl in foo. destruct foo.
Qed.


Instance Rfloor_comp: Proper (Real_equiv ==> Z.eq ==> iff) Rfloor.
Proof. split.
- intros. rewrite <- H0.
  destruct H1 as [H1 H2].
  split.
  rewrite <- H. auto. rewrite <- H.
  auto.
- intros. rewrite H0.
  destruct H1 as [H1 H2].
  split. rewrite H. auto.
  rewrite H. auto.
Qed.

Theorem Rfloor_iff: forall A z, Rfloor A z -> (inject_Q (inject_Z z) > A - 1 /\ 
  inject_Q (inject_Z z) <= A)%R.
Proof. intros. destruct H. assert (E1:(1==inject_Q 1)%R). { reflexivity. }
  split. 
  - unfold Rgt. apply (Rlt_plus_compat_r _ _ 1). rewrite E1.
    rewrite <- inject_Q_plus. assert (A - inject_Q 1 + inject_Q 1 == A)%R by ring.
    rewrite H1. auto. 
  - auto.
Qed.

