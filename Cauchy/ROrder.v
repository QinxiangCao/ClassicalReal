From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From CReal Require Import QArith_ext.QArith_base_ext.
From Coq Require Import Classes.Morphisms.
From CReal Require Import RBase_uncomp.

Lemma Qopp_le_compat_iff: forall p q, p<=q <-> -q <= -p.
Proof. split. apply Qopp_le_compat.
  intros. rewrite <- (Qopp_involutive q), <- (Qopp_involutive p).
  apply Qopp_le_compat. apply H.
Qed.

Definition Rpositive (A:Real):Prop:=
  exists eps0:Q, (eps0>0) /\ 
    (exists N, forall n, (n>=N)%nat -> 
      forall q, (match A with | Real_intro A0 _ => A0 end) n q -> q >= eps0).

Theorem Rpositive_equiv: forall A B,
  (A == B)%R -> Rpositive A -> Rpositive B.
Proof. intros [A HA] [B HB] H0 H1. hnf in *.
  destruct H1 as [eps0 [H H1]]. exists (eps0 *(1#2)). split.
  apply eps_divide_2_positive. auto.
  destruct H1 as [N1 H1].
  destruct (H0 _ (eps_divide_2_positive _ H)) as [N2 H2].
  assert (HN: lt N1 N2 \/ ~(lt N1 N2)) by (apply classic). destruct HN as [HN|HN].
  - exists (S N2). intros n HN2. assert (HN1:(n >= N1)%nat) by omega.
    intros qb Hqb. destruct (Cauchy_exists _ HA n) as [qa Hqa].
    assert (E1: qb == qa - (qa - qb)) by ring.
    assert (E2: qa - (qa - qb) >= qa - Qabs (qa - qb)).
     { apply Qplus_le_compat. apply Qle_refl. apply Qopp_le_compat. apply Qle_Qabs. }
    assert (E3: qa >= eps0).
     { apply (H1 _ HN1 _ Hqa). }
    assert (E4: - Qabs (qa - qb) >= - (eps0 * (1 # 2))).
     { apply (proj2 (Qopp_le_compat_iff _ _)). rewrite Qopp_involutive. rewrite Qopp_involutive.
       apply Qlt_le_weak. apply (H2 n HN2 qa qb Hqa Hqb). }
    assert (E5: eps0 * (1 # 2) <= qa - Qabs (qa - qb)).
     { assert (Et: eps0 * (1 # 2) == eps0 -eps0 * (1 # 2) ) by ring. rewrite Et.
       apply Qplus_le_compat. auto. auto. }
    rewrite E1.
    apply (Qle_trans _ _ _ E5 E2).
  - exists (S N1). intros n HN1. apply not_lt in HN. assert (HN2:(n > N2)%nat) by omega.
    intros qb Hqb. destruct (Cauchy_exists _ HA n) as [qa Hqa].
    assert (E1: qb == qa - (qa - qb)) by ring.
    assert (E2: qa - (qa - qb) >= qa - Qabs (qa - qb)).
     { apply Qplus_le_compat. apply Qle_refl. apply Qopp_le_compat. apply Qle_Qabs. }
    assert (E3: qa >= eps0).
     { assert (Et: le N1 n) by omega. apply (H1 _ Et _ Hqa). }
    assert (E4: - Qabs (qa - qb) >= - (eps0 * (1 # 2))).
     { apply (proj2 (Qopp_le_compat_iff _ _)). rewrite Qopp_involutive. rewrite Qopp_involutive.
       apply Qlt_le_weak. apply (H2 n HN2 qa qb Hqa Hqb). }
    assert (E5: eps0 * (1 # 2) <= qa - Qabs (qa - qb)).
     { assert (Et: eps0 * (1 # 2) == eps0 -eps0 * (1 # 2) ) by ring. rewrite Et.
       apply Qplus_le_compat. auto. auto. }
    rewrite E1.
    apply (Qle_trans _ _ _ E5 E2).
Qed.




