Set Warnings "-notation-overridden,-parsing".
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Logic.Classical.

Lemma Pos1 : forall p : positive, (1 <= Z.pos p)%Z.
Proof.
intros.
apply Pos2Z.pos_le_pos.
apply Pos.le_1_l.
Qed.

Lemma ZQ0 : (0==inject_Z 0)%Q.
Proof.
reflexivity.
Qed.

Lemma inject_Z_le : forall x : Q, exists m : Z, inject_Z m >= x.
Proof.
    destruct x. 
    assert(Qnum >= 0 \/~ Qnum >= 0)%Z. apply classic. destruct H.
  - exists Qnum. unfold inject_Z.
    assert(~ Qden < 1)%positive.
    { apply Pos.nlt_1_r. }
    apply Pos.le_nlt in H0.
    rewrite Qmake_Qdiv. rewrite Qmake_Qdiv.
    rewrite <- (Qmult_1_r (inject_Z Qnum / inject_Z 1)).
    rewrite (Qdiv_mult_l (inject_Z Qnum) (/ inject_Z 1) ).
    { apply Qle_shift_div_r.
    { reflexivity. }
      rewrite Qmult_comm. rewrite <- Qmult_1_l. rewrite Qmult_assoc.
      apply Qmult_le_compat_r.
      { rewrite Qmult_1_r. unfold inject_Z. apply Pos1. }
        rewrite ZQ0.
        rewrite <- Zle_Qle. apply Z.ge_le. apply H. }
      unfold not. intros. inversion H1.
  - exists 0%Z. unfold inject_Z. apply Znot_ge_lt in H.
    rewrite Qmake_Qdiv. apply Qle_shift_div_r.
    + reflexivity.
    + rewrite Qmult_0_l. rewrite ZQ0. rewrite <- Zle_Qle.
      apply Zlt_le_weak. apply H.
Qed.

Lemma Z_of_nat_le : forall m:Z, exists n:nat, (m <= Z.of_nat n)%Z.
Proof.
  intros. assert(m <= 0 \/ ~ m <= 0)%Z. apply classic.
  destruct H.
  - exists 1%nat. apply Z.le_trans with (m:=0%Z).
    apply H. apply Nat2Z.is_nonneg.
  - exists (Z.to_nat m). rewrite Z2Nat.id.
    reflexivity.
    rewrite <- Z.lt_nge in H.
    apply Zlt_le_weak. apply H.
Qed.

Lemma inject_Z_of_nat_le :
  forall x : Q, exists n: nat, inject_Z (Z.of_nat n) >= x.
Proof.
 intros. assert(forall m:Z, exists n:nat, (m <= Z.of_nat n)%Z).
  { apply Z_of_nat_le. }
  assert(forall x : Q, exists m : Z, inject_Z m >= x).
  { apply inject_Z_le. }
  destruct (H0 x).
  destruct (H x0).
  exists x1. apply Qle_trans with (y:=(inject_Z x0)).
  - apply H1.
  - rewrite <- Zle_Qle. apply H2.
Qed.

Lemma le_inject_Z : forall x : Q, exists m : Z, inject_Z m <= x.
Proof.
    destruct x.
    assert(Qnum >= 0 \/~ Qnum >= 0)%Z. apply classic. destruct H.
  - exists 0%Z. rewrite Qmake_Qdiv.
    apply Qle_shift_div_l.
    + rewrite ZQ0. rewrite <- Zlt_Qlt. reflexivity.
    + rewrite Qmult_0_l. rewrite ZQ0. rewrite <- Zle_Qle.
      apply Z.ge_le. apply H.
  - apply Znot_ge_lt in H. exists Qnum. unfold inject_Z.
    assert(~ Qden < 1)%positive.
    { apply Pos.nlt_1_r. }
    apply Pos.le_nlt in H0.
    rewrite Qmake_Qdiv. rewrite Qmake_Qdiv.
    rewrite <- (Qmult_1_r (inject_Z Qnum / inject_Z 1)).
    rewrite (Qdiv_mult_l (inject_Z Qnum) (/ inject_Z 1) ).
    { apply Qle_shift_div_l.
    { reflexivity. }
      rewrite Qmult_comm. rewrite <- inject_Z_mult.
      rewrite <- Zle_Qle. rewrite <- Zmult_1_l.
      apply Z.mul_le_mono_neg_r. auto.
      apply Pos1. }
    unfold not. intros. inversion H1.
Qed.

Lemma le_Z_of_nat : forall m:Z,(0 <= m)%Z -> exists n:nat, (Z.of_nat n <= m)%Z.
Proof.
  intros.
  exists 0%nat. apply H.
Qed.
