Set Warnings "-notation-overridden,-parsing".
Require Import Psatz.
Require Import Init.
Require Import QArith.
Require Import QArith.Qround.
Require Import Omega.

(***********   This is library ****************)

Definition INQ (n: nat) : Q := inject_Z (Z.of_nat n).

Coercion INQ: nat >-> Q.

Theorem INQ_plus : forall n m : nat , INQ n + INQ m == INQ (n + m).
Proof.
  intros.
  unfold INQ.
  rewrite <- inject_Z_plus.
  apply inject_Z_injective.
  rewrite <- Nat2Z.inj_add. auto.
Qed.

Theorem INQ_minus : forall n m : nat , (n >= m)%nat -> INQ (n - m) == INQ n - INQ m.
Proof.
  intros.
  assert (n - m >= 0)%nat. { omega. }
  remember (n - m)%nat as p.
  assert (n = p + m)%nat. { omega. }
  unfold Qminus.
  rewrite H1. 
  rewrite <- INQ_plus. field. 
Qed.

Theorem INQ_mult : forall n m : nat , INQ n * INQ m == INQ (n * m).
Proof.
  intros.
  unfold INQ.
  rewrite <- inject_Z_mult.
  apply inject_Z_injective.
  rewrite <- Nat2Z.inj_mul. auto.
Qed.

Theorem eq_INQ_Qeq : forall n m : nat, (n = m)%nat -> (INQ n == INQ m).
Proof.
  intros.
  unfold INQ.
  rewrite H. reflexivity.
Qed.

Theorem Qeq_INQ_eq : forall n m : nat ,(INQ n == INQ m) -> (n = m)%nat.
Proof.
  intros.
  unfold INQ in H.
  rewrite inject_Z_injective in H.
  apply Nat2Z.inj. auto.
Qed.

Theorem INQ_le : forall n m : nat, (n >= m)%nat <-> (INQ n) >= (INQ m).
Proof.
  intros.
  unfold INQ.
  split ; intros.
  - rewrite <- Zle_Qle.
    apply inj_le. auto.
  - rewrite <- Zle_Qle in H.
    apply Nat2Z.inj_le. auto.
Qed.

Theorem INQ_lt : forall n m : nat, (n > m)%nat <-> (INQ n) > (INQ m).
Proof.
  intros.
  unfold INQ.
  split ; intros.
  - rewrite <- Zlt_Qlt.
    apply inj_lt. auto.
  - rewrite <- Zlt_Qlt in H.
    apply Nat2Z.inj_lt. auto.
Qed.

Lemma INQ_nonneg: forall n, INQ n >= 0.
Proof.
  intros.
  unfold INQ.
  change 0 with (inject_Z 0).
  rewrite <- Zle_Qle.
  omega.
Qed.

Lemma INQ_S: forall n,  (((S n):Q) = n + 1)%Q.
Proof.
  intros.
  unfold INQ.
  change 1 with (inject_Z 1).
  rewrite <- inject_Z_plus.
  f_equal.
  rewrite Nat2Z.inj_succ.
  omega.
Qed.

Lemma INQ_Qeq_0 : (INQ 0 == 0)%Q.
Proof.
  reflexivity.
Qed.

Lemma INQ_Qeq_1 : (INQ 1 == 1)%Q.
Proof.
  reflexivity.
Qed.

Lemma INQ_eq_1 : (INQ 1 = 1)%Q.
Proof.
  reflexivity.
Qed.

Ltac clear_INQ :=
  repeat rewrite INQ_S in *;
  try change (INQ 0) with (0 # 1) in *.

Ltac solve_nonzero :=
  match goal with
  | |- context [INQ ?n] =>
    generalize (INQ_nonneg n);
    let m := fresh n in
    let H := fresh "H" in
    remember (INQ n) as m eqn:H;
    clear H; try clear n;
    intros
  end.

Lemma Max_pown_0 : forall n : nat , (2 ^ n > 0)%nat.
Proof.
  intros. induction n.
  + simpl. omega.
  + rewrite Nat.pow_succ_r'. omega.
Qed.

Lemma Max_powan_0 : forall (a n : nat), (a > 0)%nat -> (a ^ n > 0)%nat.
Proof.
  intros. induction n.
  + simpl. omega.
  + rewrite Nat.pow_succ_r'. 
    apply Nat.mul_pos_pos ; auto.
Qed.

Lemma Max_pown_0Q : forall n : nat , (INQ (2 ^ n) > 0)%Q.
Proof.
  intros.
  rewrite <- INQ_Qeq_0.
  apply INQ_lt. apply Max_pown_0.
Qed.
  
Lemma Max_powSn_1 : forall n : nat , ( n >= 1 -> 2 ^ n > 1)%nat.
Proof.
  intros.
  induction n.
  - inversion H.
  - simpl. rewrite <- plus_n_O. 
    apply Nat.lt_le_trans with (m := (1 + 2 ^ n) % nat).
    simpl. apply lt_n_S. apply Max_pown_0. 
    apply plus_le_compat_r. 
    pose proof Max_pown_0 n.
    apply H0.
Qed.
  
Lemma Z_le_lt_trans : forall z1 z2 z3 :Z , (z1 <= z2 -> z2 < z3 -> z1 < z3)%Z.
Proof.
  intros.
  apply Zle_compare in H.
  destruct ((z1 ?= z2) % Z) eqn : En.
  - apply Z.compare_eq in En. rewrite En. auto.
  - apply Zcompare_Lt_trans with z2 ; auto.
  - inversion H.
Qed.
  
Lemma Z_to_nat_le : forall z : Z , (inject_Z z <= Z.to_nat z)%Q.
Proof.
  intros.
  destruct z ; unfold Qle.
  - simpl. omega.
  - remember (Z.pos p) as p0.
    simpl.
    rewrite !Zmult_1_r.
    pose proof Zle_0_pos p.
    pose proof Z2Nat.id (Z.pos p) H.
    rewrite <- Heqp0 in H0. omega.
  - simpl.
    apply Z.lt_le_incl.
    apply Zlt_neg_0.
Qed.
  
Lemma eps_lemma1 : forall eps : Q , (eps > 0)%Q -> { n : nat | (INQ (n) > 1 / eps)%Q}.
Proof.
  intros.
  exists (S (Z.to_nat (Qceiling (1 / eps)))).
  rewrite INQ_S.
  apply Qlt_le_trans with (y := (inject_Z (Qceiling (1/eps)) + 1)%Q).
  - pose proof  (Qle_ceiling (1/eps)).
    rewrite Qplus_comm.
    rewrite <- Qplus_0_l at 1.
    apply Qplus_lt_le_compat ; auto.
    unfold Qlt. simpl. omega.
  - apply Qplus_le_l.
    remember (Qceiling (1 / eps)) as z.
    apply Z_to_nat_le.
Qed.
  
Lemma eps_lemma_total : forall eps : Q , { n : nat | (INQ (n) > 1 / eps)%Q}.
Proof.
  intros.
  destruct (Q_dec 0 eps).
  - destruct s. 
    + apply eps_lemma1. auto.
    + exists O.
      rewrite INQ_Qeq_0.
      rewrite <- Qopp_opp.
      rewrite <- (Qopp_opp 0).
      apply Qopp_lt_compat.
      apply Qopp_lt_compat in q as goal.
      assert ( -0 == 0). { reflexivity. }
      rewrite H in *.
      apply Qinv_lt_0_compat in goal.
      assert (/ - eps == - (1 / eps)). 
      { field. unfold not. intros. rewrite H0 in q. apply (Qlt_irrefl 0). auto. }
      rewrite <- H0. auto.
  - exists 1%nat. rewrite <- q. 
    rewrite INQ_Qeq_1.
    unfold Qlt. simpl. omega. 
Qed.

Definition eps_arrow_nat(eps : Q) : nat.
  pose proof eps_lemma_total eps.
  inversion H.
  apply x.
Defined.
  
Lemma eps_arrow_correct : forall eps : Q , (INQ(eps_arrow_nat eps ) >  1 / eps)%Q.
Proof.
  intros.
  unfold eps_arrow_nat.
  destruct (eps_lemma_total eps).
  auto.
Qed.
  
Lemma eps_arrow_pro : forall eps : Q, (eps > 0)%Q -> (INQ(eps_arrow_nat eps) > 0)%Q.
Proof.
  intros.
  pose proof eps_arrow_correct eps.
  remember (eps_arrow_nat eps) as n0.
  apply Qlt_trans with (y := 1 / eps) ; auto.
  assert (1 / eps == / eps). { field. unfold not. intros. rewrite H1 in H.
         apply (Qlt_irrefl 0). auto. }
  rewrite H1.
  apply Qinv_lt_0_compat ; auto.
Qed.