Set Warnings "-notation-overridden,-parsing".
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.

Lemma Qabs_triangle_extend: forall (a b c:Q), Qabs (a - c) <=
   Qabs (a - b) + Qabs (b - c).
Proof. intros.
    assert (Heq: a - c == (a - b) + (b - c)) by ring.
    rewrite Heq.
    apply Qabs_triangle.
Qed.
Lemma eps_divide_2_positive: forall (eps:Q), 0 < eps -> eps * (1 # 2) > 0.
Proof. intros. unfold Qmult. unfold Qlt. simpl.
    rewrite <- Zmult_assoc. simpl. apply H.
Qed.


Lemma eps_divide_2M_positive: forall (eps M:Q), 0 < eps -> 0 < M -> eps * (1 # 2) *(/M) > 0.
Proof. intros.
  apply (Qmult_lt_r _ _ _ H0). rewrite Qmult_0_l.
  rewrite <- (Qmult_assoc (eps * (1 # 2))). rewrite (Qmult_comm _ M). rewrite Qmult_inv_r.
  rewrite Qmult_1_r. apply eps_divide_2_positive. apply H.
  intros contra. rewrite contra in H0. discriminate.
Qed.
Lemma Qabs_0: forall q, Qabs q == 0 -> q==0.
Proof. intros. assert (Qabs q <= 0). { apply Qle_lteq. right. auto. }
apply Qabs_Qle_condition in H0. destruct H0.
apply Qle_lteq in H0. destruct H0.
- assert (nonsense: -0 < 0). { apply (Qlt_le_trans _ _ _ H0 H1). } discriminate nonsense.
- rewrite H0. reflexivity.
Qed. 

Lemma Qnot_0_abs: forall (q:Q), ~(q==0) -> ~(Qabs q == 0).
Proof.
intros. intros contra. apply Qabs_0 in contra. contradiction. 
Qed.
Lemma Qabs_not_0: forall (q:Q),  ~(Qabs q == 0) -> ~(q==0).
Proof.
intros. intros contra. rewrite contra in H. apply H. reflexivity.
Qed.

Lemma Qlt_not_0: forall (q:Q), q>0 -> ~(q==0).
Proof. intros. intros Con. rewrite Con in H. discriminate H.
Qed.
Lemma Qinv_not_0: forall(q:Q), ~(/q == 0) -> ~(q==0).
Proof. intros. intros C. rewrite C in H. apply H. reflexivity. Qed.

Lemma Qmult_lt_compat_trans_positive: forall a b c d, a >= 0 -> c > 0
  -> a < b -> c <= d -> a*c < b*d.
Proof. intros. apply (Qle_lt_trans _ (a*d)).
  - rewrite Qmult_comm. rewrite (Qmult_comm a). apply Qmult_le_compat_r.
    apply H2. apply H.
  - assert (E:d>0). { apply (Qlt_le_trans _ c). auto. auto. }
    apply (Qmult_lt_r _ _ _ E). auto.
Qed.

Lemma Qmult_le_compat_nonneg: forall (a1 b1 a2 b2:Q), 0 <= a1 -> 0 <= b1 
  -> a1 <= a2 -> b1 <= b2 -> a1 * b1 <= a2 * b2.
Proof. intros. apply (Qle_trans _ (a1*b2)).
  - rewrite (Qmult_comm a1). rewrite (Qmult_comm a1).
    apply Qmult_le_compat_r. apply H2. apply H.
  - apply Qmult_le_compat_r. apply H1. apply (Qle_trans _ b1). 
    apply H0. apply H2.
Qed.

Lemma Qmult_lt_compat_nonneg: forall (a1 b1 a2 b2:Q), 0 <= a1 -> 0 <= b1 
  -> a1 < a2 -> b1 < b2 -> a1 * b1 < a2 * b2.
Proof. intros. apply Qle_lteq in H.  destruct H.
  - assert (E: a1 * b1 < a1 * b2). 
  { rewrite Qmult_comm. rewrite (Qmult_comm a1). apply Qmult_lt_compat_r. auto. auto. } 
  apply (Qlt_le_trans _ _ _ E). assert (E': b2 > 0). { apply (Qle_lt_trans _ b1). auto. auto. }
  apply (Qmult_le_r _ _ _ E'). apply Qlt_le_weak. auto.
  - rewrite <- H. rewrite Qmult_0_l. rewrite <- H in H1. 
    assert (E: 0 == a2 * 0) by ring. rewrite E. apply (Qmult_lt_l _ _ _ ). auto.
    apply (Qle_lt_trans _ b1). auto. auto.
Qed.

Lemma Qopp_lt_compat : forall p q, p<q -> -q < -p.
Proof. intros. assert(H1:p<q) by auto. apply Qlt_le_weak in H.
  apply Qopp_le_compat in H. apply Qle_lteq in H.
  destruct H. auto.
  assert (E: p == q). rewrite <- Qopp_involutive. rewrite <- H.
  rewrite Qopp_involutive. reflexivity. rewrite E in H1.
  apply Qlt_irrefl in H1. contradiction.
Qed.

Lemma Qopp_le_compat_iff: forall p q, p<=q <-> -q <= -p.
Proof. split. apply Qopp_le_compat.
  intros. rewrite <- (Qopp_involutive q), <- (Qopp_involutive p).
  apply Qopp_le_compat. apply H.
Qed.
