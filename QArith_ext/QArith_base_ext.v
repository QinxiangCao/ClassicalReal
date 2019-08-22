Set Warnings "-notation-overridden,-parsing".
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Field.
From Coq Require Import Psatz.
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

Lemma Qle_Qplus_Qle : forall a b c d : Q , a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros. lra.
Qed.

Lemma Qlt_Qplus_Qlt : forall a b c d : Q , a < b -> c < d -> a + c < b + d.
Proof.
  intros. lra.
Qed.

Lemma Qle_Qplus_Qlt : forall a b c d : Q , a <= b -> c < d -> a + c < b + d.
Proof.
  intros. lra.
Qed.

Lemma Qlt_Qplus_Qle : forall a b c d : Q , a < b -> c <= d -> a + c < b + d.
Proof.
  intros. lra.
Qed.

Lemma Qabs_diff_Qlt_condition : forall a b c : Q , Qabs (a - b) < c <-> a < b + c /\ a > b - c.
Proof.
  split ; intros.
  - split ; rewrite <- (Qplus_lt_l _ _ (-b)).
    + assert (b + c + - b == c)%Q. { ring. }
      rewrite H0.
      apply Qle_lt_trans with (Qabs(a - b)) ; auto.
      apply Qle_Qabs.
    + assert (b - c + - b == - c)%Q. { ring. }
      rewrite H0. 
      assert (b + - a < c).
      { rewrite Qabs_Qminus in H.
        apply Qle_lt_trans with (Qabs(b - a)) ; auto.
        apply Qle_Qabs. 
      }
      lra.
  - destruct H.
    apply Qabs_case ; lra.
Qed.
