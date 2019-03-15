Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From CReal Require Import Dedekind.RBase.
Import ListNotations.

(** Next, we will define the plus operation and the mult operation. *)
(** First, we will define order of Real and proof some theorem about the order.*)
Definition Rle (a b:Real) : Prop :=
  match a with
    | Real_cons A HA => match b with
                          | Real_cons B HB => (forall x , A x -> B x)
                        end
  end.

Notation "a <= b" := (Rle a b).

Definition Rlt (a b:Real) : Prop :=
  match a with
    | Real_cons A HA => match b with
                          | Real_cons B HB => (forall x , A x -> B x) /\ (exists x , B x /\ ~(A x))
                        end
  end.

Notation "a < b" := (Rlt a b).

Definition Reqb(a b : Real) : Prop := a <= b /\ b <= a.

Notation "a == b" := (Reqb a b).

Theorem Rle_refl: forall x : Real, x <= x.
Proof.
  intros.
  destruct x.
  unfold Rle.
  intros. apply H0.
Qed.

Theorem Reqb_refl: forall x : Real, x == x.
Proof.
  intros.
  unfold Reqb.
  split.
  apply Rle_refl.
  apply Rle_refl.
Qed.

Theorem Rlt_le_weak: forall x y : Real, x < y -> x <= y.
Proof.
  intros.
  destruct x.
  destruct y.
  inversion H.
  unfold Rle.
  apply H2.
Qed.

Theorem Rle_trans: forall x y z : Real, x <= y -> y <= z -> x <= z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  intros.
  apply H0. apply H. apply H4.
Qed.

Theorem Rlt_trans: forall x y z : Real, x < y -> y < z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H. destruct H0. inversion H4. inversion H5. 
    exists x. split. apply H0. apply H6. apply H6.
Qed.

Theorem Rle_not_lt: forall x y : Real, x <= y -> ~ y < x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold not.
  unfold Rle in *.
  unfold Rlt.
  simpl.
  intros.
  destruct H2.
  inversion H3.
  destruct H4.
  apply H in H4.
  apply H5. apply H4.
Qed.

Theorem Rlt_not_le: forall x y : Real, x < y -> ~ y <= x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold not.
  unfold Rle.
  unfold Rlt in *.
  simpl.
  intros.
  destruct H.
  inversion H3.
  destruct H4.
  apply H2 in H4.
  apply H5. apply H4.
Qed.

Theorem Rle_antisym: forall x y : Real, x <= y -> y <= x -> x == y.
Proof.
  intros.
  unfold Reqb.
  split. apply H. apply H0.
Qed.

Theorem Rle_lt_trans: forall x y z : Real, x <= y -> y < z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H0.
    destruct H4.
    exists x.
    split.
    + apply H4.
    + unfold not in *.
      intros.
      apply H4. apply H. apply H5.
Qed.

Theorem Rlt_le_trans: forall x y z : Real, x < y -> y <= z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H.
    destruct H4.
    exists x.
    split.
    + apply H0. apply H4.
    + unfold not in *.
      intros.
      apply H4. apply H5.
Qed.

Theorem not_exists_not_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) <-> (forall x, P x).
Proof.
  split.
  - apply not_ex_not_all.
  - unfold not. intros. destruct H0. apply H0. apply H.
Qed.

Theorem not_exists_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, P x) <-> (forall x, ~ P x).
Proof.
  split.
  - apply not_ex_all_not.
  - unfold not. intros. destruct H0. apply H in H0. apply H0.
Qed.

Theorem Rnot_le_lt: forall x y : Real, ~ x <= y -> y < x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold Rle in *.
  unfold Rlt in *.
  destruct H0, H1.
  split.
  - apply not_all_ex_not in H.
    rewrite <- not_exists_not_dist.
    unfold not in *. intros.
    destruct H, H0.
    assert(H': Qle x x0 \/ Qle x0 x).
    { assert(H'':Qle x x0 \/ ~ Qle x x0). apply classic.
      destruct H''.
      - left. apply H1.
      - right. apply Qnot_le_lt in H1. apply Qlt_le_weak. apply H1. }
    destruct H'.
    + apply H0. intros. exfalso. apply H. intros.
      apply (Dedekind_properties10 x0 x ).
      split.
      apply H2. apply H1.
    + apply H. intros. exfalso. apply H0. intros.
      apply (Dedekind_properties6 x x0 ).
      split.
      apply H2. apply H1.
  - apply not_all_ex_not in H.
    destruct H.
    exists x.
    split.
    + apply not_imply_elim in H. apply H.
    + apply not_imply_elim2 in H. apply H.
Qed.

Theorem Rnot_lt_le: forall x y : Real, ~ x < y -> y <= x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold Rle in *.
  unfold Rlt in *.
  destruct H0, H1.
  apply not_and_or in H.
  destruct H.
  - apply not_all_ex_not in H.
    rewrite <- not_exists_not_dist.
    unfold not in *. intros.
    destruct H, H0.
    assert(H': Qle x x0 \/ Qle x0 x).
    { assert(H'':Qle x x0 \/ ~ Qle x x0). apply classic.
      destruct H''.
      - left. apply H1.
      - right. apply Qnot_le_lt in H1. apply Qlt_le_weak. apply H1. }
    destruct H'.
    + apply H0. intros. exfalso. apply H. intros.
      apply (Dedekind_properties10 x0 x ).
      split.
      apply H2. apply H1.
    + apply H. intros. exfalso. apply H0. intros.
      apply (Dedekind_properties6 x x0 ).
      split.
      apply H2. apply H1.
  - rewrite not_exists_dist in H.
    intros.
    assert(H': ~(A0 x /\ ~ A x)).
    { apply H. }
    apply not_and_or in H'.
    destruct H'.
    + exfalso. apply H1. apply H0.
    + apply NNPP in H1. apply H1.
Qed.

