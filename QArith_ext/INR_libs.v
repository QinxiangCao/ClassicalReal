Set Warnings "-notation-overridden,-parsing".
Require Import Psatz.
Require Import Init.
Require Import QArith.
Require Import QArith.Qround.
Require Import Omega.

(***********   This is library ****************)

Definition INR (n: nat) : Q := inject_Z (Z.of_nat n).

Coercion INR: nat >-> Q.

Lemma INR_le : forall n m : nat, (n >= m)%nat -> (INR n) >= (INR m).
Proof.
  intros.
  unfold INR.
  rewrite <- Zle_Qle.
  apply inj_le. auto.
Qed.

Lemma INR_lt : forall n m : nat, (n > m)%nat -> (INR n) > (INR m).
Proof.
  intros.
  unfold INR.
  rewrite <- Zlt_Qlt.
  apply inj_lt. auto.
Qed.

Lemma INR_nonneg: forall n, INR n >= 0.
Proof.
  intros.
  unfold INR.
  change 0 with (inject_Z 0).
  rewrite <- Zle_Qle.
  omega.
Qed.

Lemma INR_S: forall n,  (((S n):Q) = n + 1)%Q.
Proof.
  intros.
  unfold INR.
  change 1 with (inject_Z 1).
  rewrite <- inject_Z_plus.
  f_equal.
  rewrite Nat2Z.inj_succ.
  omega.
Qed.

Ltac clear_INR :=
  repeat rewrite INR_S in *;
  try change (INR 0) with (0 # 1) in *.

Ltac solve_nonzero :=
  match goal with
  | |- context [INR ?n] =>
    generalize (INR_nonneg n);
    let m := fresh n in
    let H := fresh "H" in
    remember (INR n) as m eqn:H;
    clear H; try clear n;
    intros
  end.
