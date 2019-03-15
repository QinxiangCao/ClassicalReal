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
From CReal Require Import Dedekind.ROrder.
Import ListNotations.

(** Second , we will define the plus operation of Set and Real and proof some theorem about it. *)

Definition Cut_plus_Cut (A : Q -> Prop) (B : Q -> Prop) : Q -> Prop :=
  (fun x => exists x0 x1 : Q, A x0 /\ B x1 /\ (Qeq (x0 + x1) x))
.

Theorem Dedekind_plus : forall A B, Dedekind A -> Dedekind B -> Dedekind (Cut_plus_Cut A B).
Proof.
  intros.
  rename H into DA, H0 into DB.
  split.
  - destruct (Dedekind_properties1 _ DA).
    destruct (Dedekind_properties1 _ DB).
    split.
    + inversion H.
      inversion H1.
      exists (x0 + x), x , x0.
      split.
      * apply H3.
      * split. 
        apply H4.
        apply Qplus_comm.
    + inversion H0. inversion H2.
      unfold not in *.
      exists (x + x0).
      intros. destruct H5. destruct H5.
      assert (H' : x > x1 /\ x0 > x2).
      {
        split.
        apply Dedekind_le with A.
        apply DA. unfold not. apply H3. apply H5.
        apply Dedekind_le with B.
        apply DB. unfold not. apply H4. apply H5.
      }
      assert (H'' : Qlt (x1 + x2)(x + x0)).
      {
        apply Qplus_lt_le_compat.  apply H'.
        apply Qlt_le_weak.  apply H'.
      }
      destruct H5.  destruct H6. rewrite H7 in H''.
      apply Qlt_irrefl with (x + x0). apply H''.
  - intros.
    destruct H. destruct H. destruct H.
    unfold Cut_plus_Cut.
    exists x , (q + - x).
    split; [apply H |].
    split; [apply (Dedekind_properties2 _ DB) with x0 |].
    split; [apply H |]. 
    apply Qplus_le_l with (z := x).
    destruct H. destruct H1.
    rewrite Qplus_comm in H2.
    rewrite H2.  apply Qle_trans with q.
    rewrite <- Qplus_assoc.  rewrite (Qplus_comm (- x)).
    rewrite Qplus_opp_r.  rewrite Qplus_0_r.
    apply Qle_refl. apply H0.
    rewrite Qplus_comm. rewrite <- Qplus_assoc.
    rewrite (Qplus_comm (- x)).  rewrite Qplus_opp_r.
    apply Qplus_0_r.
  - intros.
    repeat destruct H. destruct H0.
    apply (Dedekind_properties3 _ DA) in H.
    apply (Dedekind_properties3 _ DB) in H0 as goal.
    destruct H. destruct goal.
    exists (x1 + x0).
    split. unfold Cut_plus_Cut.
    exists x1,x0.
    split. apply H.
    split. apply H0. reflexivity.
    rewrite <- H1.
    apply Qplus_lt_l.  apply H.
  - intros.
    repeat destruct H0.
    unfold Cut_plus_Cut.
    exists x,x0.
    split. apply H0.
    split. apply H1.
    rewrite <- H. apply H1.
Qed.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_cons A HA) => match b with
                            | (Real_cons B HB) =>
                               Real_cons (Cut_plus_Cut A B) (Dedekind_plus A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B).

Theorem Rplus_O_r : forall a : Real, a + Rzero == a.
Proof.
  intros.
  destruct a.
  unfold Rplus.
  simpl.
  unfold Reqb.
  unfold Rle.
  rename H into DA.
  split.
  - intros.
    destruct H.
    destruct H.
    apply (Dedekind_properties2 _ DA) with x0.
    split.
    + apply H.
    + destruct H. destruct H0.
      rewrite <- Qplus_0_r with (x := x0).
      rewrite <- H1.
      apply Qplus_le_r.
      apply Qlt_le_weak. apply H0.
  - intros.
    unfold Cut_plus_Cut.
    apply (Dedekind_properties3 _ DA) in H.
    destruct H.
    exists x0,(Qplus x (-x0)).
    split.
    + apply H.
    + split.
      * apply Qplus_lt_l with (z := x0).
        rewrite Qplus_0_l.
        rewrite <- Qplus_assoc.
        rewrite Qplus_comm with (y := x0).
        rewrite Qplus_opp_r.
        rewrite Qplus_0_r. apply H.
      * rewrite Qplus_comm.
        rewrite <- Qplus_assoc.
        rewrite Qplus_comm with (y := x0).
        rewrite Qplus_opp_r.
        apply Qplus_0_r.
Qed. 

Theorem Rplus_comm : forall a b : Real, a + b == b + a.
Proof.
  intros.
  destruct a.
  destruct b.
  unfold Reqb.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H1; destruct H2; exists x1,x0.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
Qed.

Theorem Rplus_assoc : forall a b c : Real, a + b + c == a + (b + c).
Proof.
  intros.
  destruct a.
  destruct b.
  destruct c.
  unfold Reqb.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H2; repeat destruct H3.
  - exists x2 , (Qplus x (-x2)).
    split. apply H2.
    split.
    + exists x3 , x1.
      split. apply H4.
      split. apply H3.
      rewrite <- H5. destruct H4. rewrite <- H6.
      remember (Qplus x3 x1) as xp.
      rewrite <- Qplus_comm. rewrite <- Qplus_assoc. rewrite <- Heqxp.
      rewrite Qplus_comm with (y := xp).
      rewrite Qplus_comm. rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      symmetry. apply Qplus_0_r.
    + rewrite Qplus_comm with (x := x).
      rewrite Qplus_assoc. rewrite Qplus_opp_r. apply Qplus_0_l.
  - exists (Qplus x (-x3)) , x3.
    split.
    + exists x0,x2.
      split. apply H2.
      split. apply H3.
      rewrite <- H4. destruct H5. rewrite <- H6.
      rewrite <- Qplus_assoc.
      rewrite <- Qplus_assoc.
      rewrite Qplus_opp_r. rewrite Qplus_0_r. reflexivity.
    + split. apply H5.
      rewrite <- Qplus_assoc.
      rewrite Qplus_comm with (y:=x3).
      rewrite Qplus_opp_r.
      apply Qplus_0_r.
Qed.

Definition Cut_opp (A : Q -> Prop) : Q -> Prop :=
  (fun x => exists r : Q, (r > 0 /\ ~(A (Qplus (-x) (-r)))))
.

Theorem Dedekind_opp : forall A : Q -> Prop , Dedekind A -> Dedekind (Cut_opp A).
Proof.
  intros.
  rename H into DA.
  unfold Cut_opp.
  split.
  - destruct (Dedekind_properties1 _ DA). split.
    + destruct H0.
      exists (Qplus (- x) (-1 # 1) ), 1.
      remember (Qplus (- x) (-1 # 1) ) as x0.
      unfold not in *. split. reflexivity. intros.   apply H0.
      apply (Dedekind_properties4 _ DA) with (p := Qplus (- x0)  (- (1))).
      * apply Qplus_inj_l with (z := x0).
        rewrite Qplus_assoc.  rewrite Qplus_opp_r.
        rewrite Qplus_0_l. rewrite Qplus_comm.
        rewrite Heqx0.
        rewrite Qplus_assoc. rewrite Qplus_opp_r.
        reflexivity.
      * apply H1.
    + destruct H.
      exists (-x).
      apply not_exists_dist.
      intros.
      unfold not.
      intros.
      assert (H' : (Qlt 0 x0) -> A (Qplus (Qopp(Qopp(x))) (Qopp x0))).
      { intros.
        assert(H':Qeq (Qopp(Qopp(x))) x).
        { apply Qopp_involutive. }
        { apply (Dedekind_properties2 _ DA x).
          split.
          * apply H.
          * rewrite <- (Qplus_0_r x).
            apply Qplus_le_compat. rewrite Qplus_0_r. rewrite H'. apply Qle_refl.
            apply (Qopp_le_compat 0 x0).
            apply Qlt_le_weak. apply H2. } }
      destruct H1. apply H2. apply H'. apply H1.
  - intros. destruct H. destruct H. destruct H. 
    exists x. split.
    + apply H.
    + unfold not. intros. apply H1. apply (Dedekind_properties2 _ DA (Qplus (Qopp q) (Qopp x))).
      split.
      * apply H2.
      * apply Qplus_le_compat. apply Qopp_le_compat. apply H0. apply Qle_refl.
  - intros.
    inversion H.
    exists (Qplus p (x * / (2 # 1))).
    split.
    exists (x * / (2 # 1)).
    split.
    + assert (H' : Qeq 0 (0 * / (2 # 1))).
      { reflexivity. }
      rewrite H'.
      apply Qmult_lt_compat_r.
      reflexivity.
      apply H0.
    + unfold not in *.
      intros. apply H0.
      apply (Dedekind_properties4 _ DA) with (p := Qplus (- (Qplus p  (x * / (2 # 1)))) (-(x * / (2 # 1)))).
      assert (H' : Qeq x (Qplus (x * / (2 # 1)) (x * / (2 # 1)))).
      { rewrite <- Qmult_plus_distr_r. rewrite <- Qmult_1_r.
        rewrite <- Qmult_assoc.
        rewrite Qmult_inj_l with (z := x).
        reflexivity.
        apply Qnot_eq_sym. apply Qlt_not_eq. apply H0.
      }
      apply Qplus_inj_l with (z := Qplus p (x * / (2 # 1))).
      rewrite Qplus_assoc. rewrite Qplus_opp_r.
      rewrite Qplus_0_l.  rewrite Qplus_assoc.  rewrite Qplus_comm.
      rewrite Qplus_comm with (x := p).
      rewrite <- Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_r.
      rewrite Qplus_comm.
      apply Qplus_inj_l with (z := (x * / (2 # 1))).
      rewrite Qplus_opp_r. rewrite Qplus_assoc.
      rewrite <- H'. symmetry.
      apply Qplus_opp_r.
      apply H1.
    + rewrite <- Qplus_0_r.
      rewrite <- Qplus_assoc.
      rewrite Qplus_lt_r with (z := p).
      rewrite Qplus_0_l.
      apply Qlt_shift_div_l ; try (reflexivity).
      assert (H' : Qeq 0 (0 * (2 # 1))).
      { reflexivity. }
      rewrite <- H'. apply H0.
  - intros.
    inversion H0.
    exists x.
    split. apply H1.
    unfold not in *.
    intros.
    apply H1.
    apply (Dedekind_properties4 _ DA) with (p := Qplus (-q) (-x)).
    apply Qplus_inj_r.
    apply Qplus_inj_l with (z := Qplus p q).
    rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
    rewrite Qplus_0_r.
    rewrite <- Qplus_assoc. rewrite Qplus_comm with (x := q). 
    rewrite Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_l.
    apply H. apply H2.
Qed.

Definition Ropp (a : Real) : Real :=
  match a with
    | Real_cons A HA => Real_cons (Cut_opp A) (Dedekind_opp A HA)
  end.

Theorem Rplus_opp :
  forall a : Real, a + (Ropp a) == Rzero.
Proof.
  intros.
  destruct a.
  unfold Reqb.
  simpl. split.
  - intros.
    repeat destruct H0.
    destruct H1.
    destruct H1.
    destruct H1.
    rewrite <- H2.
    apply Qplus_lt_l with (z := (-x1)).
    rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
    rewrite Qplus_0_r. rewrite Qplus_0_l.
    apply Qlt_trans with (y := Qplus (-x1) (-x2)).
    apply Dedekind_le with A ; auto.
    apply Qplus_lt_r with (z := Qplus x2 x1).
    rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite <- Qplus_comm. rewrite Qplus_assoc. 
    rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite Qplus_comm.
    rewrite Qplus_opp_r. rewrite Qplus_0_r. apply H1.
  - intros.
    unfold Cut_plus_Cut.
    rename H into DA.
    destruct (Dedekind_properties1 _ DA).
    destruct H.
    exists x0, (Qplus (-x0) x).
    split; [apply H |].
    split.
    * unfold Cut_opp.
      destruct H1.
      exists (Qplus (-x1) (Qplus (-x0) (-x))).
      split.
     ++ apply Qplus_lt_l with (z := Qplus x0 x).
        rewrite Qplus_0_l. rewrite <- Qplus_assoc.
        assert (H' : Qeq (Qplus (Qplus (-x0) (-x)) (Qplus x0 x)) 0).
        {
          rewrite Qplus_assoc.
          rewrite Qplus_comm.
          rewrite <- Qplus_assoc.
          rewrite Qplus_comm with (y := Qplus (-x) x0).
          rewrite <- Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_r.
          apply Qplus_opp_r.
        }
        rewrite H'. 
        apply Qplus_lt_le_compat.
        apply Dedekind_le with A ; auto.
Abort.

Theorem Rplus_l_compat :
  forall a b c : Real, b == c -> a + b == a + c.
Proof. 
  unfold Reqb, Rle. destruct a, b, c. simpl. unfold Cut_plus_Cut.
  intros.
  destruct H2.
  split.
  - intros.
    destruct H4, H4, H4, H5.
    exists x0, x1.
    split. apply H4.
    split. apply H2, H5.
    apply H6.
  - intros.
    destruct H4, H4, H4, H5.
    exists x0, x1.
    split. apply H4.
    split. apply H3, H5.
    apply H6.
Qed.

Theorem Rplus_compat_l :
  forall a b c : Real, a + b == a + c -> b == c.
Proof. 
Admitted.

(** Third , we will define the plus operation of Set and Real and proof some theorem about it. 
Theorem Rmult_O : forall a : Real, a * Rzero == Rzero.
Proof.
Admitted.

Theorem Rmult_1 : forall a : Real, a * Rone == a.
Proof.
Admitted.

Theorem Rmult_comm : forall a b : Real, a * b == b * a.
Proof.
Admitted.

Theorem Rmult_assoc : forall a b c : Real, a * b * c == a * (b * c).
Proof.
Admitted.

Theorem Rmult_distr :
  forall a b c : Real, a * (b + c) == (a * b) + (a * c).
Proof.
Admitted.

Theorem Rmult_inv :
  forall a : Real, (a <> Rzero) -> exists b, a * b == Rone.
Proof.
Admitted.
*)
