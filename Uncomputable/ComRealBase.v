(** Uncomputablity in the definition of R function **)
(** For convenience's sake, we focus on real numbers in [0,1] **) 
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
From CReal Require Import INR_libs.
From CReal Require Import QArith_base_ext.

Module Type VIR_R.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv : R -> R.
  Parameter Rlt : R -> R -> Prop.
  Parameter Rabs : R -> R.
  Parameter up : R -> Z.
  Parameter IZR : Z -> R.
  Parameter IQR : Q -> R.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  Definition Rdiv (r1 r2 :R) : R := r1 * / r2.
  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Parameter Rpow : R -> nat ->R. 
  Parameter Rlim : (nat -> R) -> R -> Prop.
  Definition Reqb (x y : R) : Prop := x = y.
  Notation "x == y" := (Reqb x y) (no associativity, at level 70).
  Parameter Rlt_irrefl : forall r1 : R , ~ (r1 < r1).
  Parameter R_dec : forall r r1 : R , r <= r1 \/ r > r1.
  Parameter IQR_R0 : IQR (0%Q) = R0.
  Parameter IQR_R1 : IQR (1%Q) = R1.
  Parameter IQR_plus : forall r1 r2 : Q , IQR r1 + IQR r2 = IQR (r1 + r2).
  Parameter IQR_minus : forall r1 r2 : Q , IQR r1 - IQR r2 = IQR (r1 - r2).
  Parameter IQR_mult : forall r1 r2 : Q, IQR r1 * IQR r2 = IQR (r1 * r2).
  Parameter IQR_inv : forall r : Q, (~ r == 0)%Q -> / IQR r = IQR (/ r).
  Parameter IQR_le : forall r1 r2 : Q , (r1 <= r2)%Q <-> IQR r1 <= IQR r2.
  Parameter IQR_lt : forall r1 r2 : Q , (r1 < r2)%Q <-> IQR r1 < IQR r2.
  Parameter IQR_eq : forall r1 r2 : Q , (r1 = r2)%Q <-> IQR r1 = IQR r2.
  Parameter Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Parameter Rabs_pos : forall r1 : R , (r1 >= R0) -> Rabs r1 = r1.
  Parameter Rabs_neg : forall r1 : R , (r1 <= R0) -> Rabs r1 = - r1.
  Parameter Rabs_tri : forall a b c : R , Rabs(a - b) < c <-> a < b + c /\ a > b - c.
  Parameter Ropp_R0 : R0 = - R0. 
  Parameter Ropp_IQR : forall r : Q ,  - IQR r  = IQR ( - r).
  Parameter Rlt_opp : forall r : R , r > R0 -> - r < R0.
  Parameter Rle_opp : forall r : R , r >= R0 -> - r <= R0.
  Parameter Rlt_mid : forall r r1 : R , r < r1 -> exists eps : Q , (eps > 0)%Q /\ r + IQR eps < r1 - IQR eps.
  Parameter Rlt_pos_eqb : forall r1 r2 : R  , r1 < r2 <-> r2 - r1 > R0.
  Parameter Rlt_neg_eqb : forall r1 r2 : R  , r1 > r2 <-> r2 - r1 < R0.
  Parameter Rle_pos_eqb : forall r1 r2 : R  , r1 <= r2 <-> r2 - r1 >= R0.
  Parameter Rle_neg_eqb : forall r1 r2 : R  , r1 >= r2 <-> r2 - r1 <= R0.
  Parameter Rplus_0 : forall r1 r2 : R , r1 - r2 = R0 <-> r1 = r2.
  Parameter Rminus_self : forall r : R , r - r = R0.
  Definition R2 : R := R1 + R1.
  Parameter Rplus_0_l : forall r1 : R , r1 = R0 + r1.
  Parameter Rplus_0_r : forall r1 : R , r1 = r1 + R0.
  Parameter Rmult_0_l : forall r1 : R , R0 * r1 = R0.
  Parameter Rmult_0_r : forall r1 : R , r1 * R0 = R0.
  Parameter Rmult_1_r : forall r1 : R , r1 * R1 = r1.
  Parameter Rmult_1_l : forall r1 : R , R1 * r1 = r1.
  Parameter Rmult_plus_distr_l :forall r1 r2 r3 : R , r3 * (r1 + r2) = r3 * r1 + r3 * r2.
  Parameter Rmult_plus_distr_r : forall r1 r2 r3 :R , (r1 + r2) * r3 = r1 * r3 + r2 * r3.
  Parameter Rplus_comm : forall r1 r2 : R , r1 + r2 = r2 + r1.
  Parameter Rmult_comm : forall r1 r2 : R , r1 * r2 = r2 * r1.
  Parameter Rmult_le_l : forall r1 r2 r3 : R , r3 > R0 -> r3 * r1  <= r3 * r2 <-> r1 <= r2.
  Parameter Rmult_lt_l : forall r1 r2 r3 : R , r3 > R0 -> r3 * r1  < r3 * r2 <-> r1 < r2.
  Parameter Rmult_le_r : forall r1 r2 r3 : R , r3 > R0 -> r1 * r3 <= r2 * r3 <-> r1 <= r2.
  Parameter Rmult_lt_r : forall r1 r2 r3 : R , r3 > R0 -> r1 * r3 < r2 * r3 <-> r1 < r2.
  Parameter Rmult_lt_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 < r2 * r3 <-> r1 * / r3  < r2.
  Parameter Rmult_le_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 <= r2 * r3 <-> r1 * / r3 <= r2.
  Parameter Rmult_gt_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 > r2 * r3 <-> r1 * / r3  > r2.
  Parameter Rmult_ge_divr : forall r1 r2 r3 : R , r3 > R0 -> r1 >= r2 * r3 <-> r1 * / r3 >= r2.
  Parameter Ropp_opp : forall r : R , r = -- r.
  Parameter Rinv_inv : forall r : R , r <> R0 -> r = //r.
  Parameter Rinv_mult : forall r1 r2 : R , / (r1 * r2) = / r1 * / r2.
  Parameter Rinv_self : forall r : R , r <> R0 -> r * / r = R1.
  
  Parameter RT: ring_theory R0 R1 Rplus Rmult Rminus Ropp Reqb.
  Add Ring ABS: RT (abstract).
  
  Parameter Rplus_assoc : forall r1 r2 r3 : R , r1 + r2 + r3 = r1 + (r2 + r3).
  Parameter Rmult_assoc : forall r1 r2 r3 : R , r1 * r2 * r3 = r1 * (r2 * r3).
  Parameter Ropp_minus : forall r1 r2 : R , - (r1 - r2) = r2 - r1.
  Parameter Rlt_Rplus_r : forall r1 r2 r3: R , r1 < r2 -> r1 + r3 < r2 + r3.
  Parameter Rlt_Rplus_l : forall r1 r2 r3: R , r1 < r2 -> r3 + r1 < r3 + r2.
  Parameter Rle_Rplus_r : forall r1 r2 r3: R , r1 <= r2 -> r1 + r3 <= r2 + r3.
  Parameter Rle_Rplus_l : forall r1 r2 r3: R , r1 <= r2 -> r3 + r1 <= r3 + r2.
  Parameter Rlt_Rlt_minus : forall r1 r2 r3 r4 : R , r1 < r2 -> r3 < r4 -> r3 - r2 < r4 - r1.
  Parameter Rle_Rle_minus : forall r1 r2 r3 r4 : R , r1 <= r2 -> r3 <= r4 -> r3 - r2 <= r4 - r1.
  Parameter Rlt_Rle_minus : forall r1 r2 r3 r4 : R , r1 < r2 -> r3 <= r4 -> r3 - r2 < r4 - r1.
  Parameter Rle_Rlt_minus : forall r1 r2 r3 r4 : R , r1 <= r2 -> r3 < r4 -> r3 - r2 < r4 - r1.
  Parameter Rlt_Rminus_r : forall r1 r2 r3: R , r1 - r2 < r3 -> r1 - r3 < r2.
  Parameter Rlt_Rminus_Rplus : forall r1 r2 r3: R , r1 < r2 + r3 <-> r1 - r2 < r3.
  Parameter Rle_Rminus_r : forall r1 r2 r3: R , r1 - r2 <= r3 -> r1 - r3 <= r2.
  Parameter Rle_Rminus_Rplus : forall r1 r2 r3: R , r1 <= r2 + r3 <-> r1 - r2 <= r3.
  Parameter Rle_Rminus :forall r1 r2 r3 : R , r1 + r3 <= r2 <-> r1 <= r2 - r3.
  Parameter Rlt_opp_eqb :forall r1 r2 :R , r1 < -r2 <->  r2 < - r1.
  Parameter Rle_opp_eqb :forall r1 r2 :R , r1 <= -r2 <-> r2 <= - r1.
  Parameter Rgt_Rinv : forall r1 : R , r1 > R1 -> r1 > / r1.
  Parameter Rge_Rinv : forall r1 : R , r1 >= R1 -> r1 >= / r1.
  Parameter Rlt_Rinv : forall r1 : R , r1 < R1 /\ r1 > R0 -> r1 < / r1.
  Parameter Rle_Rinv : forall r1 : R , r1 <= R1 /\ r1 > R0 -> r1 <= / r1.
  Definition archimedean : nat -> R -> Prop .
    intros n r.
    apply (IQR (INR n) <= r /\ r < IQR (INR (n + 1))).
  Defined.
  
  Axiom archimedean_exists : forall r : R , exists x : nat , archimedean x r.
  
  Definition Same_Ipart : R -> R -> Prop.
    intros.
    apply (exists a : nat , IQR (INR (a)) <= X /\ IQR (INR (a)) <= X0 /\ X < IQR (INR (a + 1)) /\ X0 < IQR (INR (a + 1))).
  Defined.
  
  Definition upper_bound (X : nat -> R -> Prop) (U : R) : Prop := forall (n : nat)(q : R) , X n q -> q <= U.
  Definition Sup (X : nat -> R -> Prop) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.

  Axiom upper_bound_exists_Sup : forall (X : nat -> R -> Prop) , is_function X -> (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).

  Parameter Up_same : forall (r1 r2 : R) , r1 = r2 -> (up r1 = up r2)%Z.
  Parameter Up_R0 : (up R0 = 0)%Z.
  
  Parameter IZR_0 : forall z : Z , IZR z = R0 <-> (z = 0)%Z.
  Parameter Z_same_R : forall z1 z2 : Z , (z1 = z2)%Z <-> IZR z1 = IZR z2.
  Parameter IQR_0 : forall q : Q , IQR q = R0 <-> (q = 0)%Q.
  Parameter Q_same_R : forall q1 q2 : Q , (q1 = q2)%Z <-> IQR q1 = IQR q2.

End VIR_R.

Module Type VIR_R_EXTRA (VirR: VIR_R).
Import VirR.
  Parameter Rsinglefun : {X: R -> Prop | (forall x1 x2, X x1 -> X x2 -> x1 = x2)
         /\ (exists x, X x) /\ Proper (Reqb ==> iff) X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
End VIR_R_EXTRA.

Module VirRLemmas (VirR: VIR_R).

  Import VirR.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.

  Instance Req_equiv: Equivalence Reqb.
  Proof.
    split; hnf in *; unfold Reqb in * ; intros ; subst ; auto.
  Qed.
  
  Instance Rplus_Comm: Proper (Reqb ==> Reqb ==> Reqb) Rplus.
  Proof.
    hnf. unfold Reqb. intros.
    hnf. intros. subst. auto.
  Qed.
  
  Instance  Rminus_Comm: Proper (Reqb ==> Reqb ==> Reqb) Rminus.
  Proof.
    hnf. unfold Reqb. intros.
    hnf. intros. subst. auto.
  Qed.
  
  Instance Rmult_Comm: Proper (Reqb ==> Reqb ==> Reqb) Rmult.
  Proof.
    hnf. unfold Reqb. intros.
    hnf. intros. subst. auto.
  Qed.
  Instance Ropp_comm: Proper (Reqb ==> Reqb) Ropp.
  Proof.
    hnf. unfold Reqb. intros.
    subst. auto.
  Qed.

  Theorem Rle_lt_weak : forall r1 r2 : R , r1 < r2 -> r1 <= r2.
  Proof.
    intros.
    unfold Rle. auto.
  Qed.

  Theorem Rle_refl : forall r1 : R , r1 <= r1.
  Proof.
    intros.
    unfold Rle. auto.
  Qed.

  Theorem Rle_trans : forall r1 r2 r3:R, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
  Proof.
    intros.
    destruct H , H0.
    - apply Rle_lt_weak. apply Rlt_trans with r2 ; auto.
    - rewrite <- H0. apply Rle_lt_weak. auto.
    - rewrite H. apply Rle_lt_weak. auto.
    - rewrite H , H0. apply Rle_refl.
  Qed.

  Theorem Rlt_le_trans : forall r1 r2 r3:R , r1 < r2 -> r2 <= r3 -> r1 < r3.
  Proof.
    intros.
    destruct H0.
    - apply Rlt_trans with r2 ; auto.
    - rewrite <- H0. auto.
  Qed.

  Theorem Rle_lt_trans : forall r1 r2 r3:R , r1 <= r2 -> r2 < r3 -> r1 < r3.
  Proof.
    intros.
    destruct H.
    - apply Rlt_trans with r2 ; auto.
    - rewrite H. auto.
  Qed.

  Theorem Req : forall (x y : R) , x <= y /\ y <= x <-> x = y.
  Proof.
    intros.
    split.
    - intros.
      destruct H ; auto.
      destruct H ; auto.
      destruct H0 ; auto.
      pose proof Rlt_trans x y x H H0.
      exfalso. apply (Rlt_irrefl x) ; auto.
    - intros.
      split ; unfold Rle in * ; unfold Rge in *; auto.
  Qed.

  Theorem Rle_ge : forall (x y : R) , x >= y <-> y <= x.
  Proof.
    intros.
    unfold Rge in *.
    unfold Rle in *.
    split ; intros ; destruct H ; auto.
  Qed.

  Theorem Rlt_gt : forall (x y : R) , x > y <-> y < x.
  Proof.
    intros.
    split ; auto.
  Qed.

  Theorem Rlt_not_ge : forall r1 r2 : R , r1 < r2 <-> ~ (r2 <= r1).
  Proof.
    unfold not.
    intros.
    split ; intros.
    - apply (Rlt_irrefl r1).
      apply Rlt_le_trans with r2 ; auto.
    - destruct (R_dec r2 r1) ; auto.
      exfalso . auto. 
  Qed.
  
  Theorem Rle_not_gt : forall r1 r2 : R , r1 <= r2 <-> ~ (r2 < r1).
  Proof.
    unfold not.
    intros.
    split ; intros.
    - apply (Rlt_irrefl r1).
      apply Rle_lt_trans with r2 ; auto.
    - destruct (R_dec r1 r2) ; auto.
      exfalso . auto. 
  Qed.
  
  Theorem Rle_ge_eq : forall x y : R , x >= y -> y >= x -> x = y.
  Proof.
    intros.
    apply Rle_ge in H.
    apply Rle_ge in H0.
    apply Req ; auto.
  Qed.
  
  Theorem Rnot_eq_lt : forall x y : R , x <> y <-> x > y \/ x < y.
  Proof.
    intros.
    unfold not in *.
    split ; intros.
    - rewrite <- Req in H.
      apply not_and_or in H.
      destruct H.
      + left. rewrite <- Rlt_not_ge in H. auto.
      + right. rewrite <- Rlt_not_ge in H. auto.
    - subst.
      destruct H ; apply (Rlt_irrefl y) ; auto.
  Qed.
  
  Theorem IQR_R1_same : IQR (1%nat) = R1.
  Proof.
    apply NNPP.
    intro.
    apply Rnot_eq_lt in H.
    destruct H ; rewrite <- IQR_R1 in * ; apply IQR_lt in H ; apply (Qlt_irrefl 1) ; rewrite INR_Qeq_1 in H ;auto.
  Qed.
  
  Theorem Ipart_unique : forall (r : R)(n m : nat) , ((IQR (INR n) <= r) /\ (r < IQR (INR (n + 1)))) ->
                                                     ((IQR (INR m) <= r) /\ (r < IQR (INR (m + 1)))) -> n = m%nat.
  Proof.
    intros.
    destruct H , H0.
    apply NNPP. intro.
    apply nat_total_order in H3.
    destruct H3 ; apply lt_le_S in H3 ; rewrite <- Nat.add_1_r in H3 ; apply (Rlt_irrefl r) ; apply INR_le in H3 ; apply IQR_le in H3.
    - apply Rlt_le_trans with (IQR (n + 1)%nat) ; auto.
      apply Rle_trans with (IQR (m)) ; auto.
    - apply Rlt_le_trans with (IQR (m + 1)%nat) ; auto.
      apply Rle_trans with (IQR (n)) ; auto.
  Qed.
  
  Theorem Same_Ipart_mult : forall (r1 r2 : R)(k : nat) , (k > 0)%nat -> 
                Same_Ipart (r1 * (IQR (INR k))) (r2 * (IQR (INR k))) -> Same_Ipart r1 r2.
  Proof.
    intros.
    hnf in *.
    destruct H0 , H0 , H1 , H2.
    assert (IQR (k) > R0).
    { rewrite <- IQR_R0. apply IQR_lt. rewrite <- INR_Qeq_0. apply INR_lt. omega. }
    apply Rmult_le_divr in H0; auto.
    apply Rmult_le_divr in H1; auto.
    apply Rmult_gt_divr in H2; auto.
    apply Rmult_gt_divr in H3; auto.
    destruct (archimedean_exists (IQR x * / IQR k)) , H5.
    assert (IQR (x + 1)%nat * / IQR k <= IQR (INR (x0 + 1))).
    { apply Rmult_le_divr ; auto.
      rewrite <- Rmult_lt_divr in H6 ; auto.
      rewrite IQR_mult in *. apply IQR_le. 
      apply IQR_lt in H6.
      rewrite INR_mult in *. 
      apply INR_le. apply INR_lt in H6. 
      omega.
     }
     exists x0.
     repeat split.
     - apply Rle_trans with (IQR x * / IQR k) ; auto.
     - apply Rle_trans with (IQR x * / IQR k) ; auto.
     - apply Rlt_le_trans with (IQR (x + 1)%nat * / IQR k) ; auto.
     - apply Rlt_le_trans with (IQR (x + 1)%nat * / IQR k) ; auto.
  Qed.

  Definition Un_cv (A : nat -> R -> Prop) (r : R) : Prop :=
    is_function A /\ (
    forall eps : R , eps > R0 -> (exists n : nat , 
          forall (m : nat) (r1 : R) , (m >= n)%nat -> A m r1 -> Rabs(r1 - r) < eps)).
  
  Theorem Un_cv_inject : forall (X : nat -> R -> Prop) (r1 r2 : R) , Un_cv X r1 -> Un_cv X r2 -> r1 = r2.
  Proof. 
    intros.
    hnf in *.
    apply NNPP.
    intro.
    apply Rnot_eq_lt in H1. destruct H , H0.
    destruct H , H0.
    destruct H1 ; apply Rlt_mid in H1 ; destruct H1 ; destruct H1 ;
    apply IQR_lt in H1 ; rewrite IQR_R0 in H1; 
    specialize (H2 (IQR x) H1) ; specialize (H3 (IQR x) H1) ; destruct H2 , H3 ; destruct (H (max x0 x1));
    destruct (H0 (max x0 x1)) ; 
    specialize (H2 (max x0 x1) x2 (Nat.le_max_l x0 x1) H7 ) ; specialize (H3 (max x0 x1) x3 (Nat.le_max_r x0 x1) H8); 
    apply Rabs_tri in H2 ; apply Rabs_tri in H3 ; destruct H2 , H3 ; specialize (H4 (max x0 x1) x2 x3 H7 H8) ; subst ;
    apply (Rlt_irrefl x3). 
    - apply Rlt_trans with (r2 + IQR x) ; auto.
      apply Rlt_trans with (r1 - IQR x) ; auto.
    - apply Rlt_trans with (r1 + IQR x) ; auto.
      apply Rlt_trans with (r2 - IQR x) ; auto.
  Qed.
  
  Definition mono_up (X : nat -> R -> Prop) : Prop := is_function X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q >= q1).
  Definition mono_down (X : nat -> R -> Prop) : Prop := is_function X /\ (forall (n n1: nat)(q q1: R) ,
                                                      X n q -> X n1 q1 -> (n >= n1)%nat -> q <= q1).
  Definition mono (X : nat -> R -> Prop) : Prop := mono_up X \/ mono_down X.
  Definition lower_bound (X : nat -> R -> Prop) (L : R) : Prop := forall (n : nat)(q : R) , X n q -> L <= q.
  Definition Inf (X : nat -> R -> Prop) (inf : R) : Prop := (forall r : R , lower_bound X r -> r <= inf) /\ lower_bound X inf.
  Definition bound (X : nat -> R -> Prop) : Prop := (exists n1 : R , upper_bound X n1) /\ (exists n2 : R ,lower_bound X n2).

  Theorem Sup_pro : forall (X : nat -> R -> Prop) (sup : R) , is_function X -> Sup X sup -> forall y : R , (y < sup -> 
                              (exists n : nat , forall q : R , X n q -> ( q <= sup /\ y < q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0.
    apply Rlt_not_ge in H1.
    apply H1.
    apply Rle_ge.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q = q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply (H5 n) ; auto.
    - apply Rle_not_gt. auto. 
  Qed.
  
  Theorem Inf_pro : forall (X : nat -> R -> Prop) (inf : R) , is_function X -> Inf X inf -> forall y : R , (y > inf -> 
                              (exists n : nat , forall q : R , X n q -> (q >= inf /\ y > q))).
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H2.
    destruct H , H0.
    apply Rlt_not_ge in H1.
    apply H1.
    apply (H0 y).
    hnf.
    intros.
    specialize (H3 n).
    apply not_all_ex_not in H3.
    destruct H3 as [q' ?].
    assert (q = q').
    { apply (H4 n) ; auto. apply not_imply_elim in H3. auto. }
    subst.
    apply not_imply_elim2 in H3.
    apply not_and_or in H3.
    destruct H3.
    - exfalso. apply H3. apply Rle_ge. apply (H5 n); auto.
    - apply Rle_not_gt. auto.
  Qed.

  Theorem upper_bound_T_lower_bound : forall (X P : nat -> R -> Prop) , is_function X -> is_function P
                                                                     -> (forall n r , X n r <-> P n (-r)) 
                                                                      -> forall r , upper_bound X r <-> lower_bound P (-r).
  Proof.
    intros.
    split ; intros.
    - hnf. intros.
      specialize (H1 n (-q)).
      rewrite Ropp_opp in H3.
      rewrite <- H1 in H3.
      specialize (H2 n (-q) H3).
      rewrite Ropp_opp. rewrite Ropp_opp in H2.
      apply Rle_opp_eqb ; auto.
    - hnf. intros.
      specialize (H1 n q).
      rewrite H1 in H3.
      specialize (H2 n (-q) H3).
      rewrite Ropp_opp. apply Rle_opp_eqb ; auto.
  Qed.
  
  Theorem lower_bound_exists_Inf : forall (X : nat -> R -> Prop) , is_function X -> (exists r : R , lower_bound X r) ->
                                          (exists inf : R , Inf X inf).
  Proof.
    intros.
    destruct H0.
    set (fun (n : nat)(r : R) => X n (-r)).
    assert (is_function P).
    {
      destruct H.
      split.
      - intro. destruct (H a). exists (-x0).
        rewrite Ropp_opp in H2.
        apply H2.
      - intro. intros.
        specialize (H1 a (-b1) (-b2) H2 H3).
        rewrite Ropp_opp at 1. rewrite Ropp_opp.
        rewrite H1. auto.
    }
    assert (exists x , upper_bound P x).
    {
      exists (-x).
      apply (upper_bound_T_lower_bound P X) ; auto.
      - intros.  split; auto.
      - rewrite <- Ropp_opp. auto.
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
        - rewrite <- Ropp_opp. auto.
      }
      specialize (H3 (-r) H6).
      apply Rle_ge in H3.
      apply Rle_opp_eqb ; auto.
    - apply (upper_bound_T_lower_bound P X) ; auto.
      intros. split ; auto.
  Qed.
  
  Theorem Sup_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Sup X r1 -> Sup X r2 -> r1 = r2.
  Proof. 
    intros.
    unfold Sup in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; apply Rle_ge ; auto.
  Qed.

  Theorem Inf_unique : forall (X : nat -> R -> Prop) (r1 r2 : R), Inf X r1 -> Inf X r2 -> r1 = r2.
  Proof.
    intros.
    unfold Inf in *.
    destruct H , H0.
    pose proof (H r2 H2).
    pose proof (H0 r1 H1).
    apply Req. split ; auto.
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
    { rewrite Rplus_0_r.
      unfold Rminus.
      apply Rlt_Rplus_l.
      apply Rlt_opp. auto.
    }
    pose proof Sup_pro X x H H2 (x - eps) H3.
    destruct H4 , H.
    exists x0.
    intros.
    rewrite Rabs_neg.
    - rewrite Ropp_minus.
      apply Rlt_Rminus_r.
      destruct (H x0).
      apply Rlt_le_trans with x1.
      + apply H4 ; auto.
      + apply Rle_ge. apply (H1 m x0) ; auto.
    - apply Rle_neg_eqb.
      rewrite Rle_ge.
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
    assert (r = x).
    {
      apply (Un_cv_inject X) ; auto.
      unfold Un_cv , mono_up in *.
      split ; auto.
      intros.
      assert (x - eps < x).
      { rewrite Rplus_0_r.
        unfold Rminus.
        apply Rlt_Rplus_l.
        apply Rlt_opp. auto.
      }
      pose proof Sup_pro X x H H3 (x - eps) H4.
      destruct H5 , H.
      exists x0.
      intros.
      rewrite Rabs_neg.
      - rewrite Ropp_minus.
        apply Rlt_Rminus_r.
        destruct (H x0).
        apply Rlt_le_trans with x1.
        + apply H5 ; auto.
        + apply Rle_ge. apply (H2 m x0) ; auto.
      - apply Rle_neg_eqb.
        rewrite Rle_ge.
        destruct H3.
        apply (H9 m) ; auto.
    }
    subst. auto.
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
    { rewrite Rplus_0_r.
      unfold Rminus.
      apply Rlt_Rplus_l.
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
  
  Theorem archimedean_extend : forall r1 r2 : R , r1 > R0 /\ r2 > R0 -> exists n : nat , IQR n * r2 > r1.
  Proof.
    intros.
    apply NNPP.
    intro.
    pose proof not_ex_all_not _ _ H0.
    set (fun (n : nat)(r : R) => r = IQR n * r2).
    assert (is_function P).
    {
      subst P.
      split ; hnf ; intros.
      - exists (IQR a * r2). auto.
      - subst ; auto.
    }
    assert (upper_bound P r1).
    { hnf ; intros.
      subst P.
      simpl in *.
      subst.
      apply Rle_not_gt.
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
      assert (x - x = R0). { apply Rplus_0. auto. }
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
      simpl in *.
      subst.
      rewrite <- Rmult_1_l at 1.
      rewrite Rmult_plus_distr_l.
      rewrite <- Rmult_assoc.
      rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      rewrite <- IQR_R1. rewrite Rplus_comm.
      rewrite IQR_plus.
      assert (IQR (x0 + 1) = IQR (S x0)).
      { apply IQR_eq. rewrite INR_S. auto. }
      rewrite H9. auto.
    }
    apply (H11 (S x0) (r2 + x1) H12).
  Qed.
  
  Theorem eps_gt_10n :forall eps : R , eps > R0 -> exists n : nat , IQR 1 *  / IQR (INR (10 ^ n)%nat) < eps.
  Proof.
     intros.
     assert (IQR 1 > R0 /\ eps > R0).
     { split; auto. rewrite <- IQR_R0. apply IQR_lt.
       lra.
     }
     pose proof (archimedean_extend (IQR 1) eps H0).
     destruct H1.
     destruct H0.
     exists x.
     apply Rmult_lt_divr.
     - apply Rlt_le_trans with (IQR 1) ; auto.
       apply IQR_le. rewrite <- INR_Qeq_1.
       apply INR_le. apply Max_powan_0. omega.
     - apply Rlt_trans with (IQR x * eps) ; auto.
       rewrite (Rmult_comm eps (IQR (10 ^ x)%nat)).
       apply Rmult_lt_r ; auto.
       apply IQR_lt. apply INR_lt.
       apply Nat.pow_gt_lin_r. omega.
  Qed.
  
  Theorem Req_same : forall r1 r2 : R , r1 = r2 <-> forall eps : R , eps > R0 -> Rabs(r1 - r2) < eps.
  Proof.
    intros.
    split; intros ; subst ; try (reflexivity).
    - rewrite Rminus_self. rewrite Rabs_pos. apply Rlt_gt. auto.
      apply Rle_refl.
    - apply NNPP.
      intro.
      apply Rnot_eq_lt in H0.
      destruct H0.
      + apply Rlt_pos_eqb in H0.
        assert (r1 - r2 >= R0). { apply Rle_ge. apply Rle_lt_weak. apply H0. }
        apply eps_gt_10n in H0.
        destruct H0.
        apply (Rlt_irrefl (IQR 1 * / IQR (10^ x)%nat)).
        apply Rlt_trans with (r1 - r2) ; auto.
        rewrite <- (Rabs_pos (r1 - r2)) ; auto.
        apply H.
        apply Rmult_gt_divr.
        * rewrite <- IQR_R0. apply IQR_lt.
          rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
        * rewrite Rmult_0_l. rewrite <- IQR_R0. apply IQR_lt. lra.
      + apply Rlt_neg_eqb in H0.
        assert (r1 - r2 <= R0). { apply Rle_lt_weak. apply H0. }
        apply Rlt_neg_eqb in H0. apply Rlt_pos_eqb in H0.
        apply eps_gt_10n in H0.
        destruct H0.
        apply (Rlt_irrefl (IQR 1 * / IQR (10^ x)%nat)).
        apply Rlt_trans with (Rabs (r1 - r2)) ; auto.
        rewrite (Rabs_neg (r1 - r2)) ; auto.
        rewrite Ropp_minus. auto.
        apply H.
        apply Rmult_gt_divr.
        * rewrite <- IQR_R0. apply IQR_lt.
          rewrite <- INR_Qeq_0. apply INR_lt. apply Max_powan_0. omega.
        * rewrite Rmult_0_l. rewrite <- IQR_R0. apply IQR_lt. lra.
  Qed.

  Theorem IZR_0' : IZR 0 = R0.
  Proof.
    apply IZR_0 ; auto.
  Qed.
  Theorem Z_same_R' : forall z1 z2 : Z , (z1 <> z2)%Z <-> IZR z1 <> IZR z2.
  Proof.
    unfold not in *.
    intros. 
    split ; intros ; apply H ; apply Z_same_R ; auto.
  Qed.
  Theorem Ex_Z_R' : forall z : Z , (z <> 0)%Z <-> IZR z <> R0.
  Proof.
    unfold not in *.
    intros.
    split ; intros ; apply H ; apply IZR_0 ; auto.
  Qed.
  Theorem IQR_0' : IQR 0 = R0.
  Proof.
    apply IQR_0 ; auto.
  Qed.
  Theorem Q_same_R' : forall q1 q2 : Q , (q1 <> q2)%Z <-> IQR q1 <> IQR q2.
  Proof.
    unfold not in *.
    intros. 
    split ; intros ; apply H ; apply Q_same_R ; auto.
  Qed.
  Theorem Ex_Q_R' : forall q : Q , (q <> 0)%Q <-> IQR q <> R0.
  Proof.
    unfold not in *.
    intros.
    split ; intros ; apply H ; apply IQR_0 ; auto.
  Qed.

End VirRLemmas.

