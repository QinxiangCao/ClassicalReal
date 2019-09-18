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


Definition Cauchy_abs (A : nat -> Q -> Prop): (nat -> Q -> Prop) :=
    fun (n:nat) (q:Q) =>
     forall (qabs:Q), (A n qabs) -> q == (Qabs qabs).

Theorem Cauchy_abs_Cauchy: forall A, Cauchy A 
  -> Cauchy (Cauchy_abs A).
Proof. intros. unfold Cauchy_abs. split. 
- intros. destruct (Cauchy_exists _ H n) as [qabs1 H1].
  exists (Qabs qabs1). intros. rewrite (Cauchy_unique _ H n _ _ H1 H0).
  reflexivity.
- intros. destruct (Cauchy_exists _ H n) as [qabs H2].
  rewrite (H0 _ H2). rewrite (H1 _ H2). reflexivity.
- intros. rewrite <- H0. apply H1. auto.
- intros. destruct (Cauchy_def _ H eps H0) as [N H1].
  exists N. intros.
  destruct (Cauchy_exists _ H m1) as [qm1 Hm1].
  destruct (Cauchy_exists _ H m2) as [qm2 Hm2].
  assert (E: Qabs(qm1 - qm2) < eps). { apply (H1 m1 m2). auto. auto. auto. auto. }
  assert (E1: Qabs (qm1 - qm2) >= Qabs (Qabs qm1 - Qabs qm2)).
  { apply Qabs_Qle_condition. split.
    rewrite <- (Qopp_involutive (Qabs qm1 - Qabs qm2)). apply Qopp_le_compat.
    assert (Et: - (Qabs qm1 - Qabs qm2) == Qabs qm2 - Qabs qm1) by ring.
    rewrite Et. rewrite Qabs_Qminus. apply Qabs_triangle_reverse.
    apply Qabs_triangle_reverse. }
  rewrite (H4 _ Hm1). rewrite (H5 _ Hm2).
  apply (Qle_lt_trans _ _ _ E1). auto.
Qed.

Fixpoint Rabs(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (Cauchy_abs A) (Cauchy_abs_Cauchy A HA) 
  end.

Instance Rabs_comp : Proper (Real_equiv ==> Real_equiv ) Rabs.
Proof. hnf. intros. destruct x as [A HA].
  destruct y as [B HB]. hnf in *. unfold Cauchy_abs. intros.
  destruct (H eps H0) as [N HN].
  exists N. intros. clear H.
  destruct (Cauchy_exists _ HA m) as [qm1 Hm1].
  destruct (Cauchy_exists _ HB m) as [qm2 Hm2].
  assert (E: Qabs(qm1 - qm2) < eps). { apply (HN _ H1). auto. auto. }
  assert (E1: Qabs (qm1 - qm2) >= Qabs (Qabs qm1 - Qabs qm2)).
  { apply Qabs_Qle_condition. split.
    rewrite <- (Qopp_involutive (Qabs qm1 - Qabs qm2)). apply Qopp_le_compat.
    assert (Et: - (Qabs qm1 - Qabs qm2) == Qabs qm2 - Qabs qm1) by ring.
    rewrite Et. rewrite Qabs_Qminus. apply Qabs_triangle_reverse.
    apply Qabs_triangle_reverse. }
  rewrite (H2 _ Hm1). rewrite (H3 _ Hm2).
  apply (Qle_lt_trans _ _ _ E1). auto.
Qed.


Theorem Rabs_zero: (Rabs 0 == 0)%R.
Proof. hnf. intros. exists O. intros. unfold Cauchy_abs in *.
  rewrite H2. assert (Et: q1 - 0 == q1) by ring. rewrite Et.
  rewrite (H1 0). apply H. reflexivity.
Qed.


Theorem Rabs_positive: forall A, Rpositive A -> (Rabs A == A)%R.
Proof. intros.
  assert (E1: limit_not_0_real A). { apply limit_not_0_spec. apply Rpositive_not_zero. auto. }
  destruct A as [A HA]. unfold limit_not_0_real in E1.
  apply (Cauchy_nonzero_pre _ HA) in E1.
  hnf in *.
  destruct H as [eps [Heps [N1 H1]]].
  intros. unfold Cauchy_abs.
  destruct E1 as [N2 [eps1 [Heps1 H2]]].
  destruct (take_max_N N1 (S N2) _ _ H1 H2) as [N HN]. clear N1 H1 N2 H2.
  exists N. intros.
  assert (E2: (m >= N)%nat) by omega.
  apply HN in E2. destruct E2 as [E2 E3].
  assert (E4: q2 >= 0). { apply (Qle_trans 0 eps q2). apply Qlt_le_weak. auto. auto. }
  rewrite (H1 q2 H2). apply Qabs_pos in E4. rewrite E4.
  unfold Qminus. rewrite Qplus_opp_r. auto.
Qed.

Theorem Rabs_negative: forall A, Rnegative A -> (Rabs A == Ropp A)%R.
Proof. intros.
  assert (E1: limit_not_0_real A). { apply limit_not_0_spec. apply Rnegative_not_zero. auto. }
  destruct A as [A HA]. unfold limit_not_0_real in E1.
  apply (Cauchy_nonzero_pre _ HA) in E1.
  hnf in *. unfold Ropp in *. unfold Cauchy_opp in *.
  destruct H as [eps [Heps [N1 H1]]].
  intros. unfold Cauchy_abs.
  destruct E1 as [N2 [eps1 [Heps1 H2]]].
  destruct (take_max_N N1 (S N2) _ _ H1 H2) as [N HN]. clear N1 H1 N2 H2.
  exists N. intros.
  assert (E2: (m >= N)%nat) by omega.
  apply HN in E2. destruct E2 as [E2 E3]. clear HN.
  destruct (Cauchy_exists _ HA m) as [qa Hqa].
  rewrite (H1 qa Hqa). rewrite (H2 qa Hqa). unfold Qminus. rewrite Qopp_involutive.
  assert (E4: qa <= 0). { apply (Qle_trans qa (-eps) 0).
    - rewrite <- Qopp_involutive. apply Qopp_le_compat. apply E2.
      intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H3). reflexivity.
    - rewrite <- (Qopp_involutive 0). apply Qopp_le_compat. apply Qlt_le_weak. auto. }
  apply Qabs_neg in E4. rewrite E4. rewrite Qplus_comm.
   rewrite Qplus_opp_r. auto.
Qed.

Theorem Rabs_Ropp: forall x, (Rabs x == Rabs (-x))%R.
Proof. intros. destruct (Real_sgn_case x).
- rewrite (Rabs_positive _ H).
  assert (Rnegative (-x)). apply Rpositive_Ropp. auto.
  rewrite (Rabs_negative _ H0). ring.
- destruct H.
  + rewrite H. rewrite Rabs_zero. assert (0==-0)%R by ring.
    rewrite <- H0. rewrite Rabs_zero. reflexivity. 
  + rewrite (Rabs_negative _ H).
    assert (Rpositive (-x)). apply Rnegative_Ropp. auto.
    rewrite (Rabs_positive _ H0). ring.
Qed.

Theorem Rabs_nonneg: forall x, (0 <= (Rabs x))%R.
Proof. intros. hnf in *.
  destruct (classic ((0 == x)%R)).
  - right. rewrite <- H. symmetry. apply Rabs_zero.
  - left. assert (E: ~(x == 0)%R). { intros C. rewrite C in H. apply H. reflexivity. }
    apply Real_not_zero_positive_or_negative in E. destruct E.
    + rewrite (Rabs_positive _ H0). apply Rpositive_gt_0 in H0. auto.
    + rewrite (Rabs_negative _ H0). rewrite (Ropp_involutive 0).
      apply Ropp_lt_compat. rewrite <- Rzero_opp_zero. apply Rnegative_lt_0. auto.
Qed.


Theorem Rabs_lt_iff (x:Real)(y:Real): (y>0 -> ((Rabs x < y) <-> (-y<x /\ x<y)))%R.
Proof. intros. split.
  - intros. destruct (classic (0<x)%R).
    + split. 
       * apply (Rlt_trans _ 0). rewrite (Ropp_involutive 0). apply Ropp_lt_compat.
         rewrite <- Rzero_opp_zero. auto. auto.
       * rewrite Rabs_positive in H0. apply H0. apply Rpositive_gt_0. auto.
    + split.
       * apply Rnot_lt in H1. destruct H1.
         ** rewrite <- H1. rewrite (Ropp_involutive 0). apply Ropp_lt_compat.
            rewrite <- Rzero_opp_zero. auto.
         ** rewrite Rabs_negative in H0. rewrite (Ropp_involutive x). apply Ropp_lt_compat.
            auto. apply Rnegative_lt_0. auto.
       * apply Rnot_lt in H1. destruct H1.
         ** rewrite <- H1. auto.
         ** apply (Rlt_trans _ 0). auto. auto.
  - intros. destruct H0. destruct (classic (0<x)%R).
    + rewrite Rabs_positive. auto. apply Rpositive_gt_0. auto.
    + apply Rnot_lt in H2. destruct H2.
      * rewrite <- H2. rewrite Rabs_zero. auto.
      * rewrite Rabs_negative.  rewrite (Ropp_involutive y). apply Ropp_lt_compat. auto.
        apply Rnegative_lt_0. auto. 
Qed.




Theorem Rabs_Rmult (A B:Real): (Rabs (A*B) == (Rabs A)*(Rabs B))%R.
Proof. intros. destruct (classic (A == 0)%R),(classic (B == 0)%R).
  - rewrite H. rewrite Rabs_zero. rewrite Rmult_0_l. rewrite Rmult_0_l. apply Rabs_zero.
  - rewrite H. rewrite Rabs_zero. rewrite Rmult_0_l. rewrite Rmult_0_l. apply Rabs_zero.
  - rewrite H0. rewrite Rabs_zero. rewrite Rmult_0_r. rewrite Rmult_0_r. apply Rabs_zero.
  - apply Real_not_zero_positive_or_negative in H.
    apply Real_not_zero_positive_or_negative in H0. destruct H,H0.
    + assert (E: Rpositive (A*B)%R).
      { apply Rpositive_gt_0. rewrite <- (Rmult_0_r A). apply (Rlt_mult_l). auto.
        apply Rpositive_gt_0 in H0. auto. }
      rewrite Rabs_positive. rewrite Rabs_positive. rewrite Rabs_positive.
      reflexivity. auto. auto. auto.
    + assert (E: Rnegative (A*B)%R).
      { apply Rnegative_lt_0. rewrite <- (Rmult_0_r A). apply (Rlt_mult_l). auto.
        apply Rnegative_lt_0 in H0. auto. }
      rewrite Rabs_negative. rewrite Rabs_positive. rewrite Rabs_negative.
      rewrite (Rmult_comm A (-B)%R). rewrite <- Ropp_mult_distr.
      rewrite (Rmult_comm). reflexivity.
      auto. auto. auto.
    + assert (E: Rnegative (A*B)%R).
      { apply Rnegative_lt_0. rewrite <- (Rmult_0_l B). apply (Rlt_mult_r). auto.
        apply Rnegative_lt_0 in H. auto. }
      rewrite Rabs_negative. rewrite Rabs_negative. rewrite Rabs_positive.
      rewrite <- Ropp_mult_distr. reflexivity.
      auto. auto. auto.
    + assert (E: Rpositive (A*B)%R).
      { apply Rpositive_gt_0. rewrite Ropp_involutive. 
        rewrite (Ropp_involutive (A*B)%R). apply Ropp_lt_compat.
        rewrite Ropp_mult_distr. rewrite Rmult_comm. rewrite (Ropp_involutive (B*-A)%R).
        apply Ropp_lt_compat. rewrite Ropp_mult_distr. apply Rnegative_Ropp in H.
        apply Rnegative_Ropp in H0. rewrite <- (Rmult_0_r (-B)). apply (Rlt_mult_l). auto.
        apply Rpositive_gt_0 in H. auto. }
        rewrite Rabs_positive. rewrite Rabs_negative. rewrite Rabs_negative.
        rewrite <- Ropp_mult_distr. rewrite (Rmult_comm A (-B)). rewrite <- Ropp_mult_distr.
        rewrite <- Ropp_involutive. rewrite Rmult_comm.
        reflexivity. auto. auto. auto.
Qed.


Lemma Rabs_nonpositive: forall A : Real, ~(Rpositive A) -> (Rabs A == - A)%R.
Proof. intros. apply Rnot_positive in H. destruct H.
  rewrite (Rabs_negative _ H). reflexivity.
  rewrite H. rewrite Rabs_zero. rewrite <- Rzero_opp_zero. reflexivity.
Qed. 

Theorem Rabs_Rle: forall A,  (A <= Rabs A)%R.
Proof. intros. destruct (Real_sgn_case A).
  - rewrite Rabs_positive;auto. right. reflexivity.
  - destruct H.
    + rewrite H. rewrite Rabs_zero. right. ring.
    + rewrite Rabs_negative;auto. left. apply Rnegative_lt_0 in H.
      apply (Rlt_trans _ 0). auto. apply Ropp_lt_compat in H.
      assert (0==-0)%R by ring. rewrite H0. auto.
Qed.

Lemma Rabs_zero_inj: forall A, (Rabs A ==0)%R-> (A==0)%R.
Proof. intros. destruct (Real_sgn_case A).
  rewrite (Rabs_positive _ H0) in H. auto.
  destruct H0. auto.
  rewrite (Rabs_negative _ H0) in H. rewrite (Ropp_involutive A).
  rewrite H. ring.
Qed.


Lemma Rabs_le_iff:
  forall x y : Real,
  (y >= 0)%R -> (Rabs x <= y)%R <-> (- y <= x)%R /\ (x <= y)%R.
Proof. intros. destruct H.
  { split.
  + intros. destruct H0. apply Rabs_lt_iff in H0;auto. destruct H0. split.
    apply Rlt_le_weak. auto. apply Rlt_le_weak. auto.
    split. rewrite <- H0. apply Ropp_le_compat. rewrite <- Ropp_involutive.
    rewrite Rabs_Ropp. apply Rabs_Rle. rewrite <- H0. apply Rabs_Rle.
  + intros. destruct H0. destruct (Real_sgn_case x).
    rewrite (Rabs_positive _ H2). auto. destruct H2. rewrite H2. rewrite Rabs_zero.
    apply Rlt_le_weak. auto. rewrite (Rabs_negative _ H2). rewrite (Ropp_involutive y).
    apply Ropp_le_compat in H0. auto. }
  { split.
  + intros. rewrite <- H. rewrite <- H in H0. destruct H0.
    pose proof (Rabs_nonneg x).
    apply Rnot_lt_le in H1. contradiction. apply Rabs_zero_inj in H0.
    rewrite H0. split. right. ring. right. ring.
  + intros. destruct H0. rewrite <- H in H0,H1. destruct H0,H1.
    * assert (-0<0)%R. { apply (Rlt_trans _ x). auto. auto. }
      assert (-0==0)%R by ring. rewrite H3 in H2. apply Rlt_irrefl in H2. destruct H2.
    * right. rewrite H1. rewrite Rabs_zero. auto.
    * right. assert (-0==0)%R by ring. rewrite H2 in H0. rewrite <- H0. rewrite Rabs_zero.
      auto.
    * rewrite <- H. rewrite H1. right. rewrite Rabs_zero. reflexivity. }
Qed.


Theorem Rabs_triangle: forall A B, (Rabs(A+B)<= Rabs A + Rabs B)%R.
Proof. intros.
  destruct (Real_sgn_case A) as [HA|[HA|HA]],(Real_sgn_case B) as [HB|[HB|HB]].
  - rewrite (Rabs_positive _ HA). rewrite (Rabs_positive _ HB).
    assert (Rpositive (A+B))%R. { apply Rpositive_gt_0. rewrite <- Rplus_0_r.
      apply Rlt_plus_compat. apply Rpositive_gt_0 in HA. auto. apply Rpositive_gt_0 in HB. auto. }
    rewrite (Rabs_positive (A+B) H)%R. right. reflexivity.
  - rewrite (Rabs_positive _ HA). rewrite (HB). rewrite Rabs_zero. assert (A+0==A)%R by ring.
    rewrite H. rewrite Rabs_positive;auto. right. reflexivity.
  - rewrite (Rabs_positive _ HA). rewrite (Rabs_negative _ HB).
    apply Rabs_le_iff.  { apply Rpositive_gt_0 in HA. apply Rnegative_lt_0 in HB.
      apply Ropp_lt_compat in HB. pose proof (Rlt_plus_compat _ _ _ _ HA HB).
      assert (0+-0==0)%R by ring. rewrite H0 in H. left. auto. }
    split. assert (-(A+-B)==-A+B)%R by ring. rewrite H. apply Rle_plus_r.
    apply Rlt_le_weak. apply (Rlt_trans _ 0%R). rewrite (Ropp_involutive 0).
    apply Ropp_lt_compat. assert (0==-0)%R by ring. rewrite <- H0.
    apply Rpositive_gt_0 in HA. auto. apply Rpositive_gt_0 in HA. auto.
    apply Rle_plus_l.
    apply Rlt_le_weak. apply (Rlt_trans _ 0%R).
    apply Rnegative_lt_0 in HB. auto. apply Rnegative_lt_0 in HB.
    rewrite (Ropp_involutive 0). apply Ropp_lt_compat.
    assert (-0==0)%R by ring. rewrite H. auto.
  - rewrite HA. rewrite (Rabs_positive _ HB). rewrite Rabs_zero. assert (0+B==B)%R by ring.
    rewrite H. rewrite Rabs_positive;auto. right. reflexivity.
  - rewrite HA,HB. rewrite Rabs_zero. assert (0+0==0)%R by ring.
    rewrite H. rewrite Rabs_zero. right. reflexivity.
  - rewrite HA. rewrite (Rabs_negative _ HB). rewrite Rabs_zero. assert (0+B==B)%R by ring.
    rewrite H. rewrite (Rabs_negative _ HB). right. ring.
  - rewrite (Rabs_positive _ HB). rewrite (Rabs_negative _ HA).
    apply Rabs_le_iff.  { apply Rpositive_gt_0 in HA. apply Rpositive_gt_0 in HB.
      pose proof (Rlt_plus_compat _ _ _ _ HA HB).
      assert (0+0==0)%R by ring. rewrite H0 in H. left. auto. }
    split. assert (-(-A+B)==A-B)%R by ring. rewrite H. apply Rle_plus_l.
    apply Rlt_le_weak. apply (Rlt_trans _ 0%R). rewrite (Ropp_involutive 0).
    apply Ropp_lt_compat. assert (0==-0)%R by ring. rewrite <- H0.
    apply Rpositive_gt_0 in HB. auto. apply Rpositive_gt_0 in HB. auto.
    apply Rle_plus_r.
    apply Rlt_le_weak. apply (Rlt_trans _ 0%R).
    apply Rnegative_lt_0 in HA. auto. apply Rnegative_lt_0 in HA.
    rewrite (Ropp_involutive 0). apply Ropp_lt_compat.
    assert (-0==0)%R by ring. rewrite H. auto.
  - rewrite HB. rewrite (Rabs_negative _ HA). rewrite Rabs_zero. assert (A+0==A)%R by ring.
    rewrite H. rewrite (Rabs_negative _ HA). right. ring.
  - rewrite (Rabs_negative _ HA). rewrite (Rabs_negative _ HB).
    assert (Rnegative (A+B))%R. { apply Rpositive_gt_0. rewrite <- Rplus_0_r.
    assert (-(A+B)==-A-B)%R by ring. rewrite H.
    apply Rlt_plus_compat. apply Rpositive_gt_0 in HA. auto. apply Rpositive_gt_0 in HB. auto. }
    rewrite Rabs_negative;auto. right. ring.
Qed.


Lemma Rabs_Rminus: forall A B, (Rabs (A-B)==Rabs(B-A))%R.
Proof. intros. assert (A-B==-(B-A))%R by ring. rewrite H.
  rewrite <- Rabs_Ropp. reflexivity.
Qed.


Theorem Rabs_triangle_extend: forall A B, (Rabs (Rabs A -Rabs B) <= Rabs (A -B))%R.
Proof. intros.
  assert (A == B + (A-B))%R by ring.
  pose proof (Rabs_triangle B (A-B)).
  assert (B == A + (B-A))%R by ring.
  pose proof (Rabs_triangle A (B-A)).
  rewrite <- H in H0. rewrite <- H1 in H2.
  rewrite Rabs_Rminus in H2.
  apply Rabs_le_iff. apply Rabs_nonneg.
  split.
  apply (Rle_plus_l _ _ (-(Rabs B)-(Rabs (A-B)))) in H2.
  assert (Et1:(- Rabs B - Rabs (A - B) + Rabs B  == - Rabs (A - B))%R) by ring.
  assert (Et2: (- Rabs B - Rabs (A - B) + (Rabs A + Rabs (A - B))== Rabs A - Rabs B)%R) by ring.
  rewrite <- Et1, <- Et2. auto.
  apply (Rle_plus_l _ _ (-(Rabs B)%R)) in H0.
  assert (Et1:(- Rabs B + Rabs A == Rabs A - Rabs B)%R) by ring.
  assert (Et2:(- Rabs B + (Rabs B + Rabs (A - B)) ==  Rabs (A - B))%R) by ring. 
  rewrite <-Et1,<-Et2.
  auto.
Qed.

Lemma Qarchimedean : forall p q :Q, p > 0 -> exists n : Q, n*p>q.
Proof.
  intros. exists ((q*/p)+1)%Q. rewrite Qmult_plus_distr_l.
  assert(H':(~p==0)%Q).
  { apply Qlt_not_eq in H.
    unfold not.
    intros.
    apply H. rewrite H0. reflexivity.
  }
  rewrite Qmult_comm.
  apply (Qmult_div_r q) in H'.
  rewrite H'.
  rewrite Qmult_1_l.
  apply Qplus_lt_l with (z:=0).
  rewrite <- Qplus_assoc.
  rewrite Qplus_lt_r with (z:=q).
  rewrite Qplus_0_r. apply H.
Qed.


Theorem Rle_mult_r:
  forall A B C : Real, Rpositive C -> (A <= B)%R -> (A * C <= B * C)%R.
Proof.
  intros. destruct H0.
  - left. apply Rlt_mult_r. auto. auto.
  - right. rewrite H0. ring.
Qed.
Theorem Rle_mult_l:
  forall A B C : Real, Rpositive C -> (A <= B)%R -> (C*A<= C*B)%R.
Proof.
  intros. destruct H0.
  - left. apply Rlt_mult_l. auto. auto.
  - right. rewrite H0. ring.
Qed.
Theorem Rle_mult_r_compat:
  forall A B C : Real, Rpositive C -> (A <= B)%R <-> (A * C <= B * C)%R.
Proof.
  intros. split.
  { intros. destruct H0.
  - left. apply Rlt_mult_r. auto. auto.
  - right. rewrite H0. ring. }
  { intros. destruct H0.
  - left. apply (Rlt_mult_compat_r _ _ C). auto. auto.
  - right. rewrite <- Rmult_1_l. apply Rpositive_not_zero in H.
    rewrite <- (Rmult_inv_r' _ H). 
    assert (C * / exist (fun a0 : Real => ~ a0 == 0) C H * A == A * C */ exist (fun a0 : Real => ~ a0 == 0) C H)%R by ring.
    rewrite H0 in H1.
    rewrite H1. rewrite Rmult_assoc. rewrite Rmult_inv_r'. ring. }
Qed.

Theorem Rle_mult_l_compat:
  forall A B C : Real, Rpositive C -> (A <= B)%R <-> (C*A<= C*B)%R.
Proof.
  intros. repeat rewrite (Rmult_comm C). apply Rle_mult_r_compat. auto.
Qed.

Theorem R_Archimedian: forall A B, Rpositive A -> (B>A)%R -> exists (N:nat),
  (inject_Q (inject_Z (Z.of_nat N)) * A > B)%R.
Proof. intros.
  destruct B as [B HB],A as [A HA].
  assert (E0: Rpositive (Real_intro B HB)).
    { apply Rpositive_gt_0. apply (Rlt_trans _ (Real_intro A HA));auto.
      apply (proj1 (Rpositive_gt_0 _)). auto. }
  pose proof (CauchySeqBounded _ HB) as [M [HM H1]].
  destruct H as [eps [Heps [N1 HN1]]].
  exists ((Z.to_nat((Qceiling M)+1))*Z.to_nat(Qceiling (/eps)))%nat.
  assert (E1:(0 < Qceiling M + 1)%Z). { assert (0 <= M)%Q.
    apply Qlt_le_weak. auto. apply Qceiling_resp_le in H.
    assert (0%Z=Qceiling 0) by reflexivity. rewrite H2.
    omega. }
  assert (E2:(0 <= Qceiling M + 1)%Z). { assert (0 <= M)%Q.
    apply Qlt_le_weak. auto. apply Qceiling_resp_le in H.
    assert (0%Z=Qceiling 0) by reflexivity. rewrite H2.
    omega. }
  assert (E3: (0 < Qceiling (/ eps))%Z). {
    destruct (Z.lt_ge_cases 0  (Qceiling (/ eps))%Z). auto.
    pose proof (Qle_ceiling (/eps)).
    rewrite Zlt_Qlt. apply (Qlt_le_trans _ (/eps)).
    apply Qinv_lt_0_compat. auto. auto. }
  assert (E4: (0 <= Qceiling (/ eps))%Z). { apply Z.lt_le_incl. auto. }
 


  apply (Rlt_le_trans _ (inject_Q(inject_Z((Qceiling (M)+1))))).
  - destruct E0 as [epsB [HepsB [NB HNB]]].
      hnf. exists 1. split.
      { reflexivity. }
      exists NB.
      unfold Rminus. unfold Ropp. unfold inject_Q.
      unfold Rplus. unfold CauchySeqPlus. unfold Cauchy_opp.
      intros.
      destruct (Cauchy_exists _ HB n) as [qb Hqb].
      assert (q == inject_Z (Qceiling M + 1) - qb). {
        apply H2. reflexivity. intros.
        rewrite (Cauchy_unique _ HB _ _ _ H3 Hqb). reflexivity. }
      rewrite H3. rewrite inject_Z_plus.
      rewrite <- Qplus_0_r.
      assert (inject_Z (Qceiling M) + inject_Z 1 - qb == 1 + (inject_Z (Qceiling M) - qb)) by ring.
      rewrite H4. clear H4.
      apply (proj2 (Qplus_le_r _ _ _)). apply (proj1 (Qplus_le_l _ _ qb)).
      rewrite Qplus_0_l. apply (Qle_trans _ M).
      { apply (Qle_trans _ (Qabs qb)). apply Qle_lteq. right.
        symmetry. apply Qabs_pos. apply (Qle_trans _ epsB). apply Qlt_le_weak. auto.
        apply (HNB n). auto. auto. apply Qlt_le_weak. apply (H1 n). auto. }
      { assert (inject_Z (Qceiling M) - qb + qb == inject_Z (Qceiling M)) by ring.
        rewrite H4. apply Qle_ceiling. }
  - rewrite Nat2Z.inj_mul. rewrite inject_Z_mult. rewrite inject_Q_mult.
    rewrite Z2Nat.id;auto. rewrite <- Rmult_1_r. rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    apply Rle_mult_l;auto. apply Rpositive_gt_0. apply Qlt_Rlt.
    assert (0==inject_Z 0) by reflexivity. rewrite H. rewrite <- Zlt_Qlt. auto.
    rewrite Rmult_1_l.
    apply (Rle_mult_l_compat _ _ (inject_Q (/(inject_Z (Z.of_nat (Z.to_nat (Qceiling (/eps)))))))).
    { apply inject_Q_Rpositive. apply Qinv_lt_0_compat. assert (0==inject_Z 0) by reflexivity.
      rewrite H. rewrite <- Zlt_Qlt. rewrite Z2Nat.id. omega. omega. }
    rewrite Rmult_1_r. apply (Rle_trans _ (Real_intro A HA)).
    + apply (Rle_trans _ (inject_Q eps)).
    ++ apply Qle_Rle. rewrite Z2Nat.id;auto.
      apply (Qle_trans _ ( / inject_Z (Qceiling (/ eps)))).
      { apply Qle_lteq. right. reflexivity. }
      { apply Qle_shift_inv_r. assert (0==inject_Z 0) by reflexivity. rewrite H. rewrite <- Zlt_Qlt. auto.
        apply (Qle_trans _ (eps*(/eps))). apply Qle_lteq. right. field. intros C. rewrite C in Heps. apply Qlt_irrefl in Heps. auto.
        apply Qmult_le_l. auto. apply Qle_ceiling. }
    ++  destruct (classic (inject_Q eps <= Real_intro A HA)%R).  auto.
      apply Rnot_le_lt in H. hnf in H. destruct H as [eps0 [Heps0 [N H]]].
      unfold Rminus in H. unfold Ropp in H. unfold inject_Q in H.
      unfold Rplus in H. unfold CauchySeqPlus in H. unfold Cauchy_opp in H.
      destruct (Cauchy_exists _ HA (max N1 N)) as [qa Hqa].
      assert (eps0 <= eps + -qa). { apply (H (max N1 N)). apply Nat.le_max_r.
      intros. rewrite H2. rewrite (H3 qa). ring. auto. }
      assert (eps <= qa). { apply (HN1 (max N1 N)).  apply Nat.le_max_l. auto. }
      assert (eps0 <= 0). { apply (Qle_trans _ _ _ H2). apply (Qplus_le_l _ _ qa).
      assert (eps + - qa + qa == eps) by ring. rewrite H4. rewrite Qplus_0_l.
      auto. } apply Qle_not_lt in H4. contradiction.
    + rewrite <- Rmult_assoc. rewrite <- inject_Q_mult.
      assert ((/ inject_Z (Z.of_nat (Z.to_nat (Qceiling (/ eps)))) *
    inject_Z (Z.of_nat (Z.to_nat (Qceiling (/ eps))))) == 1).
      { field. intros C. assert (0==inject_Z 0) by ring. rewrite H in C.
        apply (proj1 (inject_Z_injective _ _ )) in C.
        rewrite Z2Nat.id in C;auto. pose proof (Qle_ceiling (/eps)).
        rewrite C in H2. apply Qinv_lt_0_compat in Heps.
        apply Qle_not_lt in H2. contradiction. }
      rewrite H. rewrite Rmult_1_l. right. reflexivity.
Qed.



 