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


Definition Rlt (a b:Real) : Prop :=
  Rpositive (Rminus b a).


Notation "a < b" := (Rlt a b):Real_scope.

Theorem Rlt_trans: forall A B C, (A < B)%R -> (B < C)%R -> (A < C)%R.
Proof. intros.
  destruct A as [A HA], B as [B HB], C as [C HC]. hnf in *.
  unfold Rminus in *. unfold Ropp in *. unfold Cauchy_opp in *.
  unfold Rplus in *. unfold CauchySeqPlus in *.
  destruct H as [epsAB [HepsAB [NAB HAB]]]. destruct H0 as [epsBC [HepsBC [NBC HBC]]].
  destruct (take_max_N NAB NBC _ _ HAB HBC) as [N H]. clear HAB HBC.
  destruct (classic (epsAB<epsBC)) as [Heps|Heps].
  - exists (epsAB+epsAB). split.
      { rewrite <- Qplus_0_r. apply Qplus_lt_le_compat. auto. apply Qlt_le_weak. auto. }
    exists N. intros n Hn qac Hq.
    destruct (H n) as [H1 H2]. auto. clear H.
    destruct (Cauchy_exists _ HA n) as [qa Hqa],
             (Cauchy_exists _ HB n) as [qb Hqb],
             (Cauchy_exists _ HC n) as [qc Hqc].
    assert (E1: epsAB + epsAB <= epsAB + epsBC). 
      { apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak. auto. }
    assert (E2: qc - qa == (qb - qa) + (qc - qb)) by ring.
    assert (E3: qac == qc - qa). 
      { apply Hq. auto. intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
    assert (E4: epsAB <= (qb - qa)).
      { apply H1. intros. auto. rewrite (H0 qa Hqa).
        rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity. }
    assert (E5: epsBC <= (qc - qb)).
      { apply H2. intros. auto. rewrite (H0 qb Hqb).
        rewrite (Cauchy_unique _ HC _ _ _ Hqc H). reflexivity. }
    rewrite E3. rewrite E2. apply (Qle_trans _ _ _ E1).
    apply Qplus_le_compat. auto. auto.
  - exists (epsBC+epsBC). split.
      { rewrite <- Qplus_0_r. apply Qplus_lt_le_compat. auto. apply Qlt_le_weak. auto. }
    exists N. intros n Hn qac Hq. apply Qnot_lt_le in Heps.
    destruct (H n) as [H1 H2]. auto. clear H.
    destruct (Cauchy_exists _ HA n) as [qa Hqa],
             (Cauchy_exists _ HB n) as [qb Hqb],
             (Cauchy_exists _ HC n) as [qc Hqc].
    assert (E1: epsBC + epsBC <= epsAB + epsBC). 
      { apply Qplus_le_compat. auto. apply Qle_refl. }
    assert (E2: qc - qa == (qb - qa) + (qc - qb)) by ring.
    assert (E3: qac == qc - qa). 
      { apply Hq. auto. intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
    assert (E4: epsAB <= (qb - qa)).
      { apply H1. intros. auto. rewrite (H0 qa Hqa).
        rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity. }
    assert (E5: epsBC <= (qc - qb)).
      { apply H2. intros. auto. rewrite (H0 qb Hqb).
        rewrite (Cauchy_unique _ HC _ _ _ Hqc H). reflexivity. }
    rewrite E3. rewrite E2. apply (Qle_trans _ _ _ E1).
    apply Qplus_le_compat. auto. auto.
Qed.

Theorem Rlt_plus_r: forall (A B C:Real), (A < B)%R -> (A+C < B+C)%R.
Proof. intros. destruct A as [A HA], B as [B HB], C as [C HC]. hnf in *.
  unfold Rminus in *. unfold Rplus in *. unfold CauchySeqPlus in *.
  unfold Ropp in *. unfold Cauchy_opp in *. destruct H as [eps [Heps [N H]]].
  exists eps. split. auto. exists N. intros.
  destruct (Cauchy_exists _ HA n) as [qa Hqa],
           (Cauchy_exists _ HB n) as [qb Hqb],
           (Cauchy_exists _ HC n) as [qc Hqc].
  assert (E: q == (qb + qc) - (qa + qc)).
    { apply H1.
      - intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H3).
        rewrite (Cauchy_unique _ HB _ _ _ Hqb H2). reflexivity.
      - intros. rewrite (H2 _ _ Hqa Hqc). reflexivity. }
  assert (E1: (qb + qc) - (qa + qc) == qb - qa) by ring.
  apply (H n). auto. intros.
  rewrite <- (Cauchy_unique _ HB _ _ _ Hqb H2).
  assert (E3: q2 == - qa) by auto. rewrite E3.
  rewrite E. rewrite E1. reflexivity.
Qed.

Theorem Rlt_mult_r: forall (A B C:Real),  (Rpositive C) ->(A < B)%R -> (A*C < B*C)%R.
Proof. intros. destruct A as [A HA], B as [B HB], C as [C HC]. hnf in *.
  unfold Rminus in *. unfold Rplus in *. unfold CauchySeqPlus in *.
  unfold Ropp in *. unfold Cauchy_opp in *. unfold Rmult in *.
  unfold CauchySeqMult in *. destruct H as [eps1 [Heps1 [N1 H1]]].
  destruct H0 as [eps2 [Heps2 [N2 H2]]].
  destruct (take_max_N N1 N2 _ _ H1 H2) as [N H]. clear H1 H2 N1 N2.
  exists (eps2*eps1). split.
  { rewrite <- (Qmult_0_l eps1). apply (Qmult_lt_r). auto. auto. }
  exists N. intros n Hn q H0. destruct (H _ Hn) as [H1 H2]. clear H.
  destruct (Cauchy_exists _ HA n) as [qa Hqa],
           (Cauchy_exists _ HB n) as [qb Hqb],
           (Cauchy_exists _ HC n) as [qc Hqc].
  assert (E1: q == qb*qc - qa*qc).
  { apply H0.
    - intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H3).
      rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity.
    - intros. rewrite (H _ _ Hqa Hqc). reflexivity. }
  assert (E2: qb*qc - qa*qc == (qb-qa)*qc) by ring.
  assert (E3: eps2 <= qb -qa).
  { apply H2. intros. rewrite (H3 _ Hqa).
    rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity. }
  assert (E4: eps1 <= qc).
  { apply H1. auto. }
  rewrite E1,E2. apply Qmult_le_compat_nonneg.
  apply Qlt_le_weak. auto.
  apply Qlt_le_weak. auto.
  auto. auto.
Qed.

Instance Rlt_comp : Proper (Real_equiv ==> Real_equiv ==> iff) Rlt.
Proof. split.
- intros. unfold Rlt. assert (E1: (y0 - y==x0 - x)%R).
  rewrite <- H. rewrite H0. reflexivity.
  unfold Rlt in H1. rewrite E1. apply H1.
- intros. unfold Rlt. assert (E1: (y0 - y ==x0 - x)%R).
  rewrite <- H. rewrite H0. reflexivity.
  unfold Rlt in H1. rewrite <- E1. apply H1.
Qed.

Lemma Rlt_mult_l: forall (A B C:Real),  (Rpositive C) ->(A < B)%R -> (C*A< C*B)%R.
Proof. intros. rewrite (Rmult_comm C A). rewrite (Rmult_comm C B). apply Rlt_mult_r.
  auto. auto.
Qed.


Definition Rle (a b:Real) : Prop :=
  (a < b)%R \/ (a == b)%R.
Notation "a <= b" := (Rle a b):Real_scope.
Definition Rgt (a b:Real) : Prop :=
  (b < a)%R.
Notation "a > b" := (Rgt a b):Real_scope.
Definition Rge (a b:Real) : Prop :=
  (b <= a)%R.
Notation "a >= b" := (Rge a b):Real_scope.


Instance Rle_comp: Proper (Real_equiv ==> Real_equiv ==> iff) Rle.
Proof. split.
- intros. hnf. hnf in H1. destruct H1.
  left. rewrite <- H0. rewrite <- H. auto.
  right. rewrite <-H. rewrite <- H0. auto.
- intros. hnf. hnf in H1. destruct H1. 
  left. rewrite H. rewrite H0. auto.
  right. rewrite H,H0. auto.
Qed.
Instance Rgt_comp: Proper (Real_equiv ==> Real_equiv ==> iff) Rgt.
Proof. split.
- intros. unfold Rgt in *. rewrite <-H,<-H0. auto.
- intros. unfold Rgt in *. rewrite H,H0. auto.
Qed.



Theorem Rpositive_gt_0: forall x, Rpositive x <-> (0<x)%R.
Proof. intros. destruct x as [A HA]. split. 
  hnf in *. intros.
  destruct H as [eps [Heps [N HN]]]. exists eps. split. auto.
  exists N. unfold Rminus. unfold Ropp. unfold Cauchy_opp.
  unfold Rzero. unfold Rplus. unfold CauchySeqPlus.
  intros. destruct (Cauchy_exists _ HA n) as [qa Hqa].
  assert (E: q == qa). 
  { rewrite <- (Qplus_0_r qa). apply H0. auto. intros. rewrite H1. reflexivity. }
  rewrite E. apply (HN n). auto. auto.
  intros. hnf in *.
  destruct H as [eps [Heps [N HN]]]. exists eps. split. auto.
  exists N. unfold Rminus in *. unfold Ropp in *. unfold Cauchy_opp in *.
  unfold Rzero in *. unfold Rplus in *. unfold CauchySeqPlus in *.
  intros. destruct (Cauchy_exists _ HA n) as [qa Hqa].
  apply (HN n). auto. intros. rewrite (H2 0).
  rewrite (Cauchy_unique _ HA _ _ _ H0 H1).
  ring. ring.
Qed.

Theorem Rnegative_lt_0: forall x, Rnegative x <-> (x<0)%R.
Proof. intros. destruct x as [A HA]. split. hnf in *. intros.
  destruct H as [eps [Heps [N HN]]]. exists eps. split. auto.
  exists N. unfold Rminus. unfold Ropp in *. unfold Cauchy_opp in *.
  unfold Rzero. unfold Rplus. unfold CauchySeqPlus.
  intros. destruct (Cauchy_exists _ HA n) as [qa Hqa].
  assert (E:q == -qa).
  { rewrite <- (Qplus_0_l (- qa)). apply H0. reflexivity. intros.
    rewrite (Cauchy_unique _ HA _ _ _ Hqa H1). reflexivity. }
  rewrite E. apply (HN n). auto. intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H1).
  reflexivity.
  intros. hnf in *.
  destruct H as [eps [Heps [N HN]]]. exists eps. split. auto.
  exists N. unfold Rminus in *. unfold Ropp in *. unfold Cauchy_opp in *.
  unfold Rzero in *. unfold Rplus in *. unfold CauchySeqPlus in *.
  intros. apply (HN n). auto. intros. rewrite H1.
  destruct (Cauchy_exists _ HA n) as [qa Hqa].
  rewrite (H0 qa). rewrite (H2 qa). ring. auto. auto.
Qed.



Theorem Ropp_lt_compat: forall x y, (x<y)%R -> (-y < -x)%R.
Proof. intros. 
  assert (E1: (x + -(x + y) <y + -(x + y))%R).
  { apply Rlt_plus_r. auto. }
  assert (E2: (x + -(x + y) == -y)%R).
  { rewrite Ropp_plus_distr. rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_comm.
    rewrite Rplus_Zero. reflexivity. }
  assert (E3: (y + -(x + y) == -x)%R).
  { rewrite Ropp_plus_distr. rewrite <- Rplus_comm. rewrite Rplus_assoc. rewrite <- (Rplus_comm y).
    rewrite Rplus_opp_r. rewrite Rplus_Zero. reflexivity. }
  rewrite <- E3. rewrite <- E2. apply E1.
Qed.

Theorem Rzero_opp_zero: (0==-0)%R.
Proof. hnf. unfold Cauchy_opp.
  intros. exists O. intros.
  rewrite H1. rewrite (H2 _ H1). rewrite H1.
  apply H.
Qed.



Theorem Rplus_lt_compat: forall x y z, (x<y <-> x+z < y+z)%R.
Proof. intros. unfold Rlt in *.
  assert (E: (y + z - (x + z) == y - x)%R).
  { unfold Rminus. rewrite (Ropp_plus_distr x z).
    rewrite (Rplus_assoc). rewrite (Rplus_comm (-x) (-z)). 
    rewrite <- (Rplus_assoc z (-z)). rewrite Rplus_opp_r.
    rewrite Rplus_0_l. reflexivity. }
  rewrite E. split. auto. auto.
Qed.


Theorem Rnot_lt (x y:Real): (~(x<y) -> (x==y)\/(x>y))%R.
Proof. intros. unfold Rlt in *. apply Rnot_positive in H.
  destruct H.
  - right. apply Rnegative_lt_0 in H. apply (Rplus_lt_compat _ 0 x) in H.
    rewrite Rplus_0_l in H. unfold Rminus in H. rewrite Rplus_assoc in H.
    rewrite (Rplus_comm _ x) in H. rewrite (Rplus_opp_r) in H. rewrite Rplus_0_r in H.
    auto.
  - left. rewrite <- Rplus_0_l. rewrite <- H. unfold Rminus. rewrite Rplus_assoc.
    rewrite (Rplus_comm _ x). rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
Qed.


Lemma Rpositive_Ropp (A:Real): Rpositive A -> Rnegative (Ropp A).
Proof. intros. destruct A as [A HA]. hnf in *. unfold Ropp.
  unfold Cauchy_opp. destruct H as [eps [Heps [N H]]].
  exists eps. split. auto. exists N. intros.
  apply (H _ H0). destruct (Cauchy_exists _ HA n) as [qa Hqa].
  assert (E: q == qa). { rewrite <- (Qopp_involutive qa). apply H1.
  intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H2). reflexivity. }
  rewrite E. auto.
Qed.

Lemma Rnegative_Ropp (A:Real): Rnegative A -> Rpositive (Ropp A).
Proof. intros. destruct A as [A HA]. auto.
Qed.


Lemma Ropp_mult_distr : forall A B, (- (A * B) == (- A) * B)%R.
Proof. intros. destruct A as [A HA],B as [B HB]. hnf. intros. 
  exists O. intros. unfold Cauchy_opp in *. unfold CauchySeqMult in *.
  destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E1: q1 == - (qa*qb)). { apply H1. intros.
    rewrite (Cauchy_unique _ HA _ _ _ Hqa H3).
    rewrite (Cauchy_unique _ HB _ _ _ Hqb H4).
    reflexivity. }
  assert (E2: q2 == - qa*qb). { apply H2. intros. 
    rewrite (Cauchy_unique _ HA _ _ _ Hqa H3). reflexivity.
    auto. }
  assert (E3: q1 - q2 == 0). { rewrite E1. rewrite E2. ring. }
  rewrite E3. apply H.
Qed.


Lemma Rlt_irrefl: forall A, ~(A<A)%R.
Proof. intros. intros C. hnf in C. destruct C as [eps [Heps H]].
  destruct H as [N HN].
  pose proof (HN N (le_refl N) 0).
  assert (foo: eps <=0). { apply H. unfold Rminus. unfold Rplus. unfold Ropp.
    unfold Cauchy_opp. unfold CauchySeqPlus. destruct A.
    intros. pose proof (H2 _ H1). rewrite H3. ring. }
  apply Qle_not_lt in foo. contradiction.
Qed.


Theorem Rnot_lt_le: forall A B, (~(A<B)<->(A>=B))%R.
Proof. intros. split.
- intros. unfold Rlt in H. apply Rnot_positive in H. unfold Rnegative in H.
  assert (Et: (-(B-A) == A - B)%R). { unfold Rminus. rewrite Ropp_plus_distr.
    rewrite <- Ropp_involutive. rewrite Rplus_comm. reflexivity. }
  rewrite Et in H. unfold Rge. unfold Rle. destruct H.
  + left. unfold Rgt. auto.
  + right. rewrite <- (Rplus_0_l A). rewrite <- H. unfold Rminus. rewrite Rplus_assoc.
    rewrite (Rplus_comm _ A). rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
- intros. hnf in H. destruct H. 
  assert (Et: (-(A-B) == B - A)%R). { unfold Rminus. rewrite Ropp_plus_distr.
  rewrite <- Ropp_involutive. rewrite Rplus_comm. reflexivity. }
  + unfold Rlt in H. apply Rpositive_not_negative in H. intros C. apply H.
    unfold Rnegative.
    rewrite Et. auto.
  + rewrite H. apply Rlt_irrefl.
Qed.

Theorem Rnot_le_lt: forall A B, (~(A<=B) <-> (A >B))%R.
Proof. intros. split.
- intros. unfold Rle in H. apply not_or_and in H. destruct H.
  unfold Rlt in H. apply Rnot_positive in H. destruct H.
  * unfold Rgt. apply Rnegative_Ropp in H.
    assert (-(B-A)==A-B)%R by ring. rewrite H1 in H. auto.
  * assert (B==A)%R. { rewrite <-(Rplus_0_r A). rewrite <- H. ring. }
    symmetry in H1. contradiction.
- intros. unfold Rle. apply and_not_or. unfold Rgt in H. split.
  * apply Rpositive_not_negative in H. intros C. apply H.
    assert (A-B==-(B-A))%R by ring. rewrite H0. apply Rpositive_Ropp. auto.
  * apply Rpositive_not_zero in H. intros C. apply H. rewrite C. ring.
Qed.

Lemma Rlt_le_weak : forall A B, (A < B -> A <= B)%R.
Proof. intros. unfold Rle. left. auto.
Qed.

Lemma Rle_refl: forall A, (A<=A)%R.
Proof. intros. right. reflexivity.
Qed.

Lemma Rle_trans : forall x y z, (x<=y -> y<=z -> x<=z)%R.
Proof. intros. destruct H,H0.
- apply Rlt_le_weak. apply (Rlt_trans _ y).
  auto. auto.
- rewrite <- H0. apply Rlt_le_weak. auto.
- rewrite H. apply Rlt_le_weak. auto.
- rewrite H,H0. apply Rle_refl.
Qed.



Lemma Rle_lt_trans : (forall x y z, x<=y -> y<z -> x<z)%R.
Proof. intros. destruct H.
- apply (Rlt_trans _ y).
  auto. auto.
- rewrite H. auto.
Qed.

Lemma Rlt_le_trans : forall x y z, (x<y -> y<=z -> x<z)%R.
Proof. intros. destruct H0.
- apply (Rlt_trans _ y).
  auto. auto.
- rewrite <- H0. auto.
Qed.



Lemma Rinv_lt_0_compat' A (H:Rpositive A): Rpositive (/(exist _ A (Rpositive_not_zero _ H))).
Proof. hnf. hnf in H. destruct H as [eps [Heps [N HN]]].
  destruct A as [A HA].
  destruct (CauchySeqBounded _ HA) as [M [HM H2]]. unfold Rinv.
 exists (/M). split.
  - apply Qinv_lt_0_compat. auto.
  - exists N. intros. pose proof (HN _ H _ H0).
    pose proof (Qlt_le_trans _ _ _ Heps H1).
    pose proof (H2 _ _ H0).
    rewrite (Qabs_pos _ (Qlt_le_weak _ _ H3)) in H4.
    apply Qlt_le_weak.
    assert ( /q*M >0). {
      rewrite <- (Qmult_0_r (/q)). apply Qmult_lt_l. auto. auto. }
    apply (proj1 (Qmult_lt_r _ _ _ H5)).
    assert (Et1: / M * (/ q * M)==/q).
      { field. split. intros C. rewrite C in H3. apply Qlt_irrefl in H3. auto.
        intros C. rewrite C in HM. apply Qlt_irrefl in HM. auto. }
    assert (Et2: q * (/ q * M) == M).
      { field. intros C. rewrite C in H3. apply Qlt_irrefl in H3. auto. }
    rewrite Et1,Et2. auto.
Qed.

Lemma Rinv_lt_0_compat A (H0: ~(A==0)%R): Rpositive A 
  -> Rpositive (/(exist _ A H0)).
Proof. intros H. hnf. hnf in H. destruct H as [eps [Heps [N HN]]].
  destruct A as [A HA].
  destruct (CauchySeqBounded _ HA) as [M [HM H2]]. unfold Rinv.
 exists (/M). split.
  - apply Qinv_lt_0_compat. auto.
  - exists N. intros. pose proof (HN _ H _ H1).
    pose proof (Qlt_le_trans _ _ _ Heps H3).
    pose proof (H2 _ _ H1).
    rewrite (Qabs_pos _ (Qlt_le_weak _ _ H4)) in H5.
    apply Qlt_le_weak.
    assert ( /q*M >0). {
      rewrite <- (Qmult_0_r (/q)). apply Qmult_lt_l. auto. auto. }
    apply (proj1 (Qmult_lt_r _ _ _ H6)).
    assert (Et1: / M * (/ q * M)==/q).
      { field. split. intros C. rewrite C in H4. apply Qlt_irrefl in H4. auto.
        intros C. rewrite C in HM. apply Qlt_irrefl in HM. auto. }
    assert (Et2: q * (/ q * M) == M).
      { field. intros C. rewrite C in H4. apply Qlt_irrefl in H4. auto. }
    rewrite Et1,Et2. auto.
Qed.

Lemma Rlt_mult_compat_r:
  forall A B C : Real, Rpositive C -> (A*C < B*C)%R -> (A < B )%R.
Proof. intros.
  pose proof (Rpositive_not_zero _ H).
  apply (Rlt_mult_r _ _ (/(exist _ C H1)) (Rinv_lt_0_compat C H1 H)) in H0.
  rewrite Rmult_assoc in H0. rewrite Rmult_inv_r' in H0.
  rewrite Rmult_assoc in H0. rewrite Rmult_inv_r' in H0.
  repeat rewrite Rmult_1_r in H0. auto.
Qed.

Lemma Rlt_plus_compat_r:
  forall A B C : Real, (A+C < B+C)%R -> (A < B )%R.
Proof. intros.
  apply (Rlt_plus_r _ _ (-C)) in H.
  repeat rewrite Rplus_assoc in H.
  repeat rewrite Rplus_opp_r in H.
  repeat rewrite Rplus_0_r in H.
  auto.
Qed.


Lemma Rle_mult_compat_r:
  forall A B C : Real, Rpositive C -> (A*C <= B*C)%R -> (A <= B )%R.
Proof. intros. destruct H0.
- left. apply Rlt_mult_compat_r in H0. auto. auto.
- right. pose proof (Rpositive_not_zero _ H).
  apply (Rmult_inj_r_suff _ _ (/(exist _ C H1))) in H0.
  repeat rewrite Rmult_assoc in H0.
  repeat rewrite Rmult_inv_r' in H0.
  repeat rewrite Rmult_1_r in H0.
  auto.
Qed.

Lemma Rle_plus_compat_r:
  forall A B C : Real, (A+C <= B+C)%R -> (A <= B )%R.
Proof. intros. destruct H.
- left.
  apply (Rlt_plus_r _ _ (-C)) in H.
  repeat rewrite Rplus_assoc in H.
  repeat rewrite Rplus_opp_r in H.
  repeat rewrite Rplus_0_r in H. auto.
- right. apply (Rplus_inj_r _ _ C). auto.
Qed.

Lemma Rle_plus_r:
  forall A B C : Real, (A<= B)%R -> (A+C <= B+C )%R.
Proof. intros. destruct H.
- left.
  apply (Rlt_plus_r _ _ (C)) in H. auto.
- right. apply (Rplus_inj_r _ _ C). auto.
Qed.







Lemma Ropp_le_compat : forall A B, (A <= B <-> -B <= -A)%R.
Proof. intros. split.
  - intros. apply (Rle_plus_r _ _ (-A-B)) in H.
    assert (A + (- A - B)==-B)%R by ring.
    assert (B + (- A - B) == -A)%R by ring.
    rewrite H0 in H. rewrite H1 in H. auto.
  - intros. apply (Rle_plus_r _ _ (A+B)) in H.
    assert (-A + (A +B)==B)%R by ring.
    assert (-B + ( A + B) == A)%R by ring.
    rewrite H0 in H. rewrite H1 in H. auto.
Qed.


Lemma Rlt_plus_l: forall A B C : Real, (A < B)%R -> (C + A < C + B)%R.
Proof. intros. repeat rewrite (Rplus_comm C).
  apply (Rlt_plus_r _ _ C). auto.
Qed.

Lemma Rlt_plus_compat: forall A B C D, (A < B -> C < D -> A + C < B + D)%R.
Proof. intros. apply (Rlt_trans _ (A+D)).
  apply Rlt_plus_l. auto.
  apply Rlt_plus_r. auto.
Qed.

Lemma Rle_plus_l: forall A B C: Real, (A<=B)%R -> (C+A <= C+B)%R.
Proof. intros. destruct H.
  - left. apply (Rlt_plus_l _ _ C). auto.
  - right. rewrite H. reflexivity.
Qed.

Lemma Rle_lt_plus_compat: forall A B C D, (A <= B -> C < D -> A + C < B + D)%R.
Proof. intros. apply (Rlt_le_trans _ (A+D)). 
  apply Rlt_plus_l. auto.
  apply Rle_plus_r. auto.
Qed.

Lemma Rlt_le_plus_compat: forall A B C D, (A < B -> C <= D -> A + C < B + D)%R.
Proof. intros. apply (Rle_lt_trans _ (A+D)). 
  apply Rle_plus_l. auto.
  apply Rlt_plus_r. auto.
Qed.



Lemma Qlt_Rlt:
  forall q1 q2 : Q, (inject_Q q1 < inject_Q q2)%R <-> q1 < q2.
Proof. split.
- intros. hnf in H.
  hnf in H. repeat destruct H as [eps [Heps [N HN]]].
  pose proof (HN N (le_refl _) (q2-q1)).
  unfold Rminus in H. unfold Ropp in H. unfold inject_Q in H.
  unfold Rplus in H. unfold CauchySeqPlus in H.
  unfold Cauchy_opp in H.
  assert (eps<=q2-q1). { apply H. intros. rewrite H0. rewrite (H1 q1). reflexivity. reflexivity. }
  apply Qlt_minus_iff. apply (Qlt_le_trans _ _ _ Heps H0).
- intros.  hnf.
  exists (q2-q1). split. apply (proj1 (Qlt_minus_iff _ _)). auto.
  exists O. intros. hnf in H1. unfold Cauchy_opp in H1.
  rewrite (H1 q2 (-q1)). apply Qle_refl. reflexivity. intros.
  rewrite H2. reflexivity.
Qed.

Lemma Qle_Rle:
  forall q1 q2 : Q, (inject_Q q1 <= inject_Q q2)%R <-> q1 <= q2.
Proof. split.
- intros. apply Qle_lteq. hnf in H.
  destruct H.
  + left. apply Qlt_Rlt. auto.
  + right. auto using inject_Q_eq_inv.
- intros. apply Qle_lteq in H. destruct H.
  + left. apply Qlt_Rlt. auto.
  + right. rewrite H. reflexivity.
Qed.



Theorem inject_Q_lt_inv: forall q1 q2, (inject_Q q1 < inject_Q q2)%R <-> q1 < q2.
Proof. intros. split.
- intros. hnf in H.
  destruct (classic (q1 < q2)). auto.
  assert (E':q2 - q1>0).
  { destruct H. destruct H. destruct H1.
    apply (Qlt_le_trans _ x). auto. apply (H1 x0).
    omega. hnf. unfold Cauchy_opp. intros.
    rewrite H2. rewrite (H3 q1). reflexivity. reflexivity. }
  apply (Qplus_lt_r _ _ q1) in E'.
  assert (Et: q1 + (q2 - q1) == q2) by ring.
  rewrite Et in E'.
  rewrite Qplus_0_r in E'. auto.
- intros. hnf. exists (q2 - q1). split.
  { apply (Qplus_lt_r _ _ q1). rewrite Qplus_0_r.
    assert (Et: q1 + (q2 - q1) == q2) by ring.
    rewrite Et. auto. }
  exists O. intros. hnf in H1.
  rewrite (H1 q2 (-q1)). apply Qle_refl.
  reflexivity. hnf. intros. rewrite H2. reflexivity.
Qed.


Lemma inject_Q_Rpositive: forall q, q>0 <-> Rpositive (inject_Q q).
Proof. intros. split.
  - intros. apply Rpositive_gt_0. apply Qlt_Rlt. auto.
  - intros. apply Rpositive_gt_0 in H. apply Qlt_Rlt in H. auto.
Qed.




