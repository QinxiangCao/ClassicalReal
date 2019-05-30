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
From CReal.Cauchy Require Import RBase.
From CReal Require Import QArith_ext.QArith_base_ext.


(*Next, define the plus operation *)
Definition CauchySeqPlus (A B: nat -> Q -> Prop): (nat -> Q -> Prop) :=
  fun (n:nat) (q:Q) =>
     forall (q1 q2:Q), A n q1 -> B n q2 -> q == q1 + q2.


Theorem Cauchy_Plus_Cauchy: forall A B, Cauchy A -> Cauchy B
  -> Cauchy (CauchySeqPlus A B).
Proof. intros A B HA HB. split.
- unfold CauchySeqPlus. intros. destruct (Cauchy_exists _ HA n) as [qa Hqa].
  destruct (Cauchy_exists _ HB n) as [qb Hqb].
  exists (qa + qb). intros q1 q2 HqA HqB.
  assert (E1:qa == q1). { apply (Cauchy_unique _ HA n qa q1). apply Hqa. apply HqA. }
  assert (E2:qb == q2). { apply (Cauchy_unique _ HB n qb q2). apply Hqb. apply HqB. }
  rewrite E1. rewrite E2. reflexivity.
- unfold CauchySeqPlus. intros n q1 q2 H1 H2.
  destruct (Cauchy_exists _ HA n) as [qa Hqa]. destruct (Cauchy_exists _ HB n) as [qb Hqb].
  assert (E1: q1 == qa + qb). { auto. }
  assert (E2: q2 == qa + qb). { auto. }
  rewrite E1. rewrite E2. reflexivity.
- intros. hnf in H0. hnf. intros. rewrite <- H. auto.
- unfold CauchySeqPlus. intros eps Heps.
  destruct ((Cauchy_def _ HA) _ (eps_divide_2_positive eps Heps)) as [n1 HAC].
  destruct ((Cauchy_def _ HB) _ (eps_divide_2_positive eps Heps)) as [n2 HBC].
  assert (H2: eps == eps *(1#2) + eps *(1#2)) by ring.

assert (Hn: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct Hn.
  * exists n2. intros m1 m2 Hm1n2 Hm2n2 q1 q2 Hq1 Hq2.
    destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1], (Cauchy_exists _ HA m2) as [qa2 Hqa2].
    destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1], (Cauchy_exists _ HB m2) as [qb2 Hqb2].
    rewrite (Hq1 qa1 qb1 Hqa1 Hqb1). rewrite (Hq2 qa2 qb2 Hqa2 Hqb2).
    assert (Et: qa1 + qb1 - (qa2 + qb2) == (qa1 - qa2) + (qb1 - qb2)) by ring.
    rewrite Et. rewrite H2.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply Qplus_lt_le_compat.
    assert (Hm1n1: (m1 > n1)%nat) by omega. assert (Hm2n1: (m2>n1)%nat) by omega.
    apply (HAC m1 m2 Hm1n1 Hm2n1 qa1 qa2 Hqa1 Hqa2).
    apply Qlt_le_weak. apply (HBC m1 m2 Hm1n2 Hm2n2 qb1 qb2 Hqb1 Hqb2).

  * exists n1. apply not_le in H. intros m1 m2 Hm1n1 Hm2n1 q1 q2 Hq1 Hq2.
    destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1], (Cauchy_exists _ HA m2) as [qa2 Hqa2].
    destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1], (Cauchy_exists _ HB m2) as [qb2 Hqb2].
    rewrite (Hq1 qa1 qb1 Hqa1 Hqb1). rewrite (Hq2 qa2 qb2 Hqa2 Hqb2).
    assert (Et: qa1 + qb1 - (qa2 + qb2) == (qa1 - qa2) + (qb1 - qb2)) by ring.
    rewrite Et. rewrite H2.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply Qplus_lt_le_compat.
    apply (HAC m1 m2 Hm1n1 Hm2n1 qa1 qa2 Hqa1 Hqa2).
    assert (Hm1n2: (m1 > n2)%nat) by omega. assert (Hm2n2: (m2>n2)%nat) by omega.
    apply Qlt_le_weak. apply (HBC m1 m2 Hm1n2 Hm2n2 qb1 qb2 Hqb1 Hqb2).
Qed.

Definition Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqPlus A B) (Cauchy_Plus_Cauchy A B HA HB)
                          end
  end.

Infix "+" := Rplus : Real_scope.


Definition Rzero:Real :=
 Real_intro (fun (n:nat) => (fun x => x == 0)) (Real_has_Q 0).

Notation " 0 " := Rzero : Real_scope.

Theorem Cauchy_Plus_equiv: forall (A1 A2 B1 B2: Real),
  (A1 == A2)%R -> (B1 == B2)%R ->
  ((Rplus A1 B1) == (Rplus A2 B2))%R. 
Proof. intros A1 A2 B1 B2 HeqA HeqB. unfold Real_equiv in *.
  destruct A1 as [a1 Ha1], B1 as [b1 Hb1].
  destruct A2 as [a2 Ha2], B2 as [b2 Hb2].
  unfold Rplus. intros eps Heps.
  destruct (HeqA _ (eps_divide_2_positive _ Heps)) as [n1 Heqa].
  destruct (HeqB _ (eps_divide_2_positive _ Heps)) as [n2 Heqb].
  clear HeqA. clear HeqB.
  assert (Heps': eps == eps *(1#2) + eps *(1#2)) by ring.
assert (Hn: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct Hn as [Hn |Hn].
  * exists n2. intros m Hn2. assert (Hn1: (m > n1)%nat) by omega.
    unfold CauchySeqPlus. intros q1 q2 H1 H2.
    destruct (Cauchy_exists _ Ha1 m) as [qa1 Hqa1].
    destruct (Cauchy_exists _ Ha2 m) as [qa2 Hqa2].
    destruct (Cauchy_exists _ Hb1 m) as [qb1 Hqb1].
    destruct (Cauchy_exists _ Hb2 m) as [qb2 Hqb2].
    rewrite (H1 qa1 qb1 Hqa1 Hqb1). rewrite (H2 qa2 qb2 Hqa2 Hqb2).
    assert (H': qa1 + qb1 - (qa2 + qb2) == qa1 - qa2 + (qb1 - qb2)) by ring.
    rewrite H'. rewrite Heps'.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply Qplus_lt_le_compat.
    apply (Heqa m Hn1 _ _ Hqa1 Hqa2).
    apply Qlt_le_weak. apply (Heqb m Hn2 _ _ Hqb1 Hqb2).

  * exists n1. intros m Hn1. assert (Hn2: (m > n2)%nat) by omega.
    unfold CauchySeqPlus. intros q1 q2 H1 H2.
    destruct (Cauchy_exists _ Ha1 m) as [qa1 Hqa1].
    destruct (Cauchy_exists _ Ha2 m) as [qa2 Hqa2].
    destruct (Cauchy_exists _ Hb1 m) as [qb1 Hqb1].
    destruct (Cauchy_exists _ Hb2 m) as [qb2 Hqb2].
    rewrite (H1 qa1 qb1 Hqa1 Hqb1). rewrite (H2 qa2 qb2 Hqa2 Hqb2).
    assert (H': qa1 + qb1 - (qa2 + qb2) == qa1 - qa2 + (qb1 - qb2)) by ring.
    rewrite H'. rewrite Heps'.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply Qplus_lt_le_compat.
    apply (Heqa m Hn1 _ _ Hqa1 Hqa2).
    apply Qlt_le_weak. apply (Heqb m Hn2 _ _ Hqb1 Hqb2).
Qed.


Theorem Rplus_comm : forall (A B: Real),
  (A + B == B + A)%R.
Proof. intros. unfold Real_equiv. destruct A as [A HA], B as [B HB].
  unfold Rplus. intros eps Heps. exists O. intros m Hm q1 q2 H1 H2.
  unfold CauchySeqPlus in *.
  destruct (Cauchy_exists _ HA m) as [qa Hqa]. destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E1: q1 == qa + qb). { apply H1. apply Hqa. apply Hqb. }
  assert (E2: q2 == qb + qa). { apply H2. apply Hqb. apply Hqa. }
  rewrite E1. rewrite E2. assert (E:qa + qb - (qb + qa) == 0) by ring.
  rewrite E. apply Heps.
Qed.

Theorem Rplus_assoc: forall (A B C: Real),
  (A + B + C == A + (B + C))%R.
Proof. intros. unfold Real_equiv. destruct A as [A HA], B as [B HB], C as [C HC].
  unfold Rplus. intros eps Heps. exists O. intros m Hm q1 q2 H1 H2.
  unfold CauchySeqPlus in *. destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb]. destruct (Cauchy_exists _ HC  m) as [qc Hqc].
  assert (E1: q1 == qa + qb + qc). {
    apply (H1 (qa+qb)%Q qc). intros qa' qb' Hqa' Hqb'.
      assert (Ea':qa' == qa). { apply (Cauchy_unique _ HA m). apply Hqa'. apply Hqa. }
      assert (Eb':qb' == qb). { apply (Cauchy_unique _ HB m). apply Hqb'. apply Hqb. }
    rewrite Ea',Eb'. reflexivity. apply Hqc. }
  assert (E2: q2 == qa + (qb + qc)). {
    apply (H2 qa (qb+qc)%Q). apply Hqa. intros qb' qc' Hqb' Hqc'.
      assert (Ec':qc' == qc). { apply (Cauchy_unique _ HC m). apply Hqc'. apply Hqc. }
      assert (Eb':qb' == qb). { apply (Cauchy_unique _ HB m). apply Hqb'. apply Hqb. }
    rewrite Ec',Eb'. reflexivity. }
  rewrite E1,E2. rewrite Qplus_assoc. unfold Qminus. rewrite Qplus_opp_r.
  apply Heps.
Qed.

Theorem Rplus_Zero: forall (A : Real),
  (A + Rzero == A)%R.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros eps Heps. unfold CauchySeqPlus.
  exists O. intros m Hm q1 q2 H1 H2.
  assert (E:0 == 0) by reflexivity.
  rewrite (H1 q2 0 H2 E). rewrite Qplus_0_r. unfold Qminus.
  rewrite Qplus_opp_r. apply Heps.
Qed.


Definition Cauchy_opp (A : nat -> Q -> Prop): (nat -> Q -> Prop) :=
    fun (n:nat) (q:Q) =>
     forall (q1:Q), (A n q1) -> q == - q1.


Theorem Cauchy_opp_Cauchy: forall A, Cauchy A 
  -> Cauchy (Cauchy_opp A).
Proof. intros. unfold Cauchy_opp. split.
  - intros. destruct (Cauchy_exists _ H n) as [q Hq]. exists (- q).
    intros. rewrite (Cauchy_unique _ H n q q1 Hq H0). reflexivity.
  - intros n q1 q2 H1 H2. destruct (Cauchy_exists _ H n) as [q Hq].
    assert (E1: q1 == - q) by (apply (H1 q Hq)).
    assert (E2: q2 == - q) by (apply (H2 q Hq)).
    rewrite E1,E2. reflexivity.
  - intros. rewrite <- H0. auto.
  - intros. apply (Cauchy_def _ H) in H0. destruct H0 as [n H0].
    exists n. intros.
    destruct (Cauchy_exists _ H m1) as [qa Hqa], (Cauchy_exists _ H m2) as [qb Hqb].
    rewrite (H3 qa Hqa). rewrite (H4 qb Hqb).
    assert (Eq: - qa - - qb == qb - qa) by ring.
    rewrite Eq. rewrite Qabs_Qminus. apply (H0 m1 m2 H1 H2 qa qb Hqa Hqb).
Qed.

Fixpoint Ropp(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (Cauchy_opp A) (Cauchy_opp_Cauchy A HA) 
  end.
Notation "- x" := (Ropp x) : Real_scope.

Definition Rminus (a b:Real) := Rplus a (Ropp b).

Infix "-" := Rminus : Real_scope.

Theorem Rplus_opp_r : forall (A:Real), Real_equiv (A + (Ropp A))  Rzero.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros eps Heps. exists O. unfold Cauchy_opp. unfold CauchySeqPlus.
  intros m Hm q1 q2 H1 H2.
  destruct (Cauchy_exists _ Ha m) as [qa Hqa].
  assert (q1 == qa + (- qa)). { apply H1. apply Hqa. intros.
    assert (E: qa == q0). { apply (Cauchy_unique _ Ha m _ _ Hqa H). }
    rewrite E. reflexivity. }
  rewrite H. rewrite Qplus_opp_r. rewrite H2. apply Heps.
Qed. 





(*Then define multiplication *)

Definition CauchySeqMult (A B: nat -> Q -> Prop): (nat -> Q -> Prop) :=
  fun (n:nat) (q:Q) =>
     forall (q1 q2:Q), A n q1 -> B n q2 -> q == q1 * q2.

Lemma CauchySeqBounded_weak: forall A, Cauchy A -> exists (N:nat),
  exists (M:Q), forall (n:nat) (q:Q),(n>N)%nat -> A n q -> (Qabs q) < M.
Proof. intros. assert (E: Qlt 0 1) by reflexivity.
  apply (Cauchy_def _ H 1) in E. destruct E as [n Hn].
  exists n. destruct (Cauchy_exists _ H (S n)). exists (1 + (Qabs x))%Q.
  intros n' q Hn' Hq.
  assert (E: Qabs q <= (Qabs (q - x)) + (Qabs x)).
    { assert (E': q == (q - x) + x) by ring.
      remember (q-x) as q'. rewrite E'. rewrite Heqq'. apply (Qabs_triangle (q - x) x). }
      apply (Qle_lt_trans _ _ _ E). apply (Qplus_lt_le_compat (Qabs (q-x)) 1 (Qabs x)).
      * apply (Hn n' (S n)). auto. auto. auto. auto.
      * apply Qle_refl. 
Qed.

Lemma FiniteSeqBounded: forall (A:nat->Q->Prop) (N:nat), Cauchy A ->
  exists (M:Q), forall (n:nat)(q:Q), (n < N)%nat -> A n q -> Qabs q < M. 
Proof. intros. induction N.
  - exists 0. intros. inversion H0.
  - destruct IHN as [M IH]. destruct (Cauchy_exists _ H N) as [xN HxN].
    assert (Hq: Qlt (Qabs xN) M \/ ~ (Qlt (Qabs xN) M)). { apply classic. } destruct Hq as [Hq | Hq].
    + exists M. intros. unfold lt in H0. apply le_S_n in H0. apply Nat.le_lteq in H0. destruct H0.
      * apply (IH n). auto. auto.
      * rewrite <- H0 in HxN. assert (E: xN == q). { apply (Cauchy_unique _ H n _ _ HxN H1). }
        rewrite <- E. apply Hq.
    + exists (1+(Qabs xN))%Q. apply Qnot_lt_le in Hq. intros. 
      unfold lt in H0. apply le_S_n in H0. apply Nat.le_lteq in H0. destruct H0.
      * rewrite <- Qplus_0_l. apply Qplus_lt_le_compat. reflexivity.
        apply (Qle_trans _ M). apply Qlt_le_weak. apply (IH n). apply H0. apply H1. apply Hq.
      * rewrite <- Qplus_0_l. apply Qplus_lt_le_compat. reflexivity.
        rewrite <- H0 in HxN.
        assert (E: xN == q). { apply (Cauchy_unique _ H n _ _ HxN H1). }
        rewrite <- E. apply Qle_lteq. right. reflexivity.
Qed.

Lemma CauchySeqBounded: forall A, Cauchy A ->
  exists (M:Q), 0 < M /\forall (n:nat) (q:Q), A n q -> (Qabs q) < M.
Proof. intros. destruct (CauchySeqBounded_weak _ H) as [N [M1 HM1]].
  destruct (FiniteSeqBounded _ (S N) H) as [M2 HM2].
  assert (HM: Qle M1 M2 \/ ~ (Qle M1 M2)). { apply classic. } destruct HM as [HM | HM].
- exists M2. split.
  { destruct (Cauchy_exists _ H O). assert (E: (0 < S N)%nat) by omega.
    apply (HM2 _ _ E) in H0. apply (Qle_lt_trans _ _ _ (Qabs_nonneg x)). auto. }
  { intros. assert (Hn: (n > N)%nat \/ ~ (n>N)%nat). { apply classic. } destruct Hn as [Hn|Hn].
  + apply (Qlt_le_trans _ M1). apply (HM1 n). auto. auto. auto.
  + apply (HM2 n). apply not_lt in Hn. unfold ge in Hn. apply le_lt_n_Sm. auto. auto. }
- exists M1. split.
  { destruct (Cauchy_exists _ H (S N)). assert (E: (S N > N)%nat) by omega.
    apply (HM1 _ _ E) in H0. apply (Qle_lt_trans _ _ _ (Qabs_nonneg x)). auto. }
  { intros. assert (Hn: (n > N)%nat \/ ~ (n>N)%nat). { apply classic. } destruct Hn as [Hn|Hn].
  + apply (HM1 n). auto. auto.
  + apply (Qlt_le_trans _ M2). apply (HM2 n). apply not_lt in Hn. unfold ge in Hn. apply le_lt_n_Sm. auto. auto.
    apply Qnot_le_lt in HM. apply Qle_lteq. left. apply HM. }
Qed.


Theorem Cauchy_Mult_Cauchy : forall A B, Cauchy A -> Cauchy B
  -> Cauchy (CauchySeqMult A B).
Proof. intros A B HA HB. unfold CauchySeqMult. split.
- intros. destruct (Cauchy_exists _ HA n) as [q1 Hq1].
  destruct (Cauchy_exists _ HB n) as [q2 Hq2].
  exists (q1*q2). intros qa qb Hqa Hqb.
  assert (E1: q1 == qa) by (apply (Cauchy_unique _ HA _ _ _ Hq1 Hqa)).
  assert (E2: q2 == qb) by (apply (Cauchy_unique _ HB _ _ _ Hq2 Hqb)).
  rewrite E1,E2. reflexivity.
- intros. destruct (Cauchy_exists _ HA n) as [qa Hqa].
  destruct (Cauchy_exists _ HB n) as [qb Hqb].
  assert (E1 : q1 == qa * qb) by (apply (H qa qb Hqa Hqb)).
  assert (E2 : q2 == qa * qb) by (apply (H0 qa qb Hqa Hqb)).
  rewrite E1,E2. reflexivity.
- intros. rewrite <- H. auto.
- intros eps Heps.
  destruct (CauchySeqBounded _ HA) as [MA [MAp HMA]].
  destruct (CauchySeqBounded _ HB) as [MB [MBp HMB]].

assert (HM: MB <= MA \/ ~ (MB <= MA)). { apply classic. } destruct HM as [HM | HM].
{
  destruct (Cauchy_def _ HA (eps * (1#2) *(/ MA))) as [NA HNA].
   { apply (eps_divide_2M_positive eps MA Heps MAp). }
  destruct (Cauchy_def _ HB (eps * (1#2) *(/ MA))) as [NB HNB].
   { apply (eps_divide_2M_positive eps MA Heps MAp). }
  assert (E: eps == MA * (eps * (1 # 2) * / MA) + MA * (eps * (1 # 2) * / MA)).
   { rewrite <- Qmult_comm.
     rewrite <- (Qmult_assoc (eps * (1 # 2))).
     rewrite <- (Qmult_comm MA).
     rewrite Qmult_inv_r. ring.
     intros contra. rewrite contra in MAp. discriminate MAp.
   }
assert (HN: le NA NB \/ ~ (le NA NB)). { apply classic. } destruct HN as [HN | HN].
+ exists NB. intros m1 m2 Hm1B Hm2B.
  assert (Hm1A: (m1 > NA)%nat) by omega.
  assert (Hm2A: (m2 > NA)%nat) by omega.
  intros q1 q2. destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA m2) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB m2) as [qb2 Hqb2].
  intros HA1B1 HA2B2. assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2*qb2) by auto.
  rewrite E1,E2.
  assert (E3: qa1 * qb1 - qa2 * qb2 ==qa1 * (qb1 - qb2) + qb2 * (qa1-qa2)) by ring.
  rewrite E3.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 * (qb1 - qb2)) (qb2 * (qa1 - qa2)))).
  rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  rewrite E. apply Qplus_lt_le_compat.
  * apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa1) (Qabs_nonneg (qb1-qb2))).
    apply (HMA m1). auto.
    apply (HNB m1 m2). auto. auto. auto. auto.
  * apply Qlt_le_weak. apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb2) (Qabs_nonneg (qa1-qa2))).
    assert (E':Qabs qb2 < MB). { apply (HMB m2). auto. }
    apply (Qlt_le_trans _ _ _ E' HM).  auto.
    apply (HNA m1 m2). auto. auto. auto. auto.
+ exists NA. intros m1 m2 Hm1A Hm2A. apply not_le in HN.
  assert (Hm1B: (m1 > NB)%nat) by omega.
  assert (Hm2B: (m2 > NB)%nat) by omega.
  intros q1 q2. destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA m2) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB m2) as [qb2 Hqb2].
  intros HA1B1 HA2B2. assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2*qb2) by auto.
  rewrite E1,E2.
  assert (E3: qa1 * qb1 - qa2 * qb2 ==qa1 * (qb1 - qb2) + qb2 * (qa1-qa2)) by ring.
  rewrite E3.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 * (qb1 - qb2)) (qb2 * (qa1 - qa2)))).
  rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  rewrite E. apply Qplus_lt_le_compat.
  * apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa1) (Qabs_nonneg (qb1-qb2))).
    apply (HMA m1). auto.
    apply (HNB m1 m2). auto. auto. auto. auto.
  * apply Qlt_le_weak. apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb2) (Qabs_nonneg (qa1-qa2))).
    assert (E':Qabs qb2 < MB). { apply (HMB m2). auto. }
    apply (Qlt_le_trans _ _ _ E' HM).  auto.
    apply (HNA m1 m2). auto. auto. auto. auto.
}
{
  destruct (Cauchy_def _ HA (eps * (1#2) *(/ MB))) as [NA HNA].
   { apply (eps_divide_2M_positive eps MB Heps MBp). }
  destruct (Cauchy_def _ HB (eps * (1#2) *(/ MB))) as [NB HNB].
   { apply (eps_divide_2M_positive eps MB Heps MBp). }
  assert (E: eps == MB * (eps * (1 # 2) * / MB) + MB * (eps * (1 # 2) * / MB)).
   { rewrite <- Qmult_comm.
     rewrite <- (Qmult_assoc (eps * (1 # 2))).
     rewrite <- (Qmult_comm MB).
     rewrite Qmult_inv_r. ring.
     intros contra. rewrite contra in MBp. discriminate MBp.
   }
apply Qnot_le_lt in HM.
assert (HN: le NA NB \/ ~ (le NA NB)). { apply classic. } destruct HN as [HN | HN].
+ exists NB. intros m1 m2 Hm1B Hm2B.
  assert (Hm1A: (m1 > NA)%nat) by omega.
  assert (Hm2A: (m2 > NA)%nat) by omega.
  intros q1 q2. destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA m2) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB m2) as [qb2 Hqb2].
  intros HA1B1 HA2B2. assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2*qb2) by auto.
  rewrite E1,E2.
  assert (E3: qa1 * qb1 - qa2 * qb2 ==qa1 * (qb1 - qb2) + qb2 * (qa1-qa2)) by ring.
  rewrite E3.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 * (qb1 - qb2)) (qb2 * (qa1 - qa2)))).
  rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  rewrite E. apply Qplus_lt_le_compat.
  * apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa1) (Qabs_nonneg (qb1-qb2))).
    assert (E':Qabs qa1 < MA). { apply (HMA m1). auto. }
    apply (Qlt_trans _ _ _ E' HM).  auto.
    apply (HNB m1 m2). auto. auto. auto. auto.
  * apply Qlt_le_weak. apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb2) (Qabs_nonneg (qa1-qa2))).
    apply (HMB m2). auto.
    apply (HNA m1 m2). auto. auto. auto. auto.
+ exists NA. intros m1 m2 Hm1A Hm2A. apply not_le in HN.
  assert (Hm1B: (m1 > NB)%nat) by omega.
  assert (Hm2B: (m2 > NB)%nat) by omega.
  intros q1 q2. destruct (Cauchy_exists _ HA m1) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA m2) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB m1) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB m2) as [qb2 Hqb2].
  intros HA1B1 HA2B2. assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2*qb2) by auto.
  rewrite E1,E2.
  assert (E3: qa1 * qb1 - qa2 * qb2 ==qa1 * (qb1 - qb2) + qb2 * (qa1-qa2)) by ring.
  rewrite E3.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 * (qb1 - qb2)) (qb2 * (qa1 - qa2)))).
  rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  rewrite E. apply Qplus_lt_le_compat.
  * apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa1) (Qabs_nonneg (qb1-qb2))).
    assert (E':Qabs qa1 < MA). { apply (HMA m1). auto. }
    apply (Qlt_trans _ _ _ E' HM).  auto.
    apply (HNB m1 m2). auto. auto. auto. auto.
  * apply Qlt_le_weak. apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb2) (Qabs_nonneg (qa1-qa2))).
    apply (HMB m2). auto.
    apply (HNA m1 m2). auto. auto. auto. auto.
}
Qed.


Definition Rmult(a b:Real):Real:=
match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqMult A B) (Cauchy_Mult_Cauchy A B HA HB)
                          end
  end.

Infix "*" := Rmult : Real_scope.


Lemma CauchySeqBounded_two: forall A B, Cauchy A -> Cauchy B ->
  exists (M:Q), 0 < M 
  /\ (forall (n:nat) (q:Q), A n q -> (Qabs q) < M)
  /\ (forall (n:nat) (q:Q), B n q -> (Qabs q) < M) .
Proof. intros.
  destruct (CauchySeqBounded _ H) as [MA [MAp HMA]].
  destruct (CauchySeqBounded _ H0) as [MB [MBp HMB]].
  assert (HM: MB <= MA \/ ~ (MB <= MA)) by (apply classic). destruct HM as [HM|HM].
  - exists MA. split.
    apply MAp. split.
    apply HMA.
    intros. apply (Qlt_le_trans _ MB). apply (HMB n). apply H1. apply HM.
  - exists MB. split. apply MBp. split. intros.
    apply (Qlt_le_trans _ MA). apply (HMA n). auto. apply Qnot_le_lt in HM.
    apply Qlt_le_weak. auto.
    apply HMB.
Qed.


Theorem Cauchy_Mult_equiv: forall (A1 A2 B1 B2: Real),
  (A1 == A2)%R -> (B1 == B2)%R ->
  ((A1 * B1)%R == (A2 * B2)%R)%R.
Proof. intros [A1 HA1] [A2 HA2] [B1 HB1] [B2 HB2] HAeq HBeq.
  unfold Real_equiv in *. unfold Rmult. intros eps Heps.
  destruct (CauchySeqBounded_two _ _ HA2 HB1) as [M [Mp [HMA2 HMB1]]].
  destruct (HAeq (eps * (1#2) *(/ M))) as [NA1 HNA1].
   { apply (eps_divide_2M_positive eps M Heps Mp). }
  destruct (HBeq (eps * (1#2) *(/ M))) as [NB2 HNB2].
   { apply (eps_divide_2M_positive eps M Heps Mp). }
  
  assert (E: eps == M * (eps * (1 # 2) * / M) + M * (eps * (1 # 2) * / M)).
   { rewrite <- Qmult_comm.
     rewrite <- (Qmult_assoc (eps * (1 # 2))).
     rewrite <- (Qmult_comm M).
     rewrite Qmult_inv_r. ring.
     intros contra. rewrite contra in Mp. discriminate Mp.
   } unfold CauchySeqMult.
  assert (HN: le NA1 NB2 \/ ~ (le NA1 NB2)). { apply classic. } destruct HN as [HN | HN].
+ exists NB2. intros m HmNB2 q1 q2 Hq1 Hq2. unfold CauchySeqMult in *.
  destruct (Cauchy_exists _ HA1 m) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA2 m) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB1 m) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB2 m) as [qb2 Hqb2].
  assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2 * qb2) by auto.
  rewrite E1,E2.
  assert (E':qa1 * qb1 - qa2 * qb2 == qa2 * (qb1 - qb2) + qb1 * (qa1-qa2)) by ring.
  rewrite E',E.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa2 * (qb1 - qb2)) (qb1 * (qa1 - qa2)))).
  apply Qplus_lt_le_compat.
  * rewrite Qabs_Qmult.
    apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa2) (Qabs_nonneg (qb1-qb2))).
    { apply (HMA2 m). auto. } 
    { apply (HNB2 _ HmNB2). auto. auto. }
  * rewrite Qabs_Qmult. apply Qlt_le_weak.
    apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb1) (Qabs_nonneg (qa1-qa2))).
    apply (HMB1 m). auto.
    assert (HmNA1: (m > NA1)%nat) by omega.
    apply (HNA1 _ HmNA1). auto. auto.

+ exists NA1. intros m HmNA1 q1 q2 Hq1 Hq2. apply not_le in HN. unfold CauchySeqMult in *.
  destruct (Cauchy_exists _ HA1 m) as [qa1 Hqa1].
  destruct (Cauchy_exists _ HA2 m) as [qa2 Hqa2].
  destruct (Cauchy_exists _ HB1 m) as [qb1 Hqb1].
  destruct (Cauchy_exists _ HB2 m) as [qb2 Hqb2].
  assert (E1:q1 == qa1 * qb1) by auto.
  assert (E2:q2 == qa2 * qb2) by auto.
  rewrite E1,E2.
  assert (E':qa1 * qb1 - qa2 * qb2 == qa2 * (qb1 - qb2) + qb1 * (qa1-qa2)) by ring.
  rewrite E',E.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa2 * (qb1 - qb2)) (qb1 * (qa1 - qa2)))).
  apply Qplus_lt_le_compat.
  * rewrite Qabs_Qmult.
    assert (HmNB2: (m > NB2)%nat) by omega.
    apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qa2) (Qabs_nonneg (qb1-qb2))).
    { apply (HMA2 m). auto. } 
    { apply (HNB2 _ HmNB2). auto. auto. }
  * rewrite Qabs_Qmult. apply Qlt_le_weak.
    apply (Qmult_lt_compat_nonneg _ _ _ _ (Qabs_nonneg qb1) (Qabs_nonneg (qa1-qa2))).
    apply (HMB1 m). auto.
    apply (HNA1 _ HmNA1). auto. auto.
Qed.

(*Proofs about Rinv*)

Definition limit_not_0 (A:nat->Q->Prop):Prop:=
(exists (eps:Q), eps>0 /\ forall (N:nat), exists(nN:nat),(nN > N)%nat /\
   (forall(q:Q), A nN q -> Qabs q > eps)).

Lemma Non_0_QSeq: forall (A:nat->Q->Prop) n, Cauchy A -> 
( ~(A n 0) )<->( forall  q, A n q -> ~(q == 0)).
Proof. split.
 - intros. intros C. rewrite C in H1. apply H0 in H1. destruct H1.
 - intros. intros C. apply H0 in C. assert (T: 0 == 0) by reflexivity. apply C in T. destruct T.
Qed.


Definition limit_not_0_real (A:Real):Prop:=
match A with
| Real_intro CA HA => limit_not_0 CA
end.

(* Every limit-not-0 Cauchy Sequence will not be 0 after a certain N *)
Lemma limit_not_0_seq : forall A (H:Cauchy A), limit_not_0_real (Real_intro A H) ->
 exists (N:nat), forall n, (n>N)%nat ->forall q, A n q -> ~(q == 0).
Proof. intros. hnf in H0. destruct H0 as [eps [Heps H0]].
  destruct (Cauchy_def _ H _ Heps) as [N' HN'].
  destruct (H0 N') as [nN' [HnN' H']].
  exists nN'. intros.
  assert (E: (n > N')%nat) by omega.
  destruct (Cauchy_exists _ H nN') as [qnN' HqnN'].
  assert (E1: Qabs (qnN' - q) < eps). { apply (HN' nN' n). auto. auto. auto. auto. }
  apply H' in HqnN'.
  assert (E2: Qabs q >= Qabs (qnN') - Qabs (qnN' - q)).
  { assert (Et: q == qnN' - (qnN' - q)) by ring.
    remember (qnN' - q) as t.
    rewrite Et. rewrite Heqt. apply Qabs_triangle_reverse. }
  apply Qopp_lt_compat in E1. 
  assert (E3: Qabs qnN' - Qabs (qnN' - q) > eps - eps).
    { apply Qplus_lt_le_compat. auto. apply Qlt_le_weak. auto. }
  rewrite (Qplus_opp_r eps) in E3.
  assert (E4: Qabs q > 0). { apply (Qlt_le_trans _ _ _ E3 E2). }
  intros C. rewrite C in E4. discriminate E4. 
Qed.



(* Some helping lemmas in justifying Rinv *)
Lemma FiniteSeqBounded_Below_nonneg: forall (A:nat->Q->Prop) (N:nat), Cauchy A ->
  exists (M:Q), M>=0 /\ forall (n:nat)(q:Q), (n < N)%nat -> A n q -> Qabs q >= M. 
Proof. intros. induction N.
  - exists 1. intros. split. apply Qle_lteq. left. reflexivity. intros. inversion H0.
  - destruct IHN as [M [HM IH]]. destruct (Cauchy_exists _ H N) as [xN HxN].
    assert (Hq: Qlt M (Qabs xN) \/ ~ (Qlt M (Qabs xN))). { apply classic. } destruct Hq as [Hq | Hq].
    + exists M.
      split. apply HM.
      intros. unfold lt in H0. apply le_S_n in H0. apply Nat.le_lteq in H0. destruct H0.
      * apply (IH n). auto. auto.
      * rewrite <- H0 in HxN. assert (E: xN == q). { apply (Cauchy_unique _ H n _ _ HxN H1). }
        rewrite <- E. apply Qlt_le_weak. apply Hq.
    + exists ((Qabs xN))%Q. apply Qnot_lt_le in Hq. split.
      apply Qabs_nonneg.
 intros. 
      unfold lt in H0. apply le_S_n in H0. apply Nat.le_lteq in H0. destruct H0.
      * apply (Qle_trans _ M). apply Hq. apply (IH n). apply H0. apply H1.
      * rewrite <- H0 in HxN.
        assert (E: xN == q). { apply (Cauchy_unique _ H n _ _ HxN H1). }
        rewrite <- E. apply Qle_lteq. right. reflexivity.
Qed.



Lemma FiniteNo0SeqBounded_Below_positive: forall (A:nat->Q->Prop) (N:nat), Cauchy A ->
  (exists N',forall n, (n>N')%nat ->  ~(A n 0)) ->
  exists (N':nat),exists (M:Q), M>0 /\ forall (n:nat)(q:Q), (n>N')%nat -> (n < N)%nat -> A n q -> Qabs q >= M. 
Proof. intros. induction N. destruct H0 as [N' H0].
  - exists N',1. intros. split. reflexivity. intros. inversion H2.
  - destruct H0 as [N'1 H0].
    destruct IHN as [N' [M [HM IH]]]. destruct (Cauchy_exists _ H N) as [xN HxN].
    assert (Hq: Qlt M (Qabs xN) \/ ~ (Qlt M (Qabs xN))). { apply classic. } destruct Hq as [Hq | Hq].
    + exists N',M.
      split. apply HM.
      intros. unfold lt in H0. apply le_S_n in H2. apply Nat.le_lteq in H2. destruct H2.
      * apply (IH n). auto. auto. auto.
      * rewrite <- H2 in HxN. assert (E: xN == q). { apply (Cauchy_unique _ H n _ _ HxN H3). }
        rewrite <- E. apply Qlt_le_weak. apply Hq.
    + assert (En: lt N'1 N \/ ~ lt N'1 N) by (apply classic). destruct En as [En|En].
      * exists N,((Qabs xN))%Q. apply Qnot_lt_le in Hq. split.
        assert (E: 0<= Qabs xN) by (apply Qabs_nonneg). apply Qle_lteq in E.
        destruct E. apply H1. symmetry in H1. apply Qabs_0 in H1.
        rewrite H1 in HxN. apply H0 in HxN. destruct HxN. auto. intros.
        unfold lt in H1. omega.
      * exists N'1,1. split. reflexivity. intros.
        assert (E: lt N'1 N) by omega. contradiction.
Qed.

Lemma Cauchy_nonzero_pre: forall A  (HA:Cauchy A),  limit_not_0_real (Real_intro A HA)
  -> exists (N:nat),
( exists (eps0:Q), eps0>0 /\ (forall (n:nat), (n>N)%nat -> forall(q:Q), A n q -> Qabs q >= eps0)). 
Proof. intros A HA. intros H.  destruct (limit_not_0_seq _ HA H) as [N0 Hnot0].
  assert (Hlim: limit_not_0 A) by auto.
  destruct H as [eps [Heps H]].
  destruct (Cauchy_def _ HA (eps*(1#2)) (eps_divide_2_positive _ Heps)) as [N1 HN].
  destruct (H N1) as [nN1 [HnN1N HnN1]].

assert (E:exists (N':nat),exists (M:Q), M>0 /\ forall (n:nat)(q:Q), (n>N')%nat -> (n < (S N1))%nat -> A n q -> Qabs q >= M ).
{ apply FiniteNo0SeqBounded_Below_positive. auto.
  destruct (limit_not_0_seq _ HA Hlim). exists x. intros. apply Non_0_QSeq. auto. 
  intros. apply (H0 n). auto. auto. }
destruct E as [N' [x [Hx H0]]].

  assert (Eq: x < eps * (1#2) \/ ~(x<eps*(1#2))). { apply classic. } destruct Eq as [Eq | Eq].
  + exists N',x. split. apply Hx.
    intros. assert (En: lt n (S N1) \/ ~(lt n (S N1))) by (apply classic). destruct En.
    { apply (H0 n). auto. auto. auto. }
    { apply not_lt in H3. apply Qlt_le_weak. apply (Qlt_trans _ (eps*(1#2)) _).  apply Eq.
      destruct (Cauchy_exists _ HA nN1) as [qnN1 HqnN1].
      assert (E: (- q) == - (q - qnN1) - qnN1) by ring.
      rewrite <- Qabs_opp. rewrite E.
      apply (Qlt_le_trans _ (- Qabs (q - qnN1) +(Qabs qnN1))).
      * assert(E1: eps * (1 # 2) == - eps*(1#2) + eps) by ring.
        rewrite E1. 
        apply Qplus_lt_le_compat.
      { apply Qlt_minus_iff. rewrite Qplus_comm.
        assert (E2: - (- eps * (1 # 2))  == eps*(1#2)) by ring. rewrite E2.
        apply (Qlt_minus_iff (Qabs (q - qnN1))). apply (HN n nN1). omega. omega. auto. auto. }
      { apply Qlt_le_weak. apply HnN1. auto. }
      * rewrite Qplus_comm. rewrite <- (Qabs_opp qnN1).
        rewrite (Qplus_comm (- (q - qnN1)) (- qnN1)).
        apply Qabs_triangle_reverse.
    }
  + exists N',(eps*(1#2)). apply Qnot_lt_le in Eq. split.
    apply (eps_divide_2_positive _ Heps). intros. 
    assert (En: lt n (S N1) \/ ~(lt n (S N1))) by (apply classic). destruct En.
    { apply (Qle_trans _ x _). auto. apply (H0 n). auto. auto. auto. }
    { apply not_lt in H3. apply Qlt_le_weak.
      destruct (Cauchy_exists _ HA nN1) as [qnN1 HqnN1].
      assert (E: (- q) == - (q - qnN1) - qnN1) by ring.
      rewrite <- Qabs_opp. rewrite E.
      apply (Qlt_le_trans _ (- Qabs (q - qnN1) +(Qabs qnN1))).
      * assert(E1: eps * (1 # 2) == - eps*(1#2) + eps) by ring.
        rewrite E1. 
        apply Qplus_lt_le_compat.
      { apply Qlt_minus_iff. rewrite Qplus_comm.
        assert (E2: - (- eps * (1 # 2))  == eps*(1#2)) by ring. rewrite E2.
        apply (Qlt_minus_iff (Qabs (q - qnN1))). apply (HN n nN1). omega. omega. auto. auto. }
      { apply Qlt_le_weak. apply HnN1. auto. }
      * rewrite Qplus_comm. rewrite <- (Qabs_opp qnN1).
        rewrite (Qplus_comm (- (q - qnN1)) (- qnN1)).
        apply Qabs_triangle_reverse.
    }
Qed.

(* A Cauchy Sequence can have its inversion as long as its limit is not 0 *)
Lemma Cauchy_inv_nonzero: forall A  (H:Cauchy A) , limit_not_0_real (Real_intro A H) 
  -> Cauchy (fun (n:nat)(q:Q) => A n (/q)).
Proof. intros. split.
- intros. destruct (Cauchy_exists _ H n).
  exists (/x). rewrite <- (Qinv_involutive x) in H1. auto.
- intros. assert (E:/q1==/q2). { apply (Cauchy_unique _ H _ _ _ H1 H2). }
  rewrite <- Qinv_involutive. rewrite E. apply Qinv_involutive.
- intros. assert (E:/ p == / q). rewrite H1. reflexivity. rewrite <- E. auto.
- intros.
  assert (H0':(exists N', forall (n : nat), (n>N')%nat ->forall q, A n q -> ~ q == 0)). { apply (limit_not_0_seq _ H). auto. }
  destruct H0' as [N' H0'].
  destruct (Cauchy_nonzero_pre A H H0) as [N0 [eps0 [Heps0 H']]].
  assert (Eeps: 0 < eps * eps0 * eps0). 
  { rewrite <- (Qmult_0_l eps0). apply (Qmult_lt_compat_r _ _ _ Heps0).
    rewrite <- (Qmult_0_l eps0). apply (Qmult_lt_compat_r _ _ _ Heps0). apply H1. }
  destruct (Cauchy_def _ H _ Eeps) as [N HN].
  assert (En: lt N' N \/ ~ lt N' N) by (apply classic). destruct En as [En|En].
  { assert (En': lt N0 N \/ ~ lt N0 N) by (apply classic). destruct En' as [En'|En']. 
    { exists N. intros m1 m2 Hm1N Hm2N q1 q2 Hq1 Hq2.
      assert (E1:Qabs (/ q1 - / q2) < eps * eps0 * eps0). { apply (HN m1 m2). auto. auto. auto. auto. }
      assert (E2:Qabs(/q1) >0). 
      { assert (Eq:Qabs (/q1) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq1. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (E3:Qabs(/q2) >0). 
      { assert (Eq:Qabs (/q2) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq2. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (Em1N': (m1 > N')%nat) by omega.
      assert (Em2N': (m2 > N')%nat) by omega.
      assert (E4:/Qabs (/ q1) <= /eps0).
      { apply (Qmult_le_l _ _ _ E2). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em1N' _ Hq1))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m1). auto. omega. auto. }
      assert (E5:/Qabs (/ q2) <= /eps0).
      { apply (Qmult_le_l _ _ _ E3). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em2N' _ Hq2))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m2). auto. omega. auto. }
      assert (E6:q1 - q2 == (/q2-/q1)/((/q1)*(/q2))).
      { unfold Qdiv. unfold Qminus. rewrite Qmult_plus_distr_l.
        rewrite Qinv_mult_distr. rewrite Qinv_involutive. rewrite Qinv_involutive. 
        rewrite (Qmult_comm (/q2)). rewrite <- Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E3)))).
        rewrite (Qmult_assoc). 
        assert (Etmp: - / q1 * q1 * q2 == - (/ q1 * q1 * q2)) by ring. 
        rewrite Etmp. rewrite (Qmult_comm (/q1)). 
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E2)))).
        ring. }
      assert (E7:eps == eps * eps0 * eps0 *  (/ eps0 * / eps0)).
      { rewrite Qmult_assoc.
        rewrite <- (Qmult_assoc _ eps0 (/eps0)). 
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r.
        rewrite <- Qmult_assoc. rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        ring. }
      assert (E8: Qabs ((/ q2 - / q1) / (/ q1 * / q2)) ==
       Qabs (/ q2 - / q1) * (/ Qabs (/ q1) / Qabs (/ q2))).
      { unfold Qdiv. rewrite Qabs_Qmult.
        rewrite Qabs_Qinv. rewrite Qabs_Qmult. rewrite Qmult_assoc.
        rewrite Qinv_mult_distr. rewrite Qmult_assoc. reflexivity. }
      rewrite E6. rewrite E7. rewrite E8.
      assert (E9: / Qabs (/ q1) / Qabs (/ q2) > 0). 
      { rewrite <- (Qmult_0_l (/ Qabs (/ q2))).
        apply (Qmult_lt_compat_r _ _ _ (Qinv_lt_0_compat _ E3) (Qinv_lt_0_compat _ E2)). }
      apply ( Qmult_lt_compat_trans_positive (
          Qabs (/ q2 - / q1))             (eps * eps0 * eps0)
          (/ Qabs (/ q1) / Qabs (/ q2))   (/ eps0 * / eps0)).
      apply Qabs_nonneg. apply E9.
      rewrite Qabs_Qminus. apply E1.
      unfold Qdiv. apply Qmult_le_compat_nonneg.
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q1))).
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q2))).
      auto. auto.     }
    { exists N0. apply not_lt in En'.
      intros m1 m2 Hm1N Hm2N q1 q2 Hq1 Hq2.
      assert (E1:Qabs (/ q1 - / q2) < eps * eps0 * eps0). { apply (HN m1 m2). omega. omega. auto. auto.  }
      assert (E2:Qabs(/q1) >0). 
      { assert (Eq:Qabs (/q1) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq1. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (E3:Qabs(/q2) >0). 
      { assert (Eq:Qabs (/q2) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq2. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (Em1N': (m1 > N')%nat) by omega.
      assert (Em2N': (m2 > N')%nat) by omega.
      assert (E4:/Qabs (/ q1) <= /eps0).
      { apply (Qmult_le_l _ _ _ E2). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em1N' _ Hq1))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m1). auto. auto. }
      assert (E5:/Qabs (/ q2) <= /eps0).
      { apply (Qmult_le_l _ _ _ E3). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em2N' _ Hq2))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m2). auto. auto. }
      assert (E6:q1 - q2 == (/q2-/q1)/((/q1)*(/q2))).
      { unfold Qdiv. unfold Qminus. rewrite Qmult_plus_distr_l.
        rewrite Qinv_mult_distr. rewrite Qinv_involutive. rewrite Qinv_involutive. 
        rewrite (Qmult_comm (/q2)). rewrite <- Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E3)))).
        rewrite (Qmult_assoc). 
        assert (Etmp: - / q1 * q1 * q2 == - (/ q1 * q1 * q2)) by ring. 
        rewrite Etmp. rewrite (Qmult_comm (/q1)). 
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E2)))).
        ring. }
      assert (E7:eps == eps * eps0 * eps0 *  (/ eps0 * / eps0)).
      { rewrite Qmult_assoc.
        rewrite <- (Qmult_assoc _ eps0 (/eps0)). 
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r.
        rewrite <- Qmult_assoc. rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        ring. }
      assert (E8: Qabs ((/ q2 - / q1) / (/ q1 * / q2)) ==
       Qabs (/ q2 - / q1) * (/ Qabs (/ q1) / Qabs (/ q2))).
      { unfold Qdiv. rewrite Qabs_Qmult.
        rewrite Qabs_Qinv. rewrite Qabs_Qmult. rewrite Qmult_assoc.
        rewrite Qinv_mult_distr. rewrite Qmult_assoc. reflexivity. }
      rewrite E6. rewrite E7. rewrite E8.
      assert (E9: / Qabs (/ q1) / Qabs (/ q2) > 0). 
      { rewrite <- (Qmult_0_l (/ Qabs (/ q2))).
        apply (Qmult_lt_compat_r _ _ _ (Qinv_lt_0_compat _ E3) (Qinv_lt_0_compat _ E2)). }
      apply ( Qmult_lt_compat_trans_positive (
          Qabs (/ q2 - / q1))             (eps * eps0 * eps0)
          (/ Qabs (/ q1) / Qabs (/ q2))   (/ eps0 * / eps0)).
      apply Qabs_nonneg. apply E9.
      rewrite Qabs_Qminus. apply E1.
      unfold Qdiv. apply Qmult_le_compat_nonneg.
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q1))).
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q2))).
      auto. auto. }
    }

  { assert (En': lt N0 N' \/ ~ lt N0 N') by (apply classic). destruct En' as [En'|En']. 
    { apply not_lt in En. exists N'. intros m1 m2 Hm1N Hm2N q1 q2 Hq1 Hq2.
      assert (E1:Qabs (/ q1 - / q2) < eps * eps0 * eps0). { apply (HN m1 m2). omega. omega. auto. auto. }
      assert (E2:Qabs(/q1) >0). 
      { assert (Eq:Qabs (/q1) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq1. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (E3:Qabs(/q2) >0). 
      { assert (Eq:Qabs (/q2) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq2. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (Em1N': (m1 > N')%nat) by omega.
      assert (Em2N': (m2 > N')%nat) by omega.
      assert (E4:/Qabs (/ q1) <= /eps0).
      { apply (Qmult_le_l _ _ _ E2). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em1N' _ Hq1))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m1). auto. omega. auto. }
      assert (E5:/Qabs (/ q2) <= /eps0).
      { apply (Qmult_le_l _ _ _ E3). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em2N' _ Hq2))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m2). auto. omega. auto. }
      assert (E6:q1 - q2 == (/q2-/q1)/((/q1)*(/q2))).
      { unfold Qdiv. unfold Qminus. rewrite Qmult_plus_distr_l.
        rewrite Qinv_mult_distr. rewrite Qinv_involutive. rewrite Qinv_involutive. 
        rewrite (Qmult_comm (/q2)). rewrite <- Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E3)))).
        rewrite (Qmult_assoc). 
        assert (Etmp: - / q1 * q1 * q2 == - (/ q1 * q1 * q2)) by ring. 
        rewrite Etmp. rewrite (Qmult_comm (/q1)). 
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E2)))).
        ring. }
      assert (E7:eps == eps * eps0 * eps0 *  (/ eps0 * / eps0)).
      { rewrite Qmult_assoc.
        rewrite <- (Qmult_assoc _ eps0 (/eps0)). 
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r.
        rewrite <- Qmult_assoc. rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        ring. }
      assert (E8: Qabs ((/ q2 - / q1) / (/ q1 * / q2)) ==
       Qabs (/ q2 - / q1) * (/ Qabs (/ q1) / Qabs (/ q2))).
      { unfold Qdiv. rewrite Qabs_Qmult.
        rewrite Qabs_Qinv. rewrite Qabs_Qmult. rewrite Qmult_assoc.
        rewrite Qinv_mult_distr. rewrite Qmult_assoc. reflexivity. }
      rewrite E6. rewrite E7. rewrite E8.
      assert (E9: / Qabs (/ q1) / Qabs (/ q2) > 0). 
      { rewrite <- (Qmult_0_l (/ Qabs (/ q2))).
        apply (Qmult_lt_compat_r _ _ _ (Qinv_lt_0_compat _ E3) (Qinv_lt_0_compat _ E2)). }
      apply ( Qmult_lt_compat_trans_positive (
          Qabs (/ q2 - / q1))             (eps * eps0 * eps0)
          (/ Qabs (/ q1) / Qabs (/ q2))   (/ eps0 * / eps0)).
      apply Qabs_nonneg. apply E9.
      rewrite Qabs_Qminus. apply E1.
      unfold Qdiv. apply Qmult_le_compat_nonneg.
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q1))).
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q2))).
      auto. auto.    }
    { apply not_lt in En. apply not_lt in En'. exists N0.
      intros m1 m2 Hm1N Hm2N q1 q2 Hq1 Hq2.
      assert (E1:Qabs (/ q1 - / q2) < eps * eps0 * eps0). { apply (HN m1 m2). omega. omega. auto. auto.  }
      assert (E2:Qabs(/q1) >0). 
      { assert (Eq:Qabs (/q1) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq1. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (E3:Qabs(/q2) >0). 
      { assert (Eq:Qabs (/q2) >= 0) by (apply Qabs_nonneg). apply Qle_lteq in Eq. destruct Eq.
        - apply H2. - apply H0' in Hq2. symmetry in H2. apply Qabs_0 in H2. contradiction. omega. }
      assert (Em1N': (m1 > N')%nat) by omega.
      assert (Em2N': (m2 > N')%nat) by omega.
      assert (E4:/Qabs (/ q1) <= /eps0).
      { apply (Qmult_le_l _ _ _ E2). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em1N' _ Hq1))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m1). auto. auto. }
      assert (E5:/Qabs (/ q2) <= /eps0).
      { apply (Qmult_le_l _ _ _ E3). 
        rewrite (Qmult_inv_r _ (Qnot_0_abs _ (H0' _ Em2N' _ Hq2))).
        rewrite Qmult_comm.
        apply (Qmult_le_l _ _ _ Heps0). rewrite Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r. rewrite Qmult_1_l.
        apply (H' m2). auto. auto. }
      assert (E6:q1 - q2 == (/q2-/q1)/((/q1)*(/q2))).
      { unfold Qdiv. unfold Qminus. rewrite Qmult_plus_distr_l.
        rewrite Qinv_mult_distr. rewrite Qinv_involutive. rewrite Qinv_involutive. 
        rewrite (Qmult_comm (/q2)). rewrite <- Qmult_assoc.
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E3)))).
        rewrite (Qmult_assoc). 
        assert (Etmp: - / q1 * q1 * q2 == - (/ q1 * q1 * q2)) by ring. 
        rewrite Etmp. rewrite (Qmult_comm (/q1)). 
        rewrite (Qmult_inv_r _ (Qinv_not_0 _ (Qabs_not_0 _ (Qlt_not_0 _ E2)))).
        ring. }
      assert (E7:eps == eps * eps0 * eps0 *  (/ eps0 * / eps0)).
      { rewrite Qmult_assoc.
        rewrite <- (Qmult_assoc _ eps0 (/eps0)). 
        rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        rewrite Qmult_1_r.
        rewrite <- Qmult_assoc. rewrite (Qmult_inv_r _ (Qlt_not_0 _ Heps0)).
        ring. }
      assert (E8: Qabs ((/ q2 - / q1) / (/ q1 * / q2)) ==
       Qabs (/ q2 - / q1) * (/ Qabs (/ q1) / Qabs (/ q2))).
      { unfold Qdiv. rewrite Qabs_Qmult.
        rewrite Qabs_Qinv. rewrite Qabs_Qmult. rewrite Qmult_assoc.
        rewrite Qinv_mult_distr. rewrite Qmult_assoc. reflexivity. }
      rewrite E6. rewrite E7. rewrite E8.
      assert (E9: / Qabs (/ q1) / Qabs (/ q2) > 0). 
      { rewrite <- (Qmult_0_l (/ Qabs (/ q2))).
        apply (Qmult_lt_compat_r _ _ _ (Qinv_lt_0_compat _ E3) (Qinv_lt_0_compat _ E2)). }
      apply ( Qmult_lt_compat_trans_positive (
          Qabs (/ q2 - / q1))             (eps * eps0 * eps0)
          (/ Qabs (/ q1) / Qabs (/ q2))   (/ eps0 * / eps0)).
      apply Qabs_nonneg. apply E9.
      rewrite Qabs_Qminus. apply E1.
      unfold Qdiv. apply Qmult_le_compat_nonneg.
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q1))).
      apply (Qinv_le_0_compat _ (Qabs_nonneg (/ q2))).
      auto. auto. }
    }
Qed.

Lemma limit_not_0_spec: forall x: Real,
  (~ x == Rzero)%R <-> limit_not_0_real x.
Proof. intros. split.
- intros. hnf. unfold Real_equiv in H. destruct x as [A HA]. unfold Rzero in *.
  apply not_all_ex_not in H. destruct H as [q Hq]. apply imply_to_and in Hq.
  destruct Hq as [Hq H]. assert (E: forall n, ~(forall m, (m>n)%nat -> (forall q1 q2 : Q, A m q1 -> q2 == 0 -> Qabs (q1 - q2) < q))).
  { intros n. apply (not_ex_all_not _ _ H n). }
  exists (q*(1#2)). split. apply eps_divide_2_positive. auto.
  intros N. assert (E1: ~(forall m : nat,
     (m > N)%nat -> forall q1 q2 : Q, A m q1 -> q2 == 0 -> Qabs (q1 - q2) < q)). { apply E. }
  clear H. clear E. apply not_all_ex_not in E1. destruct E1 as [nN E1].
  exists nN. apply imply_to_and in E1. destruct E1 as [E1 E2].
  split. apply E1. apply (not_all_ex_not) in E2. destruct E2 as [q1 Hq1].
  apply not_all_ex_not in Hq1. destruct Hq1 as [q2 Hq1].
  apply imply_to_and in Hq1. destruct Hq1 as [Hq1 H].
  apply imply_to_and in H. destruct H as [Hq2 H].
  rewrite Hq2 in H. intros q0 Hq0. assert (E: q0==q1).
  { apply (Cauchy_unique _ HA nN). auto. auto. }
  assert (E2: Qabs q0 >= q). { apply Qnot_lt_le in H. 
    assert (Et:q1 - 0 == q1) by ring. rewrite Et in H. rewrite E. auto. }
  apply (Qlt_le_trans _ q). 
  { apply (Qplus_lt_l _ _ (-q*(1#2))).
    assert (Et1: q * (1 # 2) + - q * (1 # 2) == 0) by ring.
    assert (Et2: q + - q * (1 # 2) == q*(1#2)) by ring.
    rewrite Et1,Et2. apply eps_divide_2_positive. auto. }
  auto.
- intros. destruct x as [A HA]. hnf in *. intros C. hnf in *.
  destruct H as [eps0 [Heps0 H]]. apply C in Heps0.
  destruct Heps0 as [n Hn]. destruct (H n) as [nN [HnN Hn']].
  destruct (Cauchy_exists _ HA nN) as [qnN HqnN].
  assert (E1: eps0 < Qabs qnN) by auto.
  assert (E2: eps0 > Qabs (qnN - 0)). { apply (Hn nN). auto. auto. reflexivity. }
  assert (Et: qnN-0 == qnN) by ring. rewrite Et in E2.
  assert (Nonsense: Qabs qnN <Qabs qnN ). { apply (Qlt_trans _ eps0). auto. auto. }
  apply Qlt_irrefl in Nonsense.  contradiction.
Qed.


Definition Rinv (a: {a0: Real | (~ a0 == Rzero)%R }): Real :=
  match a with
  | exist _ (Real_intro a0 H) H0 =>
      Real_intro
        (fun (n : nat) (q : Q) => a0 n (/ q))
        (Cauchy_inv_nonzero a0 H (proj1 (limit_not_0_spec (Real_intro a0 H)) H0))
  end.

Notation "/ x" := (Rinv x) : Real_scope.

Definition Rdiv x y := Rmult x (Rinv y).

Infix "/" := Rdiv : R_scope.

Theorem take_max_N_3prop:
forall N1 N2 N3 (P Q R:nat->Prop),
 (forall n, (n>N1)%nat -> P n) -> (forall n ,(n>N2)%nat -> Q n) ->
 (forall n, (n>N3)%nat -> R n) ->
  exists N, forall n,(n>N)%nat -> P n /\  Q n /\ R n.
Proof. intros N1 N2 N3 P Q R H1 H2 H3.
  destruct (classic (N1>N2)%nat),(classic (N1>N3)%nat),(classic (N2>N3)%nat).
  - exists N1. intros. split.
    * auto.
    * split. ** apply H2. omega.
             ** apply H3. omega.
  - exists N1. intros. split.
    * auto.
    * split. ** apply H2. omega.
             ** apply H3. omega.
  - exists O. split.
    * omega.
    * split. ** omega.
             ** omega.
  - exists N3. intros. split.
    * apply H1. omega.
    * split. ** apply H2. omega.
             ** apply H3. omega.
  - exists N2. intros. split.
    * apply H1. omega.
    * split. ** apply H2. omega.
             ** apply H3. omega.
  - exists O. split.
    * intros. omega.
    * split. ** omega.
             ** omega.
  - exists N2. intros. split.
    * intros. apply H1. omega.
    * split. ** apply H2. omega.
             ** apply H3. omega.
  - exists N3. intros. split.
    * apply H1. omega.
    * split. ** apply H2. omega.
             ** apply H3. omega.
Qed.


Theorem Rinv_equiv: forall A B,
((match A with exist _ A HA => A end) == (match B with exist _ B HB => B end))%R ->
(Rinv A == Rinv B)%R.
Proof. intros [[A HA1] HA2]. intros [[B HB1] HB2]. intros H. hnf in *.
  apply limit_not_0_spec in HA2. apply limit_not_0_spec in HB2.
  intros eps Heps.
  destruct (Cauchy_nonzero_pre _ HA1 HA2) as [NA [Amin [HAmin HA3]]].
  destruct (Cauchy_nonzero_pre _ HB1 HB2) as [NB [Bmin [HBmin HB3]]].
  assert (Eeps: 0< eps*Amin*Bmin).
  { rewrite <- (Qmult_0_l (Amin * Bmin)).
    rewrite Qmult_assoc.
   apply Qmult_lt_r. auto. apply Qmult_lt_r. auto. auto. }
  destruct (H (eps*Amin*Bmin) Eeps) as [N HN]. clear H.
  destruct (take_max_N_3prop NA NB N
    (fun n => forall q : Q, A n q -> Amin <= Qabs q)
    (fun n => forall q : Q, B n q -> Bmin <= Qabs q)
    (fun m => forall q1 q2 : Q, A m q1 -> B m q2 -> Qabs (q1 - q2) < eps * Amin * Bmin)
    HA3 HB3 HN) as [N0 H].
  clear HA3 HB3 HN NA NB N.
  apply (limit_not_0_seq A HA1) in HA2. destruct HA2 as [NA HA3].
  apply (limit_not_0_seq B HB1) in HB2. destruct HB2 as [NB HB3].
  destruct (take_max_N_3prop NA NB N0 _ _ _ HA3 HB3 H) as [N1 H0].
  clear HA3 HB3 H NA NB N0.
  exists N1. intros.
  destruct (H0 _ H) as [E1 [E2 [E3 [E4 E5]]]]. clear H0.
  assert (P1: Qabs ((/q2) - (/q1)) < eps * Amin * Bmin). { rewrite Qabs_Qminus. auto. }
  assert (P2: q1 - q2 == (/q2 - /q1)*(q1)*q2).
  { field. split. apply Qinv_not_0. auto. apply Qinv_not_0. auto. }
  rewrite P2. rewrite <- Qmult_assoc. rewrite Qabs_Qmult.
  assert (P3: q1 * q2 == / (/q1 * /q2)). 
  { field. split. apply Qinv_not_0. auto. apply Qinv_not_0. auto. }
  rewrite P3. rewrite Qabs_Qinv.
  rewrite Qabs_Qmult. rewrite Qinv_mult_distr.
  assert (P4: / Qabs(/q1) <= /Amin).
  { apply (Qmult_le_r _ _ _ HAmin).
    assert (Pt: Qabs (/ q1)>0).
    { destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q1))).
    - auto. - symmetry in H0. apply Qabs_0 in H0. apply E1 in H1. contradiction. }
    apply (Qmult_le_l _ _ _ Pt).
    assert (Pt2: Qabs (/ q1) * (/ Amin * Amin) == Qabs(/q1)). 
    { field. intros C. rewrite C in HAmin. apply Qlt_irrefl in HAmin. auto. }
    assert (Pt3: Qabs (/ q1) * (/ Qabs (/ q1) * Amin) == Amin).
    { field. intros C. apply Qabs_0 in C. rewrite C in H1. apply E1 in H1.
      apply H1. reflexivity. }
    rewrite Pt2,Pt3. apply E3. auto. }
  assert (P5: / Qabs(/q2) <= /Bmin).
  { apply (Qmult_le_r _ _ _ HBmin).
    assert (Pt: Qabs (/ q2)>0).
    { destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q2))).
    - auto. - symmetry in H0. apply Qabs_0 in H0. apply E2 in H2. contradiction. }
    apply (Qmult_le_l _ _ _ Pt).
    assert (Pt2: Qabs (/ q2) * (/ Bmin * Bmin) == Qabs(/q2)). 
    { field. intros C. rewrite C in HBmin. apply Qlt_irrefl in HBmin. auto. }
    assert (Pt3: Qabs (/ q2) * (/ Qabs (/ q2) * Bmin) == Bmin).
    { field. intros C. apply Qabs_0 in C. rewrite C in H2. apply E2 in H2.
      apply H2. reflexivity. }
    rewrite Pt2,Pt3. apply E4. auto. }
  assert (P6: eps == (eps * Amin * Bmin) * (/Amin * /Bmin)).
  { field. split.
    - intros C. rewrite C in HBmin. apply Qlt_irrefl in HBmin. contradiction.
    - intros C. rewrite C in HAmin. apply Qlt_irrefl in HAmin. contradiction. }
  rewrite P6.
  apply (Qmult_lt_compat_trans_positive  (Qabs (/ q2 - / q1)) (eps * Amin * Bmin) ).
  - apply Qabs_nonneg.
  - rewrite <- (Qmult_0_r (/ (Qabs (/ q1)))).
    apply Qmult_lt_l.
    + apply Qinv_lt_0_compat.
      destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q1))).
      * auto. * symmetry in H0. apply Qabs_0 in H0. apply E1 in H1. contradiction.
    + apply Qinv_lt_0_compat.
      destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q2))).
      * auto. * symmetry in H0. apply Qabs_0 in H0. apply E2 in H2. contradiction.
  - auto.
  - apply Qmult_le_compat_nonneg.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat.
      destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q1))).
      * auto. * symmetry in H0. apply Qabs_0 in H0. apply E1 in H1. contradiction.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat.
      destruct ((proj1 (Qle_lteq _ _)) (Qabs_nonneg (/q2))).
      * auto. * symmetry in H0. apply Qabs_0 in H0. apply E2 in H2. contradiction.
    + auto. + auto.
Qed. 

Theorem Rmult_comm: forall A B,
  (A * B == B * A)%R.
Proof. intros [A HA] [B HB].
unfold Real_equiv. unfold Rmult.
unfold CauchySeqMult. intros eps Heps. exists O.
intros. destruct (Cauchy_exists _ HA m) as [qa Hqa].
destruct (Cauchy_exists _ HB m) as [qb Hqb].
assert (E1: q1 == qa * qb). { auto. }
assert (E2: q2 == qb * qa). { auto. }
rewrite E1,E2.
assert (E: qa * qb - qb * qa == 0) by ring.
rewrite E. apply Heps.
Qed.

Theorem Rmult_assoc: forall A B C,
  ( A * B * C == A * (B * C))%R.
Proof. intros [A HA] [B HB] [C HC]. hnf.
  unfold CauchySeqMult. intros eps Heps. exists O.
  intros. destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  destruct (Cauchy_exists _ HC m) as [qc Hqc].
  assert (E1: q1 == qa * qb * qc). 
  { apply H0. intros. rewrite (Cauchy_unique _ HA m q0 qa H2 Hqa).
    rewrite (Cauchy_unique _ HB m qb q3 Hqb H3).
    reflexivity. auto. }
  assert (E2: q2 == qa * (qb * qc)).
  { apply H1. auto. intros. rewrite (Cauchy_unique _ HB m q0 qb H2 Hqb).
    rewrite (Cauchy_unique _ HC m qc q3 Hqc H3). reflexivity. }
  assert (E: qa * qb * qc - qa * (qb * qc) == 0) by ring.
  rewrite E1,E2,E. apply Heps.
Qed.

Definition Rone:Real :=
 Real_intro (fun (n:nat) => (fun x => x == 1)) (Real_has_Q 1).


Notation " 1 " := Rone : Real_scope.

Theorem Rmult_1_r: forall A, (A * Rone == A)%R.
Proof. intros [A HA]. hnf. unfold CauchySeqMult.
  intros. exists O. intros.
  assert (E:q1 == q2). { rewrite <- (Qmult_1_r q2). apply H1. auto. reflexivity. }
  rewrite E. unfold Qminus. rewrite Qplus_opp_r. apply H.
Qed.


Theorem Rmult_inv_r: forall A:{A: Real | (~ A == Rzero)%R }, 
((match A with | exist _ A0 _ => A0 end) * (Rinv A) == Rone)%R.
Proof. intros [[A HA1] HA2]. hnf. apply limit_not_0_spec in HA2.
  apply (limit_not_0_seq _ HA1) in HA2. destruct HA2 as [N HA2].
  intros eps Heps. exists N. intros. unfold CauchySeqMult in H0.
  destruct (Cauchy_exists _ HA1 m) as [qm Hqm].
  assert (E: q1 == qm * /qm). { apply H0. apply Hqm. rewrite Qinv_involutive. apply Hqm. }
  rewrite Qmult_inv_r in E. rewrite H1,E. apply Heps.
  apply (HA2 m). auto. auto.
Qed.

Theorem Rmult_inv_r': forall (A: Real) (H: (~ A == Rzero)%R),
(A * (Rinv (exist _ A H)) == Rone)%R.
Proof. intros [A HA1] HA2. hnf. apply limit_not_0_spec in HA2.
  apply (limit_not_0_seq _ HA1) in HA2. destruct HA2 as [N HA2].
  intros eps Heps. exists N. intros. unfold CauchySeqMult in H0.
  destruct (Cauchy_exists _ HA1 m) as [qm Hqm].
  assert (E: q1 == qm * /qm). { apply H0. apply Hqm. rewrite Qinv_involutive. apply Hqm. }
  rewrite Qmult_inv_r in E. rewrite H1,E. apply Heps.
  apply (HA2 m). auto. auto.
Qed.



Theorem Rmult_plus_distr_r: forall A B C, (A*(B+C)==A*B+A*C)%R.
Proof. intros [A HA] [B HB] [C HC] eps Heps. hnf. unfold CauchySeqMult. unfold CauchySeqPlus.
  exists O. intros m Hm Q1 Q2 H1 H2.
  destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  destruct (Cauchy_exists _ HC m) as [qc Hqc].
  assert (E1: Q1 == qa * (qb + qc)).
  { apply H1. auto. intros. rewrite (Cauchy_unique _ HB m q1 qb H Hqb).
    rewrite (Cauchy_unique _ HC m qc q2 Hqc H0). reflexivity. }
  assert (E2: Q2 == qa * qb + qa * qc).
  { apply H2. intros. rewrite (Cauchy_unique _ HA m q1 qa H Hqa).
    rewrite (Cauchy_unique _ HB m q2 qb H0 Hqb). reflexivity.
    intros. rewrite (Cauchy_unique _ HA m q1 qa H Hqa).
    rewrite (Cauchy_unique _ HC m qc q2 Hqc H0). reflexivity. }
  assert (E: qa * (qb + qc) - (qa * qb + qa * qc) == 0) by ring.
  rewrite E1,E2,E. auto.
Qed.


Instance Rplus_comp : Proper (Real_equiv ==> Real_equiv ==> Real_equiv) Rplus.
Proof. hnf. intros. hnf. intros.
  apply Cauchy_Plus_equiv. auto. auto.
Qed.

Instance Ropp_comp : Proper (Real_equiv ==> Real_equiv) Ropp.
Proof. hnf. intros [A HA] [B HB] H. hnf in *. unfold Cauchy_opp in *. intros.
  destruct (H _ H0) as [N HN]. exists N. intros.
  destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E1: q1 == -qa) by auto.
  assert (E2: q2 == -qb) by auto.
  rewrite E1,E2. assert (E3: - qa - - qb == (qb - qa)) by ring.
  rewrite E3. rewrite Qabs_Qminus. apply (HN _ H1). auto. auto.
Qed.

Instance Rminus_comp : Proper (Real_equiv ==> Real_equiv ==> Real_equiv) Rminus.
Proof. hnf. intros. hnf. intros.
  apply Ropp_comp in H0. unfold Rminus.
  rewrite H,H0. reflexivity.
Qed.

Instance Rmult_comp : Proper (Real_equiv ==> Real_equiv ==> Real_equiv) Rmult.
Proof. hnf. intros. hnf. intros.
  apply Cauchy_Mult_equiv. auto. auto.
Qed.



Lemma Rplus_0_l : forall x, (0+x == x)%R.
Proof. intros. rewrite Rplus_comm. apply Rplus_Zero.
Qed.
Lemma Rplus_0_r : forall x, (x+0 == x)%R.
Proof. intros. apply Rplus_Zero.
Qed.
Theorem Ropp_involutive: forall x, (x == - - x)%R.
Proof. intros. destruct x as [A HA]. hnf in *.
  unfold Cauchy_opp. intros. exists O.
  intros. assert (E: q2 == - - q1).
    { apply H2. intros. rewrite (Cauchy_unique _ HA _ _ _ H1 H3). reflexivity. }
  rewrite E. assert (Et: q1 - - - q1 == 0) by ring.
  rewrite Et. apply H.
Qed.

Theorem Ropp_plus_distr: forall x y, (- (x + y) == - x + - y)%R.
Proof. intros. destruct x as [A HA], y as [B HB].
  hnf in *. unfold Cauchy_opp. unfold CauchySeqPlus.
  intros. exists O. intros.
  destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E1: q1 == - (qa + qb)).
  { apply H1. intros.
    rewrite (Cauchy_unique _ HA _ _ _ Hqa H3).
    rewrite (Cauchy_unique _ HB _ _ _ Hqb H4).
    reflexivity. }
  assert (E2: q2 == -qa + -qb).
  { apply H2. intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H3). reflexivity.
    intros. rewrite (Cauchy_unique _ HB _ _ _ Hqb H3). reflexivity. }
  assert (E3: q1 - q2 == 0).
  { rewrite E1. rewrite E2. ring. }
  rewrite E3. apply H.
Qed.


Lemma Rplus_inj_r (x y z: Real):
  (x + z == y + z)%R <-> (x == y)%R.
Proof. intros. split.
  - intros. assert (E: (x == x + 0)%R). { rewrite Rplus_0_r. reflexivity. }
    rewrite E. rewrite <- (Rplus_opp_r z). rewrite <- Rplus_assoc.
    rewrite H. rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
  - intros. rewrite H. reflexivity.
Qed.

Lemma Rplus_inj_l (x y z: Real):
  (z + x == z + y)%R <-> (x == y)%R.
Proof. intros. split.
  - intros. rewrite Rplus_comm in H. rewrite (Rplus_comm z y) in H.
    apply (proj1 (Rplus_inj_r x y z)). auto.
  - intros. rewrite H. reflexivity.
Qed.

Lemma Rmult_0_l : forall x , (0*x == 0)%R.
Proof. intros. destruct x. hnf.
  intros. exists O. intros. unfold CauchySeqMult in *.
  destruct (Cauchy_exists _ H m) as [qa Hqa].
  rewrite (H2 _ _ H3 Hqa). rewrite H3. assert (E: 0*qa-0==0) by ring.
  rewrite E. apply H0.
Qed.

Lemma Rmult_0_r : forall x , (x*0 == 0)%R.
Proof. intros. rewrite Rmult_comm. apply Rmult_0_l.
Qed.

Lemma Rmult_1_l : forall n, (1*n == n)%R.
Proof. intros. rewrite Rmult_comm. apply Rmult_1_r.
Qed.

Theorem Rmult_plus_distr_l : forall x y z, ((x+y)*z==(x*z)+(y*z))%R.
Proof. intros. rewrite Rmult_comm.
  rewrite Rmult_plus_distr_r. rewrite Rmult_comm. rewrite (Rmult_comm z y).
  reflexivity.
Qed.

Theorem Rmult_integral : forall x y, (x*y==0)%R -> (x==0)%R \/ (y==0)%R.
Proof. intros.
  destruct (classic (x==0)%R).
  - left. apply H0.
  - right. rewrite <- Rmult_1_l. rewrite <- (Rmult_inv_r' x H0).
    rewrite (Rmult_comm x). rewrite Rmult_assoc. rewrite H. rewrite Rmult_0_r.
    reflexivity.
Qed.

Theorem Rmult_integral_l : forall x y, ~ (x == 0)%R -> (x*y == 0)%R -> (y == 0)%R.
Proof. intros. apply Rmult_integral in H0. destruct H0.
  - contradiction.
  - auto.
Qed.


Lemma take_max_N_0423:
forall N1 N2 N3 (P:nat->nat->Prop) (Q R:nat->Prop),
 (forall n1 n2, (n1>N1)%nat -> (n2>N1)%nat -> P n1 n2) -> (forall n ,(n>N2)%nat -> Q n) ->
 (forall n, (n>N3)%nat -> R n) ->
  exists N, (forall n1 n2,(n1>N)%nat -> (n2>N)%nat -> P n1 n2) /\ (forall n, (n>N)%nat-> Q n /\ R n).
Proof. intros. destruct (classic (lt N1 N2)), (classic (lt N2 N3)), (classic (lt N1 N3)).
- exists N3. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
- omega. 
- exists N2. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
- exists N2. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
- exists N3. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
- exists N1. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
- omega.
- exists N1. split. intros. apply H. omega. omega.
  intros. split. apply H0. omega. apply H1. omega.
Qed.

Lemma Rmult_nonzero (x y:Real): ~(x==0)%R->~(y==0)%R->~(x*y==0)%R.
Proof.
  intros. intros C. apply Rmult_integral in C. destruct C.
  - contradiction.
  - contradiction.
Qed.


Lemma Rinv_mult_distr : forall p q (Hp:~(p==0)%R)(Hq:~(q==0)%R), 
 (/ (exist _ (p * q) (Rmult_nonzero _ _ Hp Hq)) == /(exist _ p Hp) * /(exist _ q Hq))%R.
Proof. intros. destruct p as [A HA]. destruct q as [B HB].
  hnf. unfold CauchySeqMult. intros. exists O.
  intros. destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E1: /q1 == qa * qb). { apply H1. auto. auto. }
  assert (E2: / q2 == qa * qb).
  { rewrite <- (Qinv_involutive qa). rewrite <- (Qinv_involutive qb).
    rewrite <- Qinv_mult_distr. 
    rewrite <- Qinv_involutive in Hqa.
    rewrite <- Qinv_involutive in Hqb.
    rewrite (H2 _ _ Hqa Hqb). reflexivity. }
  rewrite <- (Qinv_involutive q1), <- (Qinv_involutive q2).
  rewrite E1. rewrite E2.
  assert (Et: / (qa * qb) - / (qa * qb) == 0) by ring.
  rewrite Et. apply H.
Qed.



Theorem Rdiv_mult_l : forall x y (H:~(y == 0)%R), ((x * y)*/(exist _ y H) == x)%R.
Proof. intros. destruct x as [A HA], y as [B HB].
  hnf. intros. unfold CauchySeqMult.
  apply (limit_not_0_spec) in H. apply limit_not_0_seq in H.
  destruct H as [N HN].
  exists N.
  intros. destruct (Cauchy_exists _ HA m) as [qa Hqa].
  destruct (Cauchy_exists _ HB m) as [qb Hqb].
  assert (E: q1 == qa * qb * (/qb)). { apply H1.
  - intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H3).
    rewrite (Cauchy_unique _ HB _ _ _ Hqb H4).
    reflexivity.
  - intros. rewrite Qinv_involutive. apply Hqb. }
  rewrite E. rewrite <- Qmult_assoc. rewrite Qmult_inv_r.
  rewrite Qmult_1_r. rewrite (Cauchy_unique _ HA _ _ _ Hqa H2).
  assert (Et: q2 - q2 == 0) by ring. rewrite Et. apply H0.
  apply (HN m). auto. auto.
Qed.

Theorem Rmult_div_r : forall x y (H:~ (y == 0)%R) , (y*(x*/(exist _ y H)) == x)%R.
Proof. intros. rewrite Rmult_comm. rewrite Rmult_assoc.
  rewrite (Rmult_comm _ y). rewrite <- Rmult_assoc. apply Rdiv_mult_l.
Qed.

Lemma Rmult_inj_r_suff: forall x y z, (x == y)%R -> (x * z == y * z )%R.
Proof. intros. rewrite H. reflexivity.
Qed.

Lemma Rmult_inj_r (x y z: Real): (~ z == 0 -> (x * z == y * z <-> x == y))%R.
Proof. intros. split.
  - intros. apply (Rmult_inj_r_suff _ _ (/ (exist _ z H))) in H0.
    rewrite (Rdiv_mult_l x z) in H0. rewrite (Rdiv_mult_l y z) in H0. apply H0.
  - intros. apply Rmult_inj_r_suff. auto.
Qed.



Lemma Rmult_inj_l (x y z: Real): (~ z == 0 -> (z * x == z * y <-> x == y))%R.
Proof. intros. split.
  - intros. apply (Rmult_inj_r _ _ z). apply H. rewrite Rmult_comm. rewrite (Rmult_comm y z).
    apply H0.
  - intros. rewrite H0. reflexivity.
Qed.


Lemma Rinv_nonzero (x:Real)(H:~(x==0)%R): ~(Rinv (exist _ x H) == 0)%R.
Proof. destruct x as [A HA].
  apply limit_not_0_spec. hnf.
  assert (H1: limit_not_0_real (Real_intro A HA)). { apply limit_not_0_spec. auto. }
  destruct (CauchySeqBounded _ HA) as [M [HM H2]].
  apply limit_not_0_seq in H1. destruct H1 as [N HN].
  exists (/M). split.
  - apply Qinv_lt_0_compat. auto.
  - intros. destruct (classic (N0 < N)%nat).
    + exists (S N). split. omega. intros. apply (Qmult_lt_l _ _ _ HM).
      rewrite Qmult_inv_r. apply (Qmult_lt_r _ _ (/ (Qabs q))).
      rewrite <- Qabs_Qinv. apply Qnot_0_abs_pos. apply (HN (S N)). omega. auto.
      rewrite Qmult_1_l. rewrite <- Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_r. rewrite <- Qabs_Qinv. apply (H2 (S N)). auto.
      apply Qnot_0_abs. intros C. assert (foo: ~ / q == 0). { apply (HN (S N)). auto. auto. }
      rewrite C in foo. apply foo. reflexivity. intros C. rewrite C in HM.
      apply Qlt_irrefl in HM. auto.
    + exists (S N0). split. omega. intros. apply (Qmult_lt_l _ _ _ HM).
      rewrite Qmult_inv_r. apply (Qmult_lt_r _ _ (/ (Qabs q))).
      rewrite <- Qabs_Qinv. apply Qnot_0_abs_pos. apply (HN (S N0)). omega. auto.
      rewrite Qmult_1_l. rewrite <- Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_r. rewrite <- Qabs_Qinv. apply (H2 (S N0)). auto.
      apply Qnot_0_abs. intros C. assert (foo: ~ / q == 0). { apply (HN (S N0)). omega. auto. }
      rewrite C in foo. apply foo. reflexivity. intros C. rewrite C in HM.
      apply Qlt_irrefl in HM. auto.
Qed.
Lemma Rinv_involutive (x:Real)(H:~(x==0)%R):
 (/ (exist _ (Rinv (exist _ x H)) (Rinv_nonzero _ H)) == x)%R.
Proof. destruct x as [A HA]. hnf.
  intros. exists O. intros. rewrite <- (Cauchy_unique _ HA _ _ _ H2 H3).
  rewrite Qinv_involutive. assert(E:q1 - q1==0) by ring.
  rewrite E. apply H0.
Qed.



Lemma inject_Q_plus (x y: Q): (inject_Q (x + y) == inject_Q x + inject_Q y)%R.
Proof. hnf. intros. exists O.
  intros. unfold CauchySeqPlus in *. rewrite (H2 x y). rewrite H1.
  assert (E:x + y - (x + y) == 0) by ring. rewrite E. apply H. reflexivity. reflexivity.
Qed.

Lemma inject_Q_mult (x y: Q): (inject_Q (x * y) == inject_Q x * inject_Q y)%R.
Proof. hnf. intros. exists O.
  intros. unfold CauchySeqMult in *. rewrite (H2 x y). rewrite H1.
  assert (E:x * y - (x * y) == 0) by ring. rewrite E. apply H. reflexivity. reflexivity.
Qed.
Lemma inject_Q_opp (x: Q): (inject_Q (- x) == - inject_Q x)%R.
Proof. hnf. intros. exists O.
  intros. unfold Cauchy_opp in *. rewrite (H2 x). rewrite H1.
  assert (E:- x - - x == 0) by ring. rewrite E. apply H. reflexivity.
Qed.


Instance inject_Q_comp: Proper (Qeq ==>Real_equiv) inject_Q.
Proof. hnf. intros.
  hnf. intros.
  exists O.
  intros.
  rewrite H2,H3.
  rewrite H.
  assert (Et: y-y==0)by ring.
  rewrite Et.
  apply H0.
Qed.


Lemma inject_Q_nonzero: forall q, ~ q == 0 -> ~ (inject_Q q == 0)%R.
Proof. intros. intros C.
  hnf in C.
  pose proof (C (Qabs q) (Qnot_0_abs_pos q H)).
  destruct H0.
  assert (S x>x)%nat by omega.
  pose proof (H0 (S x) H1).
  assert (Qabs q > Qabs (q -0)).
  { apply H2. reflexivity. reflexivity. }
  assert (q-0==q) by ring. rewrite H4 in H3.
  apply Qlt_irrefl in H3.
  auto.
Qed.


Lemma inject_Q_inv: forall q (H:~q==0) , (inject_Q (/q) == 
    / exist (fun a0 : Real => ~ a0 == 0) (inject_Q q) (inject_Q_nonzero _ H))%R.
Proof. intros.
  hnf.
  intros.
  exists O.
  intros.
  rewrite H2.
  assert (Et: q2 == /q). { rewrite <- H3. rewrite Qinv_involutive. reflexivity. }
  rewrite Et.
  assert (Et':  (/ q - / q) == 0) by ring.
  rewrite Et'.
  apply H0.
Qed.




Theorem inject_Q_eq_inv: forall (q1 q2:Q), (inject_Q q1 == inject_Q q2)%R -> q1 == q2.
Proof. intros. hnf in H.
  destruct (classic (q1 == q2)). auto.
  assert (E:~(q1-q2==0)).
  { intros C. apply H0. rewrite <- (Qplus_0_r q2). rewrite <- C. ring. }
  apply Qnot_0_abs_pos in E. apply H in E.
  destruct E. assert (foo: Qabs (q1 - q2) < Qabs (q1 - q2)).
  { apply (H1 (S x)). omega. reflexivity. reflexivity. }
  apply Qlt_irrefl in foo. destruct foo.
Qed.



Definition Rsrt : (ring_theory 0 1 Rplus Rmult Rminus Ropp Real_equiv)%R.
Proof.
  constructor.
  - exact Rplus_0_l.
  - exact Rplus_comm.
  - intros. rewrite Rplus_assoc. reflexivity.
  - exact Rmult_1_l.
  - exact Rmult_comm.
  - intros. rewrite Rmult_assoc. reflexivity.
  - exact Rmult_plus_distr_l.
  - reflexivity.
  - exact Rplus_opp_r.
Qed.

Add Ring Rring :Rsrt.


