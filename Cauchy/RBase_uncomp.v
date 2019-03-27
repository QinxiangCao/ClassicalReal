From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From CReal Require Import QArith_ext.QArith_base_ext.
From Coq Require Import Classes.Morphisms.

Lemma eps_divide_2M_positive: forall (eps M:Q), 0 < eps -> 0 < M -> eps * (1 # 2) *(/M) > 0.
Proof. intros.
  apply (Qmult_lt_r _ _ _ H0). rewrite Qmult_0_l.
  rewrite <- (Qmult_assoc (eps * (1 # 2))). rewrite (Qmult_comm _ M). rewrite Qmult_inv_r.
  rewrite Qmult_1_r. apply eps_divide_2_positive. apply H.
  intros contra. rewrite contra in H0. discriminate.
Qed.


Record Cauchy (CSeq : nat -> Q -> Prop) : Prop := {
  Cauchy_exists : forall (n:nat), exists (q:Q), (CSeq n q);
  Cauchy_unique : forall (n:nat) (q1 q2:Q),
      CSeq n q1 -> CSeq n q2 -> q1 == q2;
  Cauchy_refl : forall (n:nat) (q1 q2:Q),
      q1 == q2 -> ((CSeq n q1) <-> (CSeq n q2));
  Cauchy_def : forall (eps:Q), eps > 0 -> (exists (n:nat),
     forall (m1 m2:nat), (m1 > n)%nat -> (m2 > n)%nat
     -> forall (q1 q2:Q), CSeq m1 q1 -> CSeq m2 q2 ->
          Qabs (q1 - q2) < eps);
}.

Inductive Real : Type :=
| Real_intro (CSeq : nat -> Q -> Prop) (H: Cauchy CSeq).

Definition Real_equiv (x1 x2 : Real) : Prop :=
  match x1, x2 with
  | Real_intro CSeq1 H1,
    Real_intro CSeq2 H2 =>
      forall (eps:Q), eps>0 -> (exists (n:nat),
      forall (m:nat), (m > n)%nat -> 
        forall (q1 q2:Q), CSeq1 m q1 -> CSeq2 m q2 ->
          Qabs (q1 - q2) < eps)
  end.


Theorem Real_def_refl: reflexive Real Real_equiv.
Proof. unfold reflexive. intros. unfold Real_equiv.
  destruct x as [x H1]. intros.
  exists O. intros. apply (Cauchy_unique _ H1 m q1 q2 H2) in H3.
  assert (H': q1 - q2 == 0). { rewrite H3. ring. }
  rewrite H'. apply H.
Qed.

Theorem Real_def_symm: symmetric Real Real_equiv.
Proof. unfold symmetric. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy].
  intros. apply H in H0. destruct H0. exists x0. intros.
  rewrite Qabs_Qminus. apply (H0 m).
  apply H1. apply H3. apply H2. 
Qed.

Theorem Real_def_trans: transitive Real Real_equiv.
Proof. unfold transitive. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy], z as [z Hz]. intros.
  assert (Heps: eps == eps *(1#2) + eps *(1#2)) by ring.
  destruct (H _ (eps_divide_2_positive eps H1)) as [n1 Hab].
  destruct (H0 _ (eps_divide_2_positive eps H1)) as [n2 Hbc].
  clear H. clear H0.
  assert (H: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct H.

- exists n2. intros m H0 q1 q3. assert (H': (m > n1)%nat). { omega. }
  intros Hxq Hzq. destruct (Cauchy_exists _ Hy m) as [q2 Hyq].
  apply (Hab _ H' q1 q2) in Hxq.
  apply (Hbc _ H0 q2 q3) in Hyq.
  apply Qlt_le_weak in Hyq.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ Hxq Hyq).
  apply Hzq. apply Hyq.


- exists n1. apply not_le in H. intros m H0 q1 q3. assert (H': (m > n2)%nat). { omega. }
  intros Hxq Hzq. destruct (Cauchy_exists _ Hy m) as [q2 Hyq].
  apply (Hab _ H0 q1 q2) in Hxq.
  apply (Hbc _ H' q2 q3) in Hyq.
  apply Qlt_le_weak in Hyq.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ Hxq Hyq).
  apply Hzq. apply Hyq.
Qed.


Instance Real_equiv_holds: Equivalence Real_equiv.
Proof. split.
- apply Real_def_refl.
- apply Real_def_symm.
- apply Real_def_trans.
Qed.


(* We show that a constant sequence of Q is Real *)

Theorem Real_has_Q: forall (x1:Q) , Cauchy (fun (n:nat) => (fun x => x == x1)).
Proof. intros. split.
  - intros. exists x1. reflexivity.
  - intros. rewrite H. rewrite H0. reflexivity.
  - intros. split. intros. rewrite <- H. apply H0.
    intros. rewrite H. apply H0.
  - intros. exists O. intros. rewrite H2,H3. unfold Qminus. Search Qabs.
    rewrite Qplus_opp_r. apply H.
Qed.

Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_scope with R.

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
- unfold CauchySeqPlus. intros n q1 q2 H. split.
  + intros H'. intros qa qb Hqa Hqb. rewrite <- H. apply H'. auto. auto.
  + intros H'. intros qa qb Hqa Hqb. rewrite H. auto.
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

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqPlus A B) (Cauchy_Plus_Cauchy A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B) (at level 50,left associativity):Real_scope.

Definition Rzero:Real :=
 Real_intro (fun (n:nat) => (fun x => x == 0)) (Real_has_Q 0).


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
  - intros. split.
    + intros. rewrite <- H0. apply H1. apply H2.
    + intros. rewrite H0. apply H1. apply H2.
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
- intros n q1 q2 E. split.
  + intros H qa qb Hqa Hqb. rewrite <- E. auto.
  + intros H qa qb Hqa Hqb. rewrite E. auto.
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

Notation "a * b":=(Rmult a b):Real_scope.

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


Definition Cauchy_inv (A : nat -> Q -> Prop): (nat -> Q -> Prop) :=
    fun (n:nat) (q:Q) =>
     forall (q1:Q), (A n q1) -> q == /q1.

Lemma Cauchy_nonzero: forall A (eps:Q), Cauchy A -> eps > 0 ->
  (exists (N:nat), forall (n:nat)(q:Q), (n > N)%nat
     -> A n q -> Qabs q < eps) -> exists (eps0:Q), 
  eps0 > 0 /\ (forall (n:nat)(q:Q), A n q -> Qabs q >= eps0).
Proof. intros A eps HA H [N1 Hlim].
  apply (Cauchy_def _ HA) in H. destruct H as [N2 HN].
Admitted.
  


Theorem Cauchy_inv_Cauchy: forall A, Cauchy A 
  -> Cauchy (Cauchy_inv A).
Proof. intros. unfold Cauchy_inv. split.
  - intros. destruct (Cauchy_exists _ H n) as [q Hq]. exists (/ q).
    intros. rewrite (Cauchy_unique _ H n q q1 Hq H0). reflexivity.
  - intros n q1 q2 H1 H2. destruct (Cauchy_exists _ H n) as [q Hq].
    assert (E1: q1 == / q) by (apply (H1 q Hq)).
    assert (E2: q2 == / q) by (apply (H2 q Hq)).
    rewrite E1,E2. reflexivity.
  - intros. split.
    + intros. rewrite <- H0. apply H1. apply H2.
    + intros. rewrite H0. apply H1. apply H2.
  - intros. apply (Cauchy_def _ H) in H0. destruct H0 as [n H0].
    exists n. intros. 
    destruct (Cauchy_exists _ H m1) as [qa Hqa], (Cauchy_exists _ H m2) as [qb Hqb].
    rewrite (H3 qa Hqa). rewrite (H4 qb Hqb).

Admitted.

Fixpoint Rinv(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (Cauchy_inv A) (Cauchy_inv_Cauchy A HA) 
  end.




