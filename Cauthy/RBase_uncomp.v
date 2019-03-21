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


Record Cauchy (CSeq : nat -> Q -> Prop) : Prop := {
  Cauchy_exists : forall (n:nat), exists (q:Q), (CSeq n q);
  Cauchy_unique : forall (n:nat) (q1 q2:Q),
      (CSeq n q1)/\(CSeq n q2) -> q1 == q2;
  Cauchy_refl : forall (n:nat) (q1 q2:Q),
      q1 == q2 -> ((CSeq n q1) <-> (CSeq n q2));
  Cauchy_def : forall (eps:Q), eps > 0 -> (exists (n:nat),
     forall (m1 m2:nat), (m1 > n)%nat /\ (m2 > n)%nat
     -> forall (q1 q2:Q), (CSeq m1 q1) /\ (CSeq m2 q2) ->
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
        forall (q1 q2:Q), (CSeq1 m q1) /\ (CSeq2 m q2) ->
          Qabs (q1 - q2) < eps)
  end.



Theorem Real_def_refl: reflexive Real Real_equiv.
Proof. unfold reflexive. intros. unfold Real_equiv.
  destruct x as [x H1]. inversion H1. intros.
  exists O. intros. apply Cauchy_unique0 in H2.
  assert (H': q1 - q2 == 0). { rewrite H2. ring. }
  rewrite H'. apply H.
Qed.

Theorem Real_def_symm: symmetric Real Real_equiv.
Proof. unfold symmetric. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy]. inversion Hx. inversion Hy.
  intros. apply H in H0. destruct H0. exists x0. intros.
  apply and_comm in H2. rewrite Qabs_Qminus. apply (H0 m).
  apply H1. apply H2. 
Qed.

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

Theorem Real_def_trans: transitive Real Real_equiv.
Proof. unfold transitive. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy], z as [z Hz]. intros.
  assert (Heps: eps == eps *(1#2) + eps *(1#2)) by ring.
  destruct (H _ (eps_divide_2_positive eps H1)) as [n1 Hab].
  destruct (H0 _ (eps_divide_2_positive eps H1)) as [n2 Hbc].
  clear H. clear H0.
  assert (H: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct H.

- exists n2. intros m H0 q1 q3. assert (H': (m > n1)%nat). { omega. }
  intros [Hxq Hzq]. inversion Hy. destruct (Cauchy_exists0 m) as [q2 Hyq].
  assert (E1: x m q1 /\ y m q2) by auto.
  assert (E2: y m q2 /\ z m q3) by auto.
  apply (Hab _ H') in E1.
  apply (Hbc _ H0) in E2.
  apply Qlt_le_weak in E2.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ E1 E2).


- exists n1. apply not_le in H. intros m H0 q1 q3. assert (H': (m > n2)%nat). { omega. }
  intros [Hxq Hzq]. inversion Hy. destruct (Cauchy_exists0 m) as [q2 Hyq].
  assert (E1: x m q1 /\ y m q2) by auto.
  assert (E2: y m q2 /\ z m q3) by auto.
  apply (Hab _ H0) in E1.
  apply (Hbc _ H') in E2.
  apply Qlt_le_weak in E2.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ E1 E2).

Qed.


Theorem Real_equiv_holds: Equivalence Real_equiv.
Proof. split.
- apply Real_def_refl.
- apply Real_def_symm.
- apply Real_def_trans.
Qed.


(* We show that a constant sequence of Q is Real *)

Theorem Real_has_Q: forall (x1:Q) , Cauchy (fun (n:nat) => (fun x => x == x1)).
Proof. intros. split.
  - intros. exists x1. reflexivity.
  - intros. destruct H. rewrite H. rewrite H0. reflexivity.
  - intros. split. intros. rewrite <- H. apply H0.
    intros. rewrite H. apply H0.
  - intros. exists O. intros. destruct H1. rewrite H1,H2. unfold Qminus. Search Qabs.
    rewrite Qplus_opp_r. apply H.
Qed.

Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_scope with R.

(*Next, define the plus operation *)
Definition CauchySeqPlus (A B: nat -> Q -> Prop): (nat -> Q -> Prop) :=
  fun (n:nat) (q:Q) =>
     forall (q1 q2:Q), (A n q1) /\ (B n q2) -> q == q1 + q2.


Theorem Cauchy_Plus_Cauchy: forall A B, Cauchy A -> Cauchy B
  -> Cauchy (CauchySeqPlus A B).
Proof. intros A B HA HB. split.
- inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  unfold CauchySeqPlus. intros. destruct (CA1 n) as [qa Hqa].
  destruct (CB1 n) as [qb Hqb].
  exists (qa + qb). intros. destruct H as [HqA HqB].
  assert (E1:qa == q1). { apply (CA2 n qa q1). split. apply Hqa. apply HqA. }
  assert (E2:qb == q2). { apply (CB2 n qb q2). split. apply Hqb. apply HqB. }
  rewrite E1. rewrite E2. reflexivity.
- inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  unfold CauchySeqPlus. intros n q1 q2 [H1 H2].
  destruct (CA1 n) as [qa Hqa]. destruct (CB1 n) as [qb Hqb].
  assert (E1: q1 == qa + qb). { auto. }
  assert (E2: q2 == qa + qb). { auto. }
  rewrite E1. rewrite E2. reflexivity.
- inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  unfold CauchySeqPlus. intros n q1 q2 H. split.
  + intros H'. intros qa qb [Hqa Hqb]. rewrite <- H. apply H'. auto.
  + intros H'. intros qa qb [Hqa Hqb]. rewrite H. auto.
- inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  unfold CauchySeqPlus. intros eps Heps.
  destruct (CA4 _ (eps_divide_2_positive eps Heps)) as [n1 HAC].
  destruct (CB4 _ (eps_divide_2_positive eps Heps)) as [n2 HBC].
  clear CA4. clear CB4.
  assert (H2: eps == eps *(1#2) + eps *(1#2)) by ring.

assert (Hn: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct Hn.
  * exists n2. intros m1 m2 Hm2 q1 q2 [Hq1 Hq2].
    assert (Hm1: (m1 > n1 /\ m2 > n1)%nat). { omega. }
    destruct (CA1 m1) as [qa1 Hqa1], (CA1 m2) as [qa2 Hqa2].
    destruct (CB1 m1) as [qb1 Hqb1], (CB1 m2) as [qb2 Hqb2].
    assert (E1: q1 == qa1 + qb1) by auto.
    assert (E2: q2 == qa2 + qb2) by auto.
    assert (Et: q1 - q2 == (qa1 - qa2) + (qb1 - qb2)). { rewrite E1,E2. ring. }
    rewrite Et. rewrite H2.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    assert (E3: A m1 qa1 /\ A m2 qa2) by auto.
    assert (E4: B m1 qb1 /\ B m2 qb2) by auto.
    apply (HAC _ _ Hm1 qa1 qa2) in E3.
    apply (HBC _ _ Hm2 qb1 qb2) in E4. apply Qlt_le_weak in E4.
    apply (Qplus_lt_le_compat _ _ _ _ E3 E4).
  * exists n1. apply not_le in H. intros m1 m2 Hm1 q1 q2 [Hq1 Hq2].
    assert (Hm2: (m1 > n2 /\ m2 > n2)%nat). { omega. }
    destruct (CA1 m1) as [qa1 Hqa1], (CA1 m2) as [qa2 Hqa2].
    destruct (CB1 m1) as [qb1 Hqb1], (CB1 m2) as [qb2 Hqb2].
    assert (E1: q1 == qa1 + qb1) by auto.
    assert (E2: q2 == qa2 + qb2) by auto.
    assert (Et: q1 - q2 == (qa1 - qa2) + (qb1 - qb2)). { rewrite E1,E2. ring. }
    rewrite Et. rewrite H2.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    assert (E3: A m1 qa1 /\ A m2 qa2) by auto.
    assert (E4: B m1 qb1 /\ B m2 qb2) by auto.
    apply (HAC _ _ Hm1 qa1 qa2) in E3.
    apply (HBC _ _ Hm2 qb1 qb2) in E4. apply Qlt_le_weak in E4.
    apply (Qplus_lt_le_compat _ _ _ _ E3 E4).
Qed.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqPlus A B) (Cauchy_Plus_Cauchy A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B) (at level 50,left associativity).

Definition Rzero:Real :=
 Real_intro (fun (n:nat) => (fun x => x == 0)) (Real_has_Q 0).


Theorem Cauthy_Plus_equiv: forall (A1 A2 B1 B2: Real),
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
    unfold CauchySeqPlus. intros q1 q2 [H1 H2].
    inversion Ha1 as [Ca1exists _ _ _]. destruct (Ca1exists m) as [qa1 Hqa1].
    inversion Ha2 as [Ca2exists _ _ _]. destruct (Ca2exists m) as [qa2 Hqa2].
    inversion Hb1 as [Cb1exists _ _ _]. destruct (Cb1exists m) as [qb1 Hqb1].
    inversion Hb2 as [Cb2exists _ _ _]. destruct (Cb2exists m) as [qb2 Hqb2].
    assert (E1: a1 m qa1 /\ b1 m qb1) by auto.
    assert (E2: a2 m qa2 /\ b2 m qb2) by auto.
    apply H1 in E1. apply H2 in E2.
    rewrite E1,E2. assert (H': qa1 + qb1 - (qa2 + qb2) == qa1 - qa2 + (qb1 - qb2)) by ring.
    rewrite H'. rewrite Heps'.
    assert (E3: a1 m qa1 /\ a2 m qa2) by auto.
    assert (E4: b1 m qb1 /\ b2 m qb2) by auto.
    apply (Heqa m Hn1) in E3. apply (Heqb m Hn2) in E4. apply Qlt_le_weak in E4.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply (Qplus_lt_le_compat _ _ _ _ E3 E4).
  * exists n1. intros m Hn1. assert (Hn2: (m > n2)%nat) by omega.
    unfold CauchySeqPlus. intros q1 q2 [H1 H2].
    inversion Ha1 as [Ca1exists _ _ _]. destruct (Ca1exists m) as [qa1 Hqa1].
    inversion Ha2 as [Ca2exists _ _ _]. destruct (Ca2exists m) as [qa2 Hqa2].
    inversion Hb1 as [Cb1exists _ _ _]. destruct (Cb1exists m) as [qb1 Hqb1].
    inversion Hb2 as [Cb2exists _ _ _]. destruct (Cb2exists m) as [qb2 Hqb2].
    assert (E1: a1 m qa1 /\ b1 m qb1) by auto.
    assert (E2: a2 m qa2 /\ b2 m qb2) by auto.
    apply H1 in E1. apply H2 in E2.
    rewrite E1,E2. assert (H': qa1 + qb1 - (qa2 + qb2) == qa1 - qa2 + (qb1 - qb2)) by ring.
    rewrite H'. rewrite Heps'.
    assert (E3: a1 m qa1 /\ a2 m qa2) by auto.
    assert (E4: b1 m qb1 /\ b2 m qb2) by auto.
    apply (Heqa m Hn1) in E3. apply (Heqb m Hn2) in E4. apply Qlt_le_weak in E4.
    apply (Qle_lt_trans _ _ _ (Qabs_triangle (qa1 - qa2) (qb1 - qb2))).
    apply (Qplus_lt_le_compat _ _ _ _ E3 E4).
Qed.


Theorem Rplus_comm : forall (A B: Real),
  (A + B == B + A)%R.
Proof. intros. unfold Real_equiv. destruct A as [A HA], B as [B HB].
  unfold Rplus. intros eps Heps. exists O. intros m Hm q1 q2 [H1 H2].
  unfold CauchySeqPlus in *.
  inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  destruct (CA1 m) as [qa Hqa]. destruct (CB1 m) as [qb Hqb].
  assert (E1: q1 == qa + qb). { apply H1. split. apply Hqa. apply Hqb. }
  assert (E2: q2 == qb + qa). { apply H2. split. apply Hqb. apply Hqa. }
  rewrite E1. rewrite E2. assert (E:qa + qb - (qb + qa) == 0) by ring.
  rewrite E. apply Heps.
Qed.

Theorem Rplus_assoc: forall (A B C: Real),
  (A + B + C == A + (B + C))%R.
Proof. intros. unfold Real_equiv. destruct A as [A HA], B as [B HB], C as [C HC].
  unfold Rplus. intros eps Heps. exists O. intros m Hm q1 q2 [H1 H2].
  unfold CauchySeqPlus in *.
  inversion HA as [CA1 CA2 CA3 CA4]. inversion HB as [CB1 CB2 CB3 CB4].
  inversion HC as [CC1 CC2 CC3 CC4]. destruct (CA1 m) as [qa Hqa].
  destruct (CB1 m) as [qb Hqb]. destruct (CC1 m) as [qc Hqc].
  assert (E1: q1 == qa + qb + qc). {
    apply (H1 (qa+qb)%Q qc). split. intros qa' qb' [Hqa' Hqb'].
      assert (Ea':qa' == qa). { apply (CA2 m). split. apply Hqa'. apply Hqa. }
      assert (Eb':qb' == qb). { apply (CB2 m). split. apply Hqb'. apply Hqb. }
    rewrite Ea',Eb'. reflexivity. apply Hqc. }
  assert (E2: q2 == qa + (qb + qc)). {
    apply (H2 qa (qb+qc)%Q). split. apply Hqa. intros qb' qc' [Hqb' Hqc'].
      assert (Ec':qc' == qc). { apply (CC2 m). split. apply Hqc'. apply Hqc. }
      assert (Eb':qb' == qb). { apply (CB2 m). split. apply Hqb'. apply Hqb. }
    rewrite Ec',Eb'. reflexivity. }
  rewrite E1,E2. rewrite Qplus_assoc. unfold Qminus. rewrite Qplus_opp_r.
  apply Heps.
Qed.

Theorem Rplus_Zero: forall (A : Real),
  (A + Rzero == A)%R.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros eps Heps. unfold CauchySeqPlus.
  exists O. intros m Hm q1 q2 [H1 H2].
  assert (E:A m q2 /\ 0 == 0). split. apply H2. reflexivity.
  apply H1 in E. rewrite E. rewrite Qplus_0_r. unfold Qminus.
  rewrite Qplus_opp_r. apply Heps.
Qed.


Definition Cauchy_opp (A : nat -> Q -> Prop): (nat -> Q -> Prop) :=
    fun (n:nat) (q:Q) =>
     forall (q1:Q), (A n q1) -> q == - q1.


Theorem Cauchy_opp_Cauchy: forall A, Cauchy A 
  -> Cauchy (Cauchy_opp A).
Proof. intros. unfold Cauchy_opp. inversion H as [C1 C2 C3 C4]. split.
  - intros. destruct (C1 n) as [q Hq]. exists (- q).
    intros. assert (H': A n q /\ A n q1) by auto.
    apply C2 in H'. rewrite H'. reflexivity.
  - intros n q1 q2 [H1 H2]. destruct (C1 n) as [q Hq].
    assert (E1: q1 == - q) by (apply (H1 q Hq)).
    assert (E2: q2 == - q) by (apply (H2 q Hq)).
    rewrite E1,E2. reflexivity.
  - intros. split.
    + intros. rewrite <- H0. apply H1. apply H2.
    + intros. rewrite H0. apply H1. apply H2.
  - intros. apply C4 in H0. destruct H0 as [n H0].
    exists n. intros.
    destruct (C1 m1) as [qa Hqa], (C1 m2) as [qb Hqb].
    assert (E: A m1 qa /\ A m2 qb). { auto. }
    apply (H0 _ _ H1) in E. destruct H2.
    apply H2 in Hqa. apply H3 in Hqb.
    rewrite Hqa,Hqb. assert (Eq: - qa - - qb == qb - qa) by ring.
    rewrite Eq. rewrite Qabs_Qminus. apply E.
Qed.

Fixpoint Ropp(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (Cauchy_opp A) (Cauchy_opp_Cauchy A HA) 
  end.

Theorem Rplus_opp_r : forall (A:Real), Real_equiv (A + (Ropp A))  Rzero.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros eps Heps. exists O. unfold Cauchy_opp. unfold CauchySeqPlus.
  intros m Hm q1 q2 [H1 H2]. inversion Ha.
  destruct (Cauchy_exists0 m) as [qa Hqa].
  assert (q1 == qa + (- qa)). { apply H1. split. apply Hqa. intros.
    assert (E: qa == q0). { apply (Cauchy_unique0 m). auto. }
    rewrite E. reflexivity. }
  rewrite H. rewrite Qplus_opp_r. rewrite H2. apply Heps.
Qed. 
