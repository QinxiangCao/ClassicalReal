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
From CReal.Cauchy Require Import RBase.


Definition Rpositive (A:Real):Prop:=
  exists eps0:Q, (eps0>0) /\ 
    (exists N, forall n, (n>=N)%nat -> 
      forall q, (match A with | Real_intro A0 _ => A0 end) n q -> q >= eps0).

Theorem Rpositive_equiv: forall A B,
  (A == B)%R -> Rpositive A -> Rpositive B.
Proof. intros [A HA] [B HB] H0 H1. hnf in *.
  destruct H1 as [eps0 [H H1]]. exists (eps0 *(1#2)). split.
  apply eps_divide_2_positive. auto.
  destruct H1 as [N1 H1].
  destruct (H0 _ (eps_divide_2_positive _ H)) as [N2 H2].
  assert (HN: lt N1 N2 \/ ~(lt N1 N2)) by (apply classic). destruct HN as [HN|HN].
  - exists (S N2). intros n HN2. assert (HN1:(n >= N1)%nat) by omega.
    intros qb Hqb. destruct (Cauchy_exists _ HA n) as [qa Hqa].
    assert (E1: qb == qa - (qa - qb)) by ring.
    assert (E2: qa - (qa - qb) >= qa - Qabs (qa - qb)).
     { apply Qplus_le_compat. apply Qle_refl. apply Qopp_le_compat. apply Qle_Qabs. }
    assert (E3: qa >= eps0).
     { apply (H1 _ HN1 _ Hqa). }
    assert (E4: - Qabs (qa - qb) >= - (eps0 * (1 # 2))).
     { apply (proj2 (Qopp_le_compat_iff _ _)). rewrite Qopp_involutive. rewrite Qopp_involutive.
       apply Qlt_le_weak. apply (H2 n HN2 qa qb Hqa Hqb). }
    assert (E5: eps0 * (1 # 2) <= qa - Qabs (qa - qb)).
     { assert (Et: eps0 * (1 # 2) == eps0 -eps0 * (1 # 2) ) by ring. rewrite Et.
       apply Qplus_le_compat. auto. auto. }
    rewrite E1.
    apply (Qle_trans _ _ _ E5 E2).
  - exists (S N1). intros n HN1. apply not_lt in HN. assert (HN2:(n > N2)%nat) by omega.
    intros qb Hqb. destruct (Cauchy_exists _ HA n) as [qa Hqa].
    assert (E1: qb == qa - (qa - qb)) by ring.
    assert (E2: qa - (qa - qb) >= qa - Qabs (qa - qb)).
     { apply Qplus_le_compat. apply Qle_refl. apply Qopp_le_compat. apply Qle_Qabs. }
    assert (E3: qa >= eps0).
     { assert (Et: le N1 n) by omega. apply (H1 _ Et _ Hqa). }
    assert (E4: - Qabs (qa - qb) >= - (eps0 * (1 # 2))).
     { apply (proj2 (Qopp_le_compat_iff _ _)). rewrite Qopp_involutive. rewrite Qopp_involutive.
       apply Qlt_le_weak. apply (H2 n HN2 qa qb Hqa Hqb). }
    assert (E5: eps0 * (1 # 2) <= qa - Qabs (qa - qb)).
     { assert (Et: eps0 * (1 # 2) == eps0 -eps0 * (1 # 2) ) by ring. rewrite Et.
       apply Qplus_le_compat. auto. auto. }
    rewrite E1.
    apply (Qle_trans _ _ _ E5 E2).
Qed.

Instance Rpositive_proper_iff: Proper (Real_equiv ==> iff) Rpositive.
Proof.
  intros.
  hnf.
  intros.
  split.
  + apply Rpositive_equiv. auto.
  + apply Rpositive_equiv. symmetry. auto.
Qed.

Definition Rnegative (A:Real):Prop:=
 Rpositive (Ropp A).


Instance Rnegative_proper_iff: Proper (Real_equiv ==> iff) Rnegative.
Proof.
  intros.
  hnf.
  intros.
  assert (E: (Ropp x == Ropp y)%R). {
    destruct x as [X HX],y as [Y HY]. hnf. hnf in H. 
    intros eps Heps. destruct (H eps Heps) as [N H1].
    exists N. unfold Cauchy_opp. intros.
    destruct (Cauchy_exists _ HX m) as [qX HqX].
    destruct (Cauchy_exists _ HY m) as [qY HqY].
    rewrite (H2 _ HqX). rewrite (H3 _ HqY).
    assert (E1: Qabs (qX - qY) < eps). { apply (H1 m). auto. auto. auto. }
    assert (E2: - qX - - qY == - (qX - qY)) by ring. rewrite E2.
    rewrite Qabs_opp. auto. } unfold Rnegative.
  split.
  + intros. rewrite <- E. auto.
  + intros. rewrite E. auto. 
Qed.


(*
Definition Rnegative3 (A:Real):Prop:=
  match A with
  | Real_intro A0 _ =>  exists A1, Rpositive A1 /\ ( A == (Ropp A1))%R
  end.


Definition Rnegative2 (A:Real):Prop:=
  match A with
  | Real_intro A0 _ => exists A, Rpositive A /\ (forall n q, 
     (match A with Real_intro A1 _ => A1 end) n q -> A0 n (-q))
  end.

Bad Definitions!

*)

(* Seem to be a very useful theorem in proving*)
Theorem take_max_N: forall N1 N2 (P Q:nat->Prop), (forall n, (n>=N1)%nat -> P n) -> (forall n ,(n>=N2)%nat -> Q n) ->
  exists N, forall n, (n>=N)%nat -> (P n /\ Q n).
Proof. intros. assert (HN: lt N1 N2 \/ ~(lt N1 N2)) by (apply classic). destruct HN as [HN|HN].
  - exists N2. intros n HN2. assert (HN1: (n >= N1)%nat) by omega.
    split. auto. auto.
  - exists N1. intros n HN1. assert (HN2: (n >= N2)%nat) by omega.
    split. auto. auto.
Qed.

Theorem Real_positive_not_negative: forall A, ~ (Rpositive A /\ Rnegative A).
Proof. intros. intros [[eps0 [Heps0 [NA C1]]] C2]. destruct A as [A HA]. hnf in C2. unfold Ropp in C2. unfold Cauchy_opp in C2.
  destruct C2 as [eps1 [Heps1 [NB C2]]].
  destruct (take_max_N NA NB 
               (fun n => forall q : Q, A n q -> eps0 <= q)
               (fun n => forall q : Q,
     (forall q1 : Q, A n q1 -> q == - q1) -> eps1 <= q)
               C1 C2) as [N E]. clear C1 C2.
  assert (E2: (N>=N)%nat) by omega. apply E in E2. clear E.
  destruct (Cauchy_exists _ HA N) as [qa Hqa].
  destruct E2 as [E2 E3].
  assert (C1: qa > 0). { apply (Qlt_le_trans _ eps0). auto. auto. }
  assert (C2: qa < 0). { rewrite <- Qopp_involutive. rewrite <- (Qopp_involutive 0).
                         apply Qopp_lt_compat. apply (Qlt_le_trans _ eps1). auto. apply E3.
                         intros. rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
  assert (Contra: qa > qa). { apply (Qlt_trans _ 0). auto. auto. }
  apply Qlt_irrefl in Contra. contradiction.
Qed.


Theorem take_max_N_2: forall N1 N2 (P:nat->Prop) (Q:nat->nat->Prop),
 (forall n, (n>N1)%nat -> P n) -> (forall m1 m2 ,(m1>N2)%nat-> (m2 > N2)%nat -> (Q m1 m2)) ->
  exists N, (forall n, (n>=N)%nat -> P n) /\ (forall m1 m2, (m1>N)%nat-> (m2 > N)%nat  -> Q m1 m2).
Proof. intros. assert (HN: lt N1 N2 \/ ~(lt N1 N2)) by (apply classic). destruct HN as [HN|HN].
  - exists N2. split. intros n HnN2. assert (HnN1: (n > N1)%nat) by omega. auto.
    intros  m1 m2 Hm1N2 Hm2N2. auto.
  - exists (S N1). split. intros n HnN1. auto. intros.
    assert (Hm1N2: (m1 > N2)%nat) by omega.
    assert (Hm2N2: (m2 > N2)%nat) by omega.
    auto.
Qed.


Theorem Real_not_zero_positive_or_negative: forall A,
~(A==Rzero)%R -> ((Rpositive A) \/ (Rnegative A)).
Proof. intros [A HA] H. apply limit_not_0_spec in H. 
  apply (Cauchy_nonzero_pre _ HA) in H.
  destruct H as [N1 [eps0 [Heps0 H1]]].
  destruct (Cauchy_def _ HA (eps0*(1#2)) (eps_divide_2_positive _ Heps0)) as [N2 H2].
  destruct (take_max_N_2 N1 N2
               (fun n => forall q : Q, A n q -> eps0 <= Qabs q)
               (fun m1 m2 => forall (q1 q2 : Q), A m1 q1 -> A m2 q2 -> Qabs (q1 - q2) < eps0 * (1 # 2))
               H1 H2) as [N [E1 E2]]. clear H1 H2.
  destruct (Cauchy_exists _ HA (S N)) as [qN HqN].
  destruct (Qlt_le_dec qN 0) as [HqNsig|HqNsig].
  - right. hnf. exists (eps0*(1#2)). split. apply (eps_divide_2_positive _ Heps0).
      exists (S N). intros. hnf in H0. 
      destruct (Cauchy_exists _ HA n) as [qn Hqn].
      assert (E0:q == - qn) by auto. rewrite E0.
      assert (E3: qn == qN - (qN - qn)) by ring.
      assert (E4: qN- (qN - qn) <= qN + Qabs (qN -qn)).
        { apply Qplus_le_compat. apply Qle_refl.
          assert (Et: - (qN - qn) == qn - qN) by ring. rewrite Et.
          rewrite Qabs_Qminus. apply Qle_Qabs. }
      assert (E5: qN <= - eps0). { 
          assert (Et: qN == - (Qabs qN)).
          { assert (Et1: - qN == Qabs qN). symmetry. apply Qabs_neg. apply Qlt_le_weak. auto.
            rewrite <- Et1. rewrite Qopp_involutive. reflexivity. }
          rewrite Et. apply Qopp_le_compat. apply (E1 (S N)). omega. auto. }
      assert (E6: Qabs (qN - qn) < eps0 * ( 1 # 2)). 
        { apply (E2 (S N) n). omega. auto. auto. auto. }
      assert (E7: - (eps0 * (1 # 2)) == - eps0 + eps0 * (1 # 2)) by ring.
      rewrite <- Qopp_involutive. apply Qopp_le_compat.
      rewrite E7,E3. apply (Qle_trans _ _ _ E4). apply Qplus_le_compat. auto.
      apply Qlt_le_weak. auto.
   - left. hnf. exists (eps0*(1#2)). split. apply (eps_divide_2_positive _ Heps0).
      exists (S N). intros. hnf in H0.
      assert (E3: q == qN - (qN - q)) by ring.
      assert (E4: qN- (qN - q) >= qN - Qabs (qN -q)).
        { apply Qplus_le_compat. apply Qle_refl.
          apply Qopp_le_compat. apply Qle_Qabs. }
      assert (E5: qN >= eps0). { rewrite <- (Qabs_pos qN HqNsig). apply (E1 (S N)). omega. auto. }
      assert (E6: Qabs (qN - q) < eps0 * ( 1 # 2)). 
        { apply (E2 (S N) n). omega. auto. auto. auto. }
      assert (E7: (eps0 * (1 # 2)) == eps0 - eps0 * (1 # 2)) by ring.
      rewrite E7,E3. apply (Qle_trans _ (qN - Qabs (qN - q)) _). apply Qplus_le_compat. auto.
      apply Qopp_le_compat. apply Qlt_le_weak. auto. auto.
Qed.


Theorem take_max_N3: forall N1 N2 (P Q:nat->Prop), (forall n, (n>=N1)%nat -> P n) -> (forall n ,(n>N2)%nat -> Q n) ->
  exists N, forall n, (n>=N)%nat -> (P n /\ Q n).
Proof. intros. assert (HN: lt N1 N2 \/ ~(lt N1 N2)) by (apply classic). destruct HN as [HN|HN].
  - exists (S N2). intros n HN2. assert (HN1: (n >= N1)%nat) by omega.
    split. auto. auto.
  - exists (S N1). intros n HN1. assert (HN2: (n >= N2)%nat) by omega.
    split. apply H. omega. apply H0. omega.
Qed.

Lemma Rzero_not_positive: forall A, (A == 0)%R -> ~ Rpositive A.
Proof. intros A.
      destruct A as [A HA]. intros C H. hnf in *. destruct H as [eps [Heps [N H]]].
      destruct (C _ Heps) as [N1 HN1]. clear C.
      destruct (take_max_N3 N N1
                   (fun n => forall q : Q, A n q -> eps <= q)
                   (fun m => forall q1 q2 : Q, A m q1  -> q2 == 0 -> Qabs (q1 - q2) < eps)
                    H HN1) as [Nmax HNmax]. clear H HN1.
      destruct (Cauchy_exists _ HA Nmax) as [qn Hqn].
      assert (E1: qn >= eps). { apply (HNmax Nmax). omega. auto. }
      assert (E2: Qabs qn < eps). { rewrite <- (Qplus_0_r qn).
          assert (Et: ge Nmax Nmax) by omega.
          apply ((proj2 (HNmax Nmax Et)) qn (- 0)). auto. reflexivity. }
      assert (E3: qn > Qabs qn). { apply (Qlt_le_trans _ _ _ E2 E1). }
      apply Qlt_not_le in E3. apply E3. apply Qle_Qabs.
Qed.

Lemma Rzero_not_negative: forall A, (A == 0)%R -> ~ Rnegative A.
Proof. intros A.
      destruct A as [A HA]. intros C H. hnf in *. destruct H as [eps [Heps [N H]]].
      destruct (C _ Heps) as [N1 HN1]. clear C. unfold Ropp in H. unfold Cauchy_opp in H.
      destruct (take_max_N3 N N1
                   (fun n => forall q : Q, (forall q1 : Q, A n q1 -> q == - q1) -> eps <= q)
                   (fun m => forall q1 q2 : Q, A m q1  -> q2 == 0 -> Qabs (q1 - q2) < eps)
                    H HN1) as [Nmax HNmax]. clear H HN1.
      destruct (Cauchy_exists _ HA Nmax) as [qn Hqn].
      assert (E1: qn <= - eps). { rewrite <-Qopp_involutive. apply Qopp_le_compat. 
        apply (HNmax Nmax). omega. intros.  rewrite (Cauchy_unique _ HA _ _ _ Hqn H). reflexivity. }
      assert (E2: Qabs qn < eps). { rewrite <- (Qplus_0_r qn).
          assert (Et: ge Nmax Nmax) by omega.
          apply ((proj2 (HNmax Nmax Et)) qn (- 0)). auto. reflexivity. }
      assert (E3: - qn > Qabs qn). { apply (Qlt_le_trans _ _ _ E2). 
          rewrite <- Qopp_involutive. apply Qopp_le_compat. auto. }
      rewrite <- Qabs_opp in E3.
      apply Qlt_not_le in E3. apply E3. apply Qle_Qabs.
Qed.

Lemma Rpositive_not_zero: forall A, Rpositive A -> ~ (A == 0)%R.
Proof. intros A H. intros C. rewrite C in H. hnf in H. unfold Rzero in H.
       destruct H as [eps0 [Heps0 [N HN]]].
       assert (nonsense: eps0 <=0). { apply (HN N). omega. reflexivity. }
       apply Qle_not_lt in nonsense. contradiction.
Qed.

Lemma Rnegative_not_positive: forall A, Rnegative A -> ~ Rpositive A.
Proof. intros. intros C. assert (E:Rpositive A /\ Rnegative A) by auto.
       apply Real_positive_not_negative in E. apply E.
Qed.

Lemma Rpositive_not_negative: forall A, Rpositive A -> ~ Rnegative A.
Proof. intros. intros C. assert (E:Rpositive A /\ Rnegative A) by auto.
       apply Real_positive_not_negative in E. apply E.
Qed.

Lemma Rnegative_not_zero: forall A, Rnegative A -> ~(A==0)%R.
Proof. intros A H. intros C. rewrite C in H. hnf in H. unfold Rzero in H.
       destruct H as [eps0 [Heps0 [N HN]]].
       destruct A as [A HA]. unfold Ropp in HN. unfold Cauchy_opp in HN.
       destruct (Cauchy_exists _ HA N) as [qn Hqn].
       assert (nonsense: eps0 <= 0). { apply (HN N). 
       omega. intros. rewrite H. reflexivity. }
       apply Qle_not_lt in nonsense. contradiction.
Qed.

Theorem Real_positive_0_negative: forall A, 
 ( Rpositive A /\ ~(A==Rzero)%R  /\ ~ Rnegative A ) \/
 ( ~ Rpositive A /\ (A==Rzero)%R  /\ ~ Rnegative A ) \/
 ( ~ Rpositive A /\ ~(A==Rzero)%R  /\ Rnegative A ).
Proof. intros. assert (Case1: (A==Rzero)%R  \/ ~(A==Rzero)%R) by (apply classic).
  destruct Case1 as [Case1|Case2].
  - right. left. split.
    + apply Rzero_not_positive. auto.
    + split. auto.
      apply Rzero_not_negative. auto.
   - apply Real_not_zero_positive_or_negative in Case2. destruct Case2 as [Case2|Case3].
   + left. split. auto. split.
     * apply Rpositive_not_zero. auto.
     * apply Rpositive_not_negative. auto.
   + right. right. split.
     * apply Rnegative_not_positive. auto.
     * split. apply Rnegative_not_zero. auto.
       auto.
Qed.

Definition Rlt (a b:Real) : Prop :=
  Rpositive (Rminus a b).


Notation "a < b" := (Rlt a b):Real_scope.

Theorem Rlt_trans: forall A B C, (A < B)%R -> (B < C)%R -> (A < C)%R.
Proof. intros.
  destruct A as [A HA], B as [B HB], C as [C HC]. hnf in *.
  unfold Rminus in *. unfold Ropp in *. unfold Cauchy_opp in *.
  unfold Rplus in *. unfold CauchySeqPlus in *.
  destruct H as [epsAB [HepsAB [NAB HAB]]]. destruct H0 as [epsBC [HepsBC [NBC HBC]]].
  destruct (take_max_N NAB NBC
                  (fun n => forall q : Q, (forall q1 q2 : Q, A n q1 -> (forall q3 : Q, B n q3 -> q2 == - q3) -> q == q1 + q2) -> epsAB <= q)
                  (fun n => forall q : Q, (forall q1 q2 : Q, B n q1 -> (forall q3 : Q, C n q3 -> q2 == - q3) -> q == q1 + q2) -> epsBC <= q)
                      HAB HBC) as [N H]. clear HAB HBC.
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
    assert (E2: qa - qc == (qa - qb) + (qb - qc)) by ring.
    assert (E3: qac == qa - qc). 
      { apply Hq. auto. intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H). reflexivity. }
    assert (E4: epsAB <= (qa - qb)).
      { apply H1. intros. auto. rewrite (H0 qb Hqb).
        rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
    assert (E5: epsBC <= (qb - qc)).
      { apply H2. intros. auto. rewrite (H0 qc Hqc).
        rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity. }
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
    assert (E2: qa - qc == (qa - qb) + (qb - qc)) by ring.
    assert (E3: qac == qa - qc). 
      { apply Hq. auto. intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H). reflexivity. }
    assert (E4: epsAB <= (qa - qb)).
      { apply H1. intros. auto. rewrite (H0 qb Hqb).
        rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
    assert (E5: epsBC <= (qb - qc)).
      { apply H2. intros. auto. rewrite (H0 qc Hqc).
        rewrite (Cauchy_unique _ HB _ _ _ Hqb H). reflexivity. }
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
  assert (E: q == (qa + qc) - (qb + qc)).
    { apply H1.
      - intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H3).
        rewrite (Cauchy_unique _ HA _ _ _ Hqa H2). reflexivity.
      - intros. rewrite (H2 _ _ Hqb Hqc). reflexivity. }
  assert (E1: (qa + qc) - (qb + qc) == qa - qb) by ring.
  apply (H n). auto. intros.
  rewrite <- (Cauchy_unique _ HA _ _ _ Hqa H2).
  assert (E3: q2 == - qb) by auto. rewrite E3.
  rewrite E. rewrite E1. reflexivity.
Qed.

Theorem Rlt_mult_r: forall (A B C:Real),  (Rpositive C) ->(A < B)%R -> (A*C < B*C)%R.
Proof. intros. destruct A as [A HA], B as [B HB], C as [C HC]. hnf in *.
  unfold Rminus in *. unfold Rplus in *. unfold CauchySeqPlus in *.
  unfold Ropp in *. unfold Cauchy_opp in *. unfold Rmult in *.
  unfold CauchySeqMult in *. destruct H as [eps1 [Heps1 [N1 H1]]].
  destruct H0 as [eps2 [Heps2 [N2 H2]]].
  destruct (take_max_N N1 N2
                  (fun n => forall q : Q, C n q -> eps1 <= q)
                  (fun n => forall q : Q, (forall q1 q2 : Q, A n q1 -> (forall q3 : Q, B n q3 -> q2 == - q3) -> q == q1 + q2) -> eps2 <= q)
                      H1 H2) as [N H]. clear H1 H2 N1 N2.
  exists (eps2*eps1). split.
  { rewrite <- (Qmult_0_l eps1). apply (Qmult_lt_r). auto. auto. }
  exists N. intros n Hn q H0. destruct (H _ Hn) as [H1 H2]. clear H.
  destruct (Cauchy_exists _ HA n) as [qa Hqa],
           (Cauchy_exists _ HB n) as [qb Hqb],
           (Cauchy_exists _ HC n) as [qc Hqc].
  assert (E1: q == qa*qc - qb*qc).
  { apply H0.
    - intros. rewrite (Cauchy_unique _ HC _ _ _ Hqc H3).
      rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity.
    - intros. rewrite (H _ _ Hqb Hqc). reflexivity. }
  assert (E2: qa*qc - qb*qc == (qa-qb)*qc) by ring.
  assert (E3: eps2 <= qa -qb).
  { apply H2. intros. rewrite (H3 _ Hqb).
    rewrite (Cauchy_unique _ HA _ _ _ Hqa H). reflexivity. }
  assert (E4: eps1 <= qc).
  { apply H1. auto. }
  rewrite E1,E2. apply Qmult_le_compat_nonneg.
  apply Qlt_le_weak. auto.
  apply Qlt_le_weak. auto.
  auto. auto.
Qed.

Instance Rlt_comp : Proper (Real_equiv ==> Real_equiv ==> iff) Rlt.
Proof. split.
- intros. unfold Rlt. assert (E1: (y-y0==x-x0)%R).
  rewrite <- H. rewrite H0. reflexivity.
  unfold Rlt in H1. rewrite E1. apply H1.
- intros. unfold Rlt. assert (E1: (y-y0==x-x0)%R).
  rewrite <- H. rewrite H0. reflexivity.
  unfold Rlt in H1. rewrite <- E1. apply H1.
Qed.


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


Theorem Rabs_zero: forall A, (A==0)%R -> (Rabs A == 0)%R.
Proof. intros. rewrite H. hnf. intros. exists O. intros. unfold Cauchy_abs in *.
  rewrite H3. assert (Et: q1 - 0 == q1) by ring. rewrite Et.
  rewrite (H2 0). apply H0. reflexivity.
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
