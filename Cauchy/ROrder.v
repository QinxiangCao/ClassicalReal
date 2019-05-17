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
From CReal Require Import QArith_ext.QArith_base_ext.
From Coq Require Import Classes.Morphisms.
From CReal.Cauchy Require Import RBase.
From Coq Require Export Field.


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

Lemma Rnot_positive: forall A, ~ (Rpositive A) -> (Rnegative A) \/ (A==0)%R.
Proof. intros. destruct (classic (A==0)%R).
  - right. auto.
  - left. destruct (classic (Rnegative A)). auto.
    destruct (Real_positive_0_negative A).
    + destruct H2. contradiction.
    + destruct H2. * destruct H2. destruct H3. contradiction.
      * destruct H2. destruct H3. auto.
Qed.

Lemma Rnot_negative: forall A, ~ (Rnegative A) -> (Rpositive A) \/ (A==0)%R.
Proof. intros. destruct (classic (A==0)%R).
  - right. auto.
  - left. destruct (classic (Rpositive A)). auto.
    destruct (Real_positive_0_negative A).
    + destruct H2. contradiction.
    + destruct H2. * destruct H2. destruct H3. contradiction.
      * destruct H2. destruct H3. contradiction.
Qed.



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

Theorem Rabs_Ropp (A:Real): (Rabs A == Rabs (- A))%R.
Proof. intros. destruct (classic (A == 0)%R).
  - rewrite H. rewrite <- Rzero_opp_zero. reflexivity.
  - apply Real_not_zero_positive_or_negative in H. destruct H.
    + rewrite (Rabs_positive _ H). apply Rpositive_Ropp in H. rewrite Rabs_negative.
      rewrite <- Ropp_involutive. reflexivity. auto.
    + rewrite (Rabs_negative _ H). apply Rnegative_Ropp in H. rewrite Rabs_positive.
      reflexivity. auto.
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



(** Some helping lemmas (easy to prove)*)

Lemma Qplus_le_lt_compat:forall x y z t, x<=y -> z<t -> x+z < y+t.
Proof. intros.
  rewrite (Qplus_comm x). rewrite (Qplus_comm y).
  apply Qplus_lt_le_compat.
  auto. auto.
Qed.

Lemma Qopp_Qlt_compat: forall p q, p<q -> -q < -p.
Proof. intros. apply (Qplus_lt_r _ _ (p+q)).
  rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
  rewrite Qplus_0_r. rewrite Qplus_comm.
  rewrite Qplus_assoc. rewrite (Qplus_comm _ p). rewrite Qplus_opp_r.
  rewrite Qplus_0_l. auto.
Qed.

Lemma Qle_lt_minus (a b c d:Q): a <= b -> c < d -> a - d < b - c.
Proof. intros.
  apply Qplus_le_lt_compat. auto. apply Qopp_Qlt_compat. auto.
Qed.


Lemma Qdiv_lt_compat (a b c :Q): c> 0 ->a < b ->  a/c < b/c.
Proof. intros. apply Qinv_lt_0_compat in H.
  apply (Qmult_lt_r _ _ _ H). auto.
Qed.


Lemma Qdiv_le_compat (a b c :Q):  c> 0 ->a <= b -> a/c <= b/c.
Proof. intros. apply Qinv_lt_0_compat in H.
  apply (Qmult_le_r _ _ _ H). auto.
Qed.

Lemma Qinject_nat_pos: forall m, m<>O -> 0 < inject_Z (Z.of_nat (m)).
Proof. intros. assert (0==inject_Z 0%Z) by reflexivity.
  rewrite H0. rewrite <- Zlt_Qlt.
  pose proof (Nat2Z.is_nonneg m).
  apply Zle_lt_or_eq in H1. destruct H1.
  auto. destruct H.
  rewrite <- (Nat2Z.id m).
  rewrite <- H1. reflexivity.
Qed.

Lemma inject_Z_nonzero: forall n, n<>O -> ~ inject_Z (Z.of_nat (n)) == 0.
Proof. intros. apply Qinject_nat_pos in H. intros C.
  rewrite C in H. apply Qlt_irrefl in H. auto.
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


Lemma Inject_1: forall x, Z.pos (Pos.of_nat (S x)) = Z.of_nat (S x).
Proof. intros. induction x.
  - reflexivity.
  - rewrite (Nat2Pos.inj_succ). rewrite Pos2Z.inj_succ.
    rewrite IHx. rewrite <- Nat2Z.inj_succ. reflexivity. auto.
Qed.

Lemma Inject_2: forall x, (x<>0)%nat -> Z.pos (Pos.of_nat (x)) = Z.of_nat (x).
Proof. intros. destruct x.
  - destruct H. reflexivity.
  - apply Inject_1.
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

Lemma inject_of_nat_equiv:forall n, (n<>0)%nat -> Z.of_nat n # Pos.of_nat n == 1.
Proof. intros. destruct n.
  - destruct H. reflexivity.
  - induction n.
  + reflexivity.
  + assert ( S n <> 0)%nat by omega. apply IHn in H0.
    rewrite Nat2Z.inj_succ. rewrite Nat2Pos.inj_succ.
    rewrite Qmake_Qdiv in H0.
    assert (inject_Z (Z.of_nat (S n)) == inject_Z (Z.pos (Pos.of_nat (S n)))).
    { rewrite <- (Qmult_1_r (inject_Z (Z.pos (Pos.of_nat (S n))))). rewrite <- H0.
      field. intros C. assert (0 == inject_Z 0) by reflexivity. rewrite H1 in C.
      apply (proj1 (inject_Z_injective _ _)) in C. inversion C. }
    apply  (proj1 (inject_Z_injective _ _)) in H1. rewrite H1.
    rewrite Qmake_Qdiv.
    assert ((Z.succ (Z.pos (Pos.of_nat (S n)))) = (Z.pos (Pos.succ (Pos.of_nat (S n))))).
    { rewrite Pos2Z.inj_succ. reflexivity. } 
    rewrite H2. field. intros C. assert (0 == inject_Z 0) by reflexivity. rewrite H3 in C.
      apply (proj1 (inject_Z_injective _ _)) in C. inversion C. omega.
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


Lemma inject_Q_pos: forall q, q>0 -> Rpositive (inject_Q q).
Proof. intros. hnf. exists (q*(1#2)). split.
  apply eps_divide_2_positive. auto.
  exists (S O). intros. unfold inject_Q in H1. rewrite H1.
  rewrite <- (Qmult_1_r q). rewrite <- Qmult_assoc.
  apply (proj2 (Qmult_le_l _ _ _ H)). rewrite Qmult_1_l.
  intros C. inversion C.
Qed.


Lemma max_lt_lub_l: forall n m p, (max n m < p -> n < p)%nat.
Proof. intros. apply (le_lt_trans _ (max n m)).
  apply Nat.le_max_l. auto.
Qed.

Lemma Qmake_pos_inject_Z: forall m, (m<>0)%nat -> 1 # Pos.of_nat m ==  1 / inject_Z (Z.of_nat m).
Proof. intros. rewrite Qmake_Qdiv. rewrite Inject_2. reflexivity. auto.
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


Lemma Qabs_Qlt_condition x y: Qabs x < y <-> -y < x /\ x < y.
Proof.
 split.
  split.
   rewrite <- (Qopp_opp x).
   apply Qopp_lt_compat.
   apply Qle_lt_trans with (Qabs (-x)).
   apply Qle_Qabs.
   now rewrite Qabs_opp.
  apply Qle_lt_trans with (Qabs x); auto using Qle_Qabs.
 intros (H,H').
 apply Qabs_case; trivial.
 intros. rewrite <- (Qopp_opp y). now apply Qopp_lt_compat.
Qed.


Lemma Qabs_diff_Qlt_condition:
  forall x y r : Q, Qabs (x - y) < r <-> (x - r < y /\ y < x + r)%Q.
Proof.
 intros. unfold Qminus.
 rewrite Qabs_Qlt_condition.
 rewrite <- (Qplus_lt_l (-r) (x+-y) (y+r)).
 rewrite <- (Qplus_lt_l (x+-y) r (y-r)).
 setoid_replace (-r + (y + r)) with y by ring.
 setoid_replace (r + (y - r)) with y by ring.
 setoid_replace (x + - y + (y + r)) with (x + r) by ring.
 setoid_replace (x + - y + (y - r)) with (x - r) by ring.
 intuition.
Qed.


Theorem inject_Q_eq_inv: forall q1 q2, (inject_Q q1 == inject_Q q2)%R -> q1 == q2.
Proof. intros. hnf in H.
  destruct (classic (q1 == q2)). auto.
  assert (E:~(q1-q2==0)).
  { intros C. apply H0. rewrite <- (Qplus_0_r q2). rewrite <- C. ring. }
  apply Qnot_0_abs_pos in E. apply H in E.
  destruct E. assert (foo: Qabs (q1 - q2) < Qabs (q1 - q2)).
  { apply (H1 (S x)). omega. reflexivity. reflexivity. }
  apply Qlt_irrefl in foo. destruct foo.
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



(** ---------- Single2Element Function ----------------*)

(** First define Rfloor (Real -> Z -> Prop) *)

Definition Rfloor (A:Real)(z:Z):Prop := (inject_Q (inject_Z z) <= A)%R
 /\ (inject_Q ((inject_Z z) + 1) > A)%R.

Theorem Rfloor_exists: forall A:Real, exists z, Rfloor A z.
Proof. intros. destruct A as [A HA].
  destruct (Cauchy_def _ HA (1#4)) as [n Hn]. reflexivity.
  destruct (Cauchy_exists _ HA (S n)) as [qn Hqn].
  remember (Qfloor qn) as zqn.
  destruct (classic (inject_Q (inject_Z zqn) <= (Real_intro A HA))%R).
  - destruct (classic (inject_Q (inject_Z (zqn + 1)%Z) <= (Real_intro A HA))%R).
  + exists (zqn + 1)%Z. hnf. split.
    auto. hnf. exists (1#2). split. reflexivity.
    exists (S n). intros. hnf in H2. unfold Cauchy_opp in H2.
    destruct (Cauchy_exists _ HA n0) as [qn0 Hqn0].
    assert (q == inject_Z (zqn+ 2) - qn0).
    { apply H2. assert (Et: 1 == inject_Z 1) by ring.
      rewrite Et. rewrite <- inject_Z_plus.
      assert (Et1: (zqn + 2 = zqn + 1 + 1)%Z) by omega.
      rewrite Et1. reflexivity.
      intros. rewrite (Cauchy_unique _ HA _ _ _ Hqn0 H3). reflexivity. }
    assert (H4: inject_Z (zqn +1) > qn).
    { rewrite Heqzqn. apply Qlt_floor. }
    assert (H5: Qabs (qn - qn0) < 1#4).
    { apply (Hn (S n) n0). auto. auto. auto. auto. }
    apply (Qle_trans _  (-(1#4)+1)).
    { assert (-(1#4)+1==3#4). { ring. }
      rewrite H6. intros C. simpl in C. discriminate C. }
    rewrite H3. unfold Qminus.
    assert (H7: inject_Z (zqn + 1) - qn0 > -(1#4)).
    { apply (Qlt_trans _ (qn-qn0)). apply Qabs_Qlt_condition in H5. destruct H5.
      auto. unfold Qminus. apply (proj2 (Qplus_lt_l _ _ (- qn0))). auto. }
    assert (H8: inject_Z (zqn + 2) + - qn0 == inject_Z (zqn + 1) - qn0 + 1).
    { unfold Qminus. rewrite <-(Qplus_assoc). rewrite (Qplus_comm _ 1).
      rewrite Qplus_assoc. assert (1==inject_Z 1) by ring.
      rewrite H6. rewrite <- inject_Z_plus.
      assert (zqn + 1 + 1 = zqn + 2)%Z by omega. rewrite H8. reflexivity. }
    rewrite H8. apply Qplus_le_compat.
    apply Qlt_le_weak. auto. apply Qle_refl.
  + exists zqn. hnf. split.
    auto. apply Rnot_le_lt in H0.
    assert ((inject_Q (inject_Z (zqn + 1)) ==(inject_Q (inject_Z zqn + 1)))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. rewrite inject_Z_plus. ring. }
      rewrite H5. auto. }
    rewrite <- H1. auto.
  - destruct (classic (inject_Q (inject_Z zqn - 1) <= (Real_intro A HA))%R).
  + exists (zqn-1)%Z. split.
    assert (T:((inject_Q (inject_Z (zqn - 1)) ==(inject_Q (inject_Z zqn -1)))%R)).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite T. auto.
    apply Rnot_le_lt in H.
    assert ((inject_Q (inject_Z (zqn-1)+1) ==(inject_Q (inject_Z zqn )))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite H1. auto.
  + apply Rnot_le_lt in H. apply Rnot_le_lt in H0. exists (zqn-2)%Z.
    hnf. split.
  * hnf. left. hnf. exists (1#2). split. reflexivity.
    exists (S n). intros. hnf in H2. unfold Cauchy_opp in H2.
    destruct (Cauchy_exists _ HA n0) as [qn0 Hqn0].
    assert (q == qn0 - inject_Z (zqn - 2)).
    { apply H2. auto. intros. rewrite H3. reflexivity. }
    assert (H4: inject_Z (zqn ) <= qn).
    { rewrite Heqzqn. apply Qfloor_le. }
    assert (H5: Qabs (qn0 - qn) < 1#4).
    { apply (Hn n0 (S n)). auto. auto. auto. auto. }
    apply (Qle_trans _  (-(1#4)+(inject_Z 2))).
    { assert (-(1#4)+(inject_Z 2)==7#4). { ring. }
      rewrite H6. intros C. simpl in C. discriminate C. }
    rewrite H3. unfold Qminus.
    assert (H7: qn0 -inject_Z (zqn) > -(1#4)).
    { apply Qabs_Qlt_condition in H5. destruct H5.
      apply (Qlt_le_trans _ (qn0 - qn)).
      auto. unfold Qminus. apply (proj2 (Qplus_le_r _ _ (qn0))).
      apply Qopp_le_compat. auto. }
    assert (H8: qn0 + - inject_Z (zqn - 2) == (qn0 - (inject_Z zqn)) + (inject_Z 2)).
    { unfold Qminus. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
    rewrite H8. apply Qplus_le_compat.
    apply Qlt_le_weak. auto. apply Qle_refl.
  * assert (T:(inject_Q (inject_Z zqn - 1) ==(inject_Q (inject_Z (zqn - 2) + 1)))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H3,H4. unfold Zminus. rewrite inject_Z_plus.
      rewrite inject_Z_opp. ring. }
      rewrite H5. auto. }
    rewrite <- T. auto.
Qed.


Theorem Rfloor_unique: forall (A:Real) (z1 z2:Z), Rfloor A z1 -> Rfloor A z2 -> z1 = z2.
Proof. intros. hnf in *. destruct H as [H1 H2], H0 as [H3 H4].
destruct (Ztrichotomy_inf z1 z2) as [[Z1|Z2]|Z3].
- assert (E:(z1+1<=z2)%Z) by omega.
  rewrite Zle_Qle in E. apply Qle_Rle in E.
  assert (foo: (A < A)%R).
  { apply (Rlt_le_trans _ _ _ H2). apply (Rle_trans _ (inject_Q (inject_Z z2))).
    assert (Et: (inject_Q (inject_Z z1 + 1) == (inject_Q (inject_Z (z1 + 1))))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H5,H6.  rewrite inject_Z_plus. ring. }
      rewrite H7. auto. }
    rewrite Et. auto. auto. }
  apply Rlt_irrefl in foo. destruct foo.
- auto.
- assert (E:(z2+1<=z1)%Z) by omega.
  rewrite Zle_Qle in E. apply Qle_Rle in E.
  assert (foo: (A < A)%R).
  { apply (Rlt_le_trans _ _ _ H4). apply (Rle_trans _ (inject_Q (inject_Z z1))).
    assert (Et: (inject_Q (inject_Z z2 + 1) == (inject_Q (inject_Z (z2 + 1))))%R).
    { hnf. intros. exists O. intros.
      assert (q1 - q2 == 0). { rewrite H5,H6.  rewrite inject_Z_plus. ring. }
      rewrite H7. auto. }
    rewrite Et. auto. auto. }
  apply Rlt_irrefl in foo. destruct foo.
Qed.


Instance Rfloor_comp: Proper (Real_equiv ==> Z.eq ==> iff) Rfloor.
Proof. split.
- intros. rewrite <- H0.
  destruct H1 as [H1 H2].
  split.
  rewrite <- H. auto. rewrite <- H.
  auto.
- intros. rewrite H0.
  destruct H1 as [H1 H2].
  split. rewrite H. auto.
  rewrite H. auto.
Qed.


(** Single Element Set to Element Function *)
Definition SingletonSet2Element : {X: Real -> Prop|(exists x, X x) /\ (forall x1 x2, X x1 ->
 X x2 -> x1 == x2) /\ Proper (Real_equiv ==> iff) (X)
 }%R -> Real.

Proof. intros. destruct X as [S [H1 [H2 H3]]].
  apply (Real_intro (fun n q => exists A, S A /\ forall z,
          (Rfloor (A * (inject_Q (inject_Z (Z.of_nat (n)%nat)))) z) -> 
        q == z # (Pos.of_nat (n)%nat))).
  split.
- intros. destruct H1 as [A0 HA0].
  destruct (Rfloor_exists  (A0 * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].
  exists (z # Pos.of_nat (n)).
  exists A0. split. auto. intros. rewrite (Rfloor_unique _ _ _ Hz H). reflexivity.
- intros. destruct H as[A1 [SHA1 HA1]]. destruct H0 as [A2 [SHA2 HA2]].
  destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat n)))) as [z1 Hz1].
  destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat n)))) as [z2 Hz2].
  assert (E:z1=z2). { apply (Rfloor_unique _ _ _ Hz1 Hz2). }
  rewrite (H2 _ _ SHA1 SHA2) in Hz2.
  rewrite (HA1 _ Hz1),(HA2 _ Hz2). rewrite E. reflexivity.
- intros. destruct H0 as [A [SHA HA]]. exists A. split. auto. 
  intros. rewrite <- H. apply (HA z). auto.
- intros. exists (max 2 (Z.to_nat (1 + (Qceiling (1/eps))))).
  intros. destruct H5 as [A1 [HA1 Hq1]].
  assert (Em1: m1 <> 0%nat).
  { intros C. rewrite C in H0. omega. }
  assert (Em2: m2 <> 0%nat).
  { intros C. rewrite C in H4. omega. }
  assert (Em3: (m1 - 1 <> 0)%nat).
  { intros C. assert (m1 = 1)%nat by omega. rewrite H5 in H0.
    apply max_lt_lub_l in H0. assert (foo: (~ 2<1)%nat). omega. contradiction. }
  assert (Em4: (m2 - 1 <> 0)%nat).
  { intros C. assert (m2 = 1)%nat by omega. rewrite H5 in H4.
    apply max_lt_lub_l in H4. assert (foo: (~ 2<1)%nat). omega. contradiction. }
    destruct H6 as [A2 [HA2 Hq2]].
    assert (A1==A2)%R by (apply (H2 _ _ HA1 HA2)).
    destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat m1)))) as [z1 Hz1].
    destruct (Rfloor_exists (A2 * inject_Q (inject_Z (Z.of_nat m2)))) as [z2 Hz2].
    assert (Hqz1: q1 == z1 # Pos.of_nat m1) by auto.
    assert (Hqz2: q2 == z2 # Pos.of_nat m2) by auto.
    clear Hq1. clear Hq2. 

    assert (E1: - (1/(inject_Z (Z.of_nat m1))) < (q1 - q2)
          /\ q1 - q2 < 1/(inject_Z (Z.of_nat m2))).
    { destruct Hz1 as [P1 P2].
      
      assert (T1: (inject_Q q1 > (A1 - (inject_Q (1#Pos.of_nat m1))))%R).
        { unfold Rgt. rewrite Hqz1. rewrite <- (Rmult_1_r A1).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em1))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m1)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em1).
          rewrite <- inject_Q_inv. reflexivity. }
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R as Rden.
        rewrite Et2. clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m1)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m1) * (1 # Pos.of_nat m1) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m1) * / inject_Z (Z.pos (Pos.of_nat m1)) ==
                            inject_Z (Z.of_nat m1)  / inject_Z (Z.pos (Pos.of_nat m1))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rlt_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m1))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m1)) > 0)).
          { rewrite (Inject_2 _ Em1). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z1) /
          inject_Z (Z.pos (Pos.of_nat m1)) * inject_Z (Z.pos (Pos.of_nat m1)) == 
          inject_Z (z1)).
          { field. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite Et5. unfold Rminus. rewrite Rmult_plus_distr_l.
        assert (Et6: (Rden * inject_Q (inject_Z (Z.pos (Pos.of_nat m1))) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            rewrite Qmake_Qdiv. unfold Qdiv. rewrite <- Qmult_assoc.
            rewrite (Qmult_comm (/ inject_Z (Z.pos (Pos.of_nat m1)))).
            rewrite Qmult_inv_r. reflexivity. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite <- Ropp_mult_distr. rewrite Et6.
        apply (Rlt_plus_compat_r _ _ 1%R).
        assert (Et7: (1 == (inject_Q 1))%R) by reflexivity.
        rewrite Rplus_assoc. rewrite (Rplus_comm (-(1))%R).
        rewrite Rplus_opp_r. rewrite Rplus_0_r. rewrite Et7.
        rewrite <- inject_Q_plus. rewrite (Inject_2 _ Em1). auto. }
      assert (T2: (inject_Q q1 <= A1 )%R).
        { rewrite Hqz1. rewrite <- (Rmult_1_r A1).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em1))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m1)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em1).
          rewrite <- inject_Q_inv. reflexivity. } 
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R as Rden.
        clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m1)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m1) * (1 # Pos.of_nat m1) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m1) * / inject_Z (Z.pos (Pos.of_nat m1)) ==
                            inject_Z (Z.of_nat m1)  / inject_Z (Z.pos (Pos.of_nat m1))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rle_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m1))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m1)) > 0)).
          { rewrite (Inject_2 _ Em1). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z1) /
          inject_Z (Z.pos (Pos.of_nat m1)) * inject_Z (Z.pos (Pos.of_nat m1)) == 
          inject_Z (z1)).
          { field. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite Et5. rewrite (Inject_2 _ Em1). auto. }
      clear P1. clear P2.
      destruct Hz2 as [P1 P2].
      assert (T3: (inject_Q q2 > (A2 - (inject_Q (1#Pos.of_nat m2))))%R).
        { unfold Rgt. rewrite Hqz2. rewrite <- (Rmult_1_r A2).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em2))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m2)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em2).
          rewrite <- inject_Q_inv. reflexivity. }
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R as Rden.
        rewrite Et2. clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m2)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m2) * (1 # Pos.of_nat m2) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m2) * / inject_Z (Z.pos (Pos.of_nat m2)) ==
                            inject_Z (Z.of_nat m2)  / inject_Z (Z.pos (Pos.of_nat m2))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rlt_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m2))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m2)) > 0)).
          { rewrite (Inject_2 _ Em2). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z2) /
          inject_Z (Z.pos (Pos.of_nat m2)) * inject_Z (Z.pos (Pos.of_nat m2)) == 
          inject_Z (z2)).
          { field. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite Et5. unfold Rminus. rewrite Rmult_plus_distr_l.
        assert (Et6: (Rden * inject_Q (inject_Z (Z.pos (Pos.of_nat m2))) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            rewrite Qmake_Qdiv. unfold Qdiv. rewrite <- Qmult_assoc.
            rewrite (Qmult_comm (/ inject_Z (Z.pos (Pos.of_nat m2)))).
            rewrite Qmult_inv_r. reflexivity. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite <- Ropp_mult_distr. rewrite Et6.
        apply (Rlt_plus_compat_r _ _ 1%R).
        assert (Et7: (1 == (inject_Q 1))%R) by reflexivity.
        rewrite Rplus_assoc. rewrite (Rplus_comm (-(1))%R).
        rewrite Rplus_opp_r. rewrite Rplus_0_r. rewrite Et7.
        rewrite <- inject_Q_plus. rewrite (Inject_2 _ Em2). auto. }
      assert (T4: (inject_Q q2 <= A2 )%R).
        { rewrite Hqz2. rewrite <- (Rmult_1_r A2).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em2))).
        assert (Et2: ((inject_Q (1 # Pos.of_nat m2)) == /
        exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em2).
          rewrite <- inject_Q_inv. reflexivity. } 
        remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R as Rden.
        clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m2)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m2) * (1 # Pos.of_nat m2) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m2) * / inject_Z (Z.pos (Pos.of_nat m2)) ==
                            inject_Z (Z.of_nat m2)  / inject_Z (Z.pos (Pos.of_nat m2))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rle_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m2))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m2)) > 0)).
          { rewrite (Inject_2 _ Em2). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z2) /
          inject_Z (Z.pos (Pos.of_nat m2)) * inject_Z (Z.pos (Pos.of_nat m2)) == 
          inject_Z (z2)).
          { field. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite Et5. rewrite (Inject_2 _ Em2). auto. }
      rewrite <- H5 in T3. rewrite <- H5 in T4.
      apply Ropp_le_compat in T2. apply Ropp_le_compat in T4.
      assert (inject_Q q1 + (- (inject_Q q2)) > A1 - inject_Q (1 # Pos.of_nat m1) + (-A1))%R.
      { apply Rlt_le_plus_compat. auto. auto. }
      assert (inject_Q q2 + (- (inject_Q q1)) > A1 - inject_Q (1 # Pos.of_nat m2) + (-A1))%R.
      { apply Rlt_le_plus_compat. auto. auto. }
      assert (Et1: (inject_Q q1 + - inject_Q q2== inject_Q (q1 - q2))%R).
      { rewrite <- inject_Q_opp. rewrite <- inject_Q_plus. reflexivity. }
      assert (Et2: (inject_Q q2 + - inject_Q q1== inject_Q (-(q1 - q2)))%R).
      { rewrite <- inject_Q_opp. rewrite <- inject_Q_plus.
        assert ((q2 + - q1)==- (q1 - q2)) by ring. rewrite H8. reflexivity. }
      assert (Et3: (A1 - inject_Q (1 # Pos.of_nat m1) + - A1 == - inject_Q (1 # Pos.of_nat m1))%R).
      { unfold Rminus. rewrite (Rplus_comm A1). rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity. }
      assert (Et4: (A1 - inject_Q (1 # Pos.of_nat m2) + - A1 == - inject_Q (1 # Pos.of_nat m2))%R).
      { unfold Rminus. rewrite (Rplus_comm A1). rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity. }
      rewrite Et1 in H6. rewrite Et2 in H7. rewrite Et3 in H6. rewrite Et4 in H7.
      clear Et1. clear Et2. clear Et3. clear Et4. unfold Rgt in H6,H7.
      rewrite <- inject_Q_opp in H6,H7.
      apply inject_Q_lt_inv in H6. apply inject_Q_lt_inv in H7.
      apply Qopp_lt_compat in H7. rewrite Qopp_involutive in H7,H7.
      rewrite <- Qmake_pos_inject_Z. split. auto. rewrite <- Qmake_pos_inject_Z. auto. auto. auto.
}

  assert (E2: eps > 1 / inject_Z (Z.of_nat (m2 - 1))).
  { apply Qlt_shift_div_r. apply Qinject_nat_pos. omega.
    apply (Qmult_lt_l _ _ _ (Qinv_lt_0_compat _ H)).
    assert (Et: / eps * (eps * inject_Z (Z.of_nat (m2-1))) == inject_Z (Z.of_nat (m2-1))).
      { field. intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
    rewrite Et. rewrite Qmult_1_r.
    assert (Et1: / eps <= inject_Z (Qceiling (1 / eps))).
      { assert (Et0: / eps == 1 / eps). { field.
        intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
        rewrite Et0. apply Qle_ceiling. }
    apply (Qle_lt_trans _ _ _ Et1).
    rewrite <- Zlt_Qlt.
    assert( Et2: (m2 - 1 + 1 = m2)%nat). { omega. }
    apply (Zplus_lt_reg_r _ _ (Z.of_nat 1)).
    rewrite <- Nat2Z.inj_add. rewrite Et2.
    assert (Et3: (0<=Qceiling (1 / eps))%Z).
    { rewrite Zle_Qle. apply Qlt_le_weak. apply (Qlt_le_trans _ (1/eps)).
      unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. auto.
      apply Qle_ceiling. }
    rewrite <- (Z2Nat.id (Qceiling (1 / eps))).
    rewrite Zplus_comm.
    rewrite <- Nat2Z.inj_add.
    rewrite <- Nat2Z.inj_lt.
    assert (Et4: 1%nat = (Z.to_nat 1)) by reflexivity.
    rewrite Et4.
    rewrite <- Z2Nat.inj_add.
    apply Nat.max_lub_lt_iff in H0.
    apply Nat.max_lub_lt_iff in H4.
    apply (proj2 H4). omega. auto. auto. }


  assert (E3: eps > 1 / inject_Z (Z.of_nat (m1 - 1))).
  { apply Qlt_shift_div_r. apply Qinject_nat_pos. omega.
    apply (Qmult_lt_l _ _ _ (Qinv_lt_0_compat _ H)).
    assert (Et: / eps * (eps * inject_Z (Z.of_nat (m1-1))) == inject_Z (Z.of_nat (m1-1))).
      { field. intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
    rewrite Et. rewrite Qmult_1_r.
    assert (Et1: / eps <= inject_Z (Qceiling (1 / eps))).
      { assert (Et0: / eps == 1 / eps). { field.
        intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
        rewrite Et0. apply Qle_ceiling. }
    apply (Qle_lt_trans _ _ _ Et1).
    rewrite <- Zlt_Qlt.
    assert( Et2: (m1 - 1 + 1 = m1)%nat). { omega. }
    apply (Zplus_lt_reg_r _ _ (Z.of_nat 1)).
    rewrite <- Nat2Z.inj_add. rewrite Et2.
    assert (Et3: (0<=Qceiling (1 / eps))%Z).
    { rewrite Zle_Qle. apply Qlt_le_weak. apply (Qlt_le_trans _ (1/eps)).
      unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. auto.
      apply Qle_ceiling. }
    rewrite <- (Z2Nat.id (Qceiling (1 / eps))).
    rewrite Zplus_comm.
    rewrite <- Nat2Z.inj_add.
    rewrite <- Nat2Z.inj_lt.
    assert (Et4: 1%nat = (Z.to_nat 1)) by reflexivity.
    rewrite Et4.
    rewrite <- Z2Nat.inj_add.
    apply Nat.max_lub_lt_iff in H0.
    apply Nat.max_lub_lt_iff in H4.
    apply (proj2 H0). omega. auto. auto. }
  destruct E1 as [E0 E1].
  assert (E4: Qabs(q1 - q2) <=  (1 / inject_Z (Z.of_nat m1))
              \/ Qabs (q1 - q2) <= (1 / inject_Z (Z.of_nat m2))).
  { destruct (classic (1/(inject_Z (Z.of_nat m1)) < (1/inject_Z (Z.of_nat m2)))).
    - right. apply Qabs_Qle_condition. split.
      + apply (Qle_trans _  (-(1 / inject_Z (Z.of_nat (m1))))).
        apply Qopp_le_compat. apply Qlt_le_weak. auto.
        apply Qlt_le_weak. auto.
      + apply Qlt_le_weak. auto.
    - left. apply Qabs_Qle_condition. apply Qnot_lt_le in H6. split.
      + apply Qlt_le_weak. auto.
      + apply (Qle_trans _  ((1 / inject_Z (Z.of_nat (m2))))).
        apply Qlt_le_weak. auto. auto. }

  assert (E5: 1 / inject_Z (Z.of_nat m1) < 1 / inject_Z (Z.of_nat (m1 - 1))).
    { apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat m1))). apply Qinject_nat_pos. omega.
      unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm  (/ inject_Z (Z.of_nat m1) )).
      rewrite Qmult_inv_r. rewrite Qmult_1_r.
      apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat (m1-1)))). apply Qinject_nat_pos. omega.
      rewrite Qmult_1_l. rewrite Qmult_1_l.
      rewrite Qmult_comm. rewrite Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_l.
      rewrite <- Zlt_Qlt. apply inj_lt. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m1 - 1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega. }

  assert (E6: 1 / inject_Z (Z.of_nat m2) < 1 / inject_Z (Z.of_nat (m2 - 1))).
    { apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat m2))). apply Qinject_nat_pos. omega.
      unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm  (/ inject_Z (Z.of_nat m2) )).
      rewrite Qmult_inv_r. rewrite Qmult_1_r.
      apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat (m2-1)))). apply Qinject_nat_pos. omega.
      rewrite Qmult_1_l. rewrite Qmult_1_l.
      rewrite Qmult_comm. rewrite Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_l.
      rewrite <- Zlt_Qlt. apply inj_lt. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m2 - 1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m2)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega. }
  destruct E4.
  * apply (Qle_lt_trans _ _ _ H6). apply (Qlt_trans _ _ _ E5).
    auto.
  * apply (Qle_lt_trans _ _ _ H6). apply (Qlt_trans _ _ _ E6).
    auto.
Qed.

Lemma Rabs_nonpositive: forall A : Real, ~(Rpositive A) -> (Rabs A == - A)%R.
Proof. intros. apply Rnot_positive in H. destruct H.
  rewrite (Rabs_negative _ H). reflexivity.
  rewrite H. rewrite Rabs_zero. rewrite <- Rzero_opp_zero. reflexivity.
Qed. 

