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

Lemma Rnot_positive: forall A, ~ (Rpositive A) -> (Rnegative A) \/ (A==0)%R.
Proof. intros. destruct (classic (A==0)%R).
  - right. auto.
  - left. destruct (classic (Rnegative A)). auto.
    destruct (Real_positive_0_negative A).
    + destruct H2. contradiction.
    + destruct H2. * destruct H2. destruct H3. contradiction.
      * destruct H2. destruct H3. auto.
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








(*


Definition SingletonSet2Element (A:{X: nat -> Real -> Prop| (forall n x1 x2, X n x1 ->
 X n x2 -> x1 == x2) /\ (forall n, exists x, X n x) /\ forall n, Proper (Real_equiv ==> iff) (X n)
 /\ (Cauchy_Criterion X)}%R
) : Real.
Admitted.
Definition Rel2Func: {f:Real->Real->Prop|(forall x1 x2 y1 y2,
 f x1 y1 -> f x2 y2 -> x1 == x2 -> y1 == y2)
/\ (forall x, exists y, f x y)
/\ (Proper (Real_equiv ==> Real_equiv ==> iff) f)}%R ->
(Real -> Real).


*)

