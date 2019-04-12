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
From CReal Require Import RBase_uncomp.

Lemma Qopp_le_compat_iff: forall p q, p<=q <-> -q <= -p.
Proof. split. apply Qopp_le_compat.
  intros. rewrite <- (Qopp_involutive q), <- (Qopp_involutive p).
  apply Qopp_le_compat. apply H.
Qed.

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

Theorem Real_positive_0_negative: forall A, 
 ( Rpositive A /\ ~(A==Rzero)%R  /\ ~ Rnegative A ) \/
 ( ~ Rpositive A /\ (A==Rzero)%R  /\ ~ Rnegative A ) \/
 ( ~ Rpositive A /\ ~(A==Rzero)%R  /\ Rnegative A ).
Proof. intros. assert (Case1: (A==Rzero)%R  \/ ~(A==Rzero)%R) by (apply classic).
  destruct Case1 as [Case1|Case2].
  - right. left. split.
    + destruct A as [A HA]. intros H. hnf in *. destruct H as [eps [Heps [N H]]].
      destruct (Case1 _ Heps) as [N1 HN1]. clear Case1.
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
    + split. auto.
      destruct A as [A HA]. intros H. hnf in *. destruct H as [eps [Heps [N H]]].
      destruct (Case1 _ Heps) as [N1 HN1]. clear Case1. unfold Ropp in H. unfold Cauchy_opp in H.
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
   - apply Real_not_zero_positive_or_negative in Case2. destruct Case2 as [Case2|Case3].
   + left. split. auto. split.
     * intros C. rewrite C in Case2. hnf in Case2. unfold Rzero in Case2.
       destruct Case2 as [eps0 [Heps0 [N HN]]].
       assert (nonsense: eps0 <=0). { apply (HN N). omega. reflexivity. }
       apply Qle_not_lt in nonsense. contradiction.
     * intros C. assert (E:Rpositive A /\ Rnegative A) by auto.
       apply Real_positive_not_negative in E. apply E.
   + right. right. split.
     * intros C. assert (E:Rpositive A /\ Rnegative A) by auto.
       apply Real_positive_not_negative in E. apply E.
     * split. { intros C. rewrite C in Case3. hnf in Case3. unfold Rzero in Case3.
       destruct Case3 as [eps0 [Heps0 [N HN]]].
       destruct A as [A HA]. unfold Ropp in HN. unfold Cauchy_opp in HN.
       destruct (Cauchy_exists _ HA N) as [qn Hqn].
       assert (nonsense: eps0 <= 0). { apply (HN N). 
       omega. intros. rewrite H. reflexivity. }
       apply Qle_not_lt in nonsense. contradiction. }
     { auto. }
Qed.

Definition Rlt (a b:Real) : Prop :=
  Rpositive (Rminus a b).




Notation "a < b" := (Rlt a b):Real_scope.