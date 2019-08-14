Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
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
From Coq Require Import Classes.Morphisms.
From CReal Require Import Dedekind.RBase.
From CReal Require Import Dedekind.ROrder.
From CReal Require Import Dedekind.RArith.
Require Import CReal.Cauchy.RBase.
Require Import CReal.Cauchy.ROrder.
From Coq Require Import PArith.BinPosDef.
Import Pos.
Require Import CReal.Iso.Cauchy2Dedekind.
Require Import CReal.Iso.Dedekind2Cauchy.
From Coq Require Import Psatz.

Theorem Bijection: forall x y,(D2C x==y)%C <->(C2D y==x)%D.
Proof.
  intros. split.
- intros. destruct x. destruct y.
  unfold D2C in H. hnf in H. unfold "==". split.
  + hnf. intros. destruct H2. destruct H2. destruct H3.
    specialize H with ((1#2)*x0). destruct H. lra.
    assert(exists q:Q,CSeq (x1+x2+1)%nat q). apply Cauchy_exists. auto.
    destruct H4.
    specialize H3 with (x1+x2+1)%nat x3.
    assert(x+x0<x3). apply H3. omega. auto.
    assert((exists N : Z,
       A (N # 2 ^ of_nat (x1+x2+1)%nat) /\ ~ A (N + 1 # 2 ^ of_nat (x1+x2+1)%nat))).
    apply Dcut_P . auto. destruct H6.
    specialize H with (x1+x2+1)%nat (x4 # 2 ^ of_nat (x1 + x2 + 1)) x3.
    assert(Qabs ((x4 # 2 ^ of_nat (x1 + x2 + 1)) - x3) < (1 # 2) * x0).
    apply H. omega. exists x4. split.
    apply H6. split. apply H6. reflexivity. apply H4.
    assert(x<=x4 # 2 ^ of_nat (x1 + x2 + 1)).
    assert(x3-(x4 # 2 ^ of_nat (x1 + x2 + 1))<(1 # 2) * x0).
    apply Qle_lt_trans with (Qabs ((x4 # 2 ^ of_nat (x1 + x2 + 1)) - x3)).
    assert(Qabs ((x4 # 2 ^ of_nat (x1 + x2 + 1)) - x3)==Qabs (x3-(x4 # 2 ^ of_nat (x1 + x2 + 1))))%Q.
    rewrite<-Qabs_opp. 
    assert(- ((x4 # 2 ^ of_nat (x1 + x2 + 1)) - x3)==x3 - (x4 # 2 ^ of_nat (x1 + x2 + 1)))%Q. lra.
    rewrite H8. reflexivity. rewrite H8. apply Qle_Qabs. auto. lra.
    destruct H0.
    apply Dedekind_properties2 with (x4 # 2 ^ of_nat (x1 + x2 + 1)).
    split. apply H6. apply H8.
  + hnf. intros.
    destruct H0.
    assert(exists r : Q, A r /\ x < r).  apply Dedekind_properties3.
    apply H2. destruct H0. destruct H0. exists ((1#4)*(x0-x)). split.
    lra. assert(exists q:Q,q==x0-x)%Q. exists (x0-x). reflexivity.
    destruct H4 as [eps H4].
    assert(exists n:nat,((2#1)/eps<=inject_Z(Z.of_nat n))).
    apply Inject_lemmas.inject_Z_of_nat_le. destruct H5.
    destruct H with ((1#4)*eps). lra.
    exists (x1+x2)%nat. intros. 
    assert(exists N : Z,
         A (N # 2 ^ of_nat n) /\ ~ A (N + 1 # 2 ^ of_nat n)).
    apply Dcut_P. split. auto. auto. auto. auto. destruct H9.
    assert(Qabs ((x3 # 2 ^ of_nat n)-p ) < (1#4)*eps).
    apply H6 with n. omega. exists x3. split.
    apply H9. split. apply H9. reflexivity. auto.
    assert(((x3 # 2 ^ of_nat n) - p) < (1 # 4) * eps)%Q.
    apply Qle_lt_trans with (Qabs ((x3 # 2 ^ of_nat n) - p)).
    apply Qle_Qabs. auto.
    assert(x0-(1#2)*eps<(x3 # 2 ^ of_nat n)).
    assert(x0<x3+1# 2 ^ of_nat n). apply Dcut_lt with A.
    split;auto;auto;auto;auto. auto. apply H9.
    assert(1# 2^of_nat n<(1#2)*eps).
    apply Qlt_le_trans with (1#of_nat n). apply power_compare2. omega.
    assert(exists q:Q,q==(1 # 2) * eps)%Q. exists ((1 # 2) * eps).
    reflexivity. destruct H13. rewrite<-H13.
    assert((2 # 1) / eps==1/x4)%Q.
    rewrite H13.
    field. lra.
    rewrite H14 in H5. 
    apply inject_compare with x1. lra. omega. auto.
    assert(x3 + 1 # 2 ^ of_nat n==(x3# 2 ^ of_nat n)+(1 # 2 ^ of_nat n))%Q.
    rewrite Qplus_sameden. reflexivity. rewrite H14 in H12.
    lra.
    lra.
- intros. destruct x,y. hnf. hnf in H. destruct H.
  hnf in H,H2. intros.
  assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#4)*eps).
  apply H1. lra. destruct H4.
  assert(exists n:nat,((2#1)/eps<=inject_Z(Z.of_nat n))).
  apply Inject_lemmas.inject_Z_of_nat_le.
  destruct H5 as [t P].            
  exists (x+t+1)%nat. intros.
  destruct H6. destruct H6. destruct H8.
  apply H2 in H6.
  destruct H6. destruct H6. destruct H10.
  assert(exists q:Q,CSeq (x+x2+1)%nat q) by apply H1. destruct H11.
  assert((x0 # 2 ^ of_nat m) + x1 < x3). apply H10 with (x+x2+1)%nat.
  omega. auto. assert(Qabs (q2 - x3) < (1 # 4) * eps) . apply H4 with m (x+x2+1)%nat.
  omega. omega. auto. auto.
  specialize H with (x0 + 1 # 2 ^ of_nat m).
  assert(~((exists t : Q,
       0 < t /\
       (exists N : nat,
          forall (n : nat) (p : Q),
          (n > N)%nat -> CSeq n p -> (x0 + 1 # 2 ^ of_nat m) + t < p)))).
  unfold not. intros. apply H8. apply H. auto.
  
  assert(~(q1+(1#(2^ (of_nat m)))+((1#2)*eps))<q2)%Q.
  unfold not. intros. apply H14.
  exists ((1#4)*eps). split. lra.
  
  
  exists (x+t+m)%nat.
  intros.
  rewrite<-Qplus_sameden. rewrite<-H9.
  apply Qlt_le_trans with (q2-(1#4)*eps). lra.
  assert(q2-p<(1#4)*eps).
  apply Qle_lt_trans with (Qabs(q2-p)).
  apply Qle_Qabs. apply H4 with m n. omega. omega. auto. auto. 
  assert((1 # 2 ^ of_nat m)<(1#2)*eps).
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
    assert(exists q:Q,q==(1 # 2) * eps)%Q. exists ((1 # 2) * eps).
    reflexivity. destruct H19. rewrite<-H19.
    assert((2 # 1) / eps==1/x4)%Q.
    rewrite H19.
    field. lra.
    rewrite H20 in P. 
    apply inject_compare with t. lra. omega. auto. lra.
  assert((1 # 2 ^ of_nat m)<(1#2)*eps).
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
    assert(exists q:Q,q==(1 # 2) * eps)%Q. exists ((1 # 2) * eps).
    reflexivity. destruct H16. rewrite<-H16.
    assert((2 # 1) / eps==1/x4)%Q.
    rewrite H16.
    field. lra.
    rewrite H17 in P. 
    apply inject_compare with t. lra. omega. auto.
  assert(q2<q1+eps). lra.
  assert(q1<q2+(1#4)*eps). 
  assert(x3-q2<(1#4)*eps).
  apply Qle_lt_trans with (Qabs (q2 - x3)).
  rewrite<-Qabs_opp. assert(- (q2 - x3)==x3-q2)%Q.
  lra. rewrite H18. apply Qle_Qabs. auto. lra.
  apply QArith_base_ext.Qabs_Qlt_condition. split.
  lra. lra.
Qed.
