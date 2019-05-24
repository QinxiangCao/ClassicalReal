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
Module C1:=Cauchy.RBase.
Module C2:=Cauchy.ROrder.
Module D1 := Dedekind.RBase.
Module D2 := Dedekind.ROrder.
Module D3 := Dedekind.RArith.
Bind Scope CReal_Scope with Cauchy.RBase.Real.
Delimit Scope CReal_Scope with C.

Bind Scope DReal_Scope with Dedekind.RBase.Real.
Delimit Scope DReal_Scope with D.
Local Open Scope DReal_Scope.

Notation "a == b" :=(D2.Req a b):DReal_Scope.
Notation "a + b" :=(D3.Rplus a b):DReal_Scope.
Notation "a * b" :=(D3.Rmult a b):DReal_Scope.
Notation "a == b" :=(C1.Real_equiv a b):CReal_Scope.
Notation "a + b" :=(C1.Rplus a b):CReal_Scope.
Notation "a * b" :=(C1.Rmult a b):CReal_Scope.
Lemma Z_1_mult: forall(a:Z),(1*a=a)%Z.
Proof.
  intros. simpl. induction a. omega. omega. omega.
Qed.
Lemma mult_lt_0:forall (a b :Q),0<a->0<b->0<a*b.
Proof.
  intros. unfold Qlt in *. simpl in *.
  rewrite Zmult_comm in*.  rewrite Z_1_mult in *.
  assert(0=Qnum a*0)%Z. rewrite Zmult_comm. reflexivity. rewrite H1.
  apply Zmult_lt_compat_l . auto. auto.
Qed.

Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (fun q=>exists (t:Q),(t>0)%Q/\(exists(N:nat),forall (n:nat)(p:Q),(n>N)%nat->CSeq n p->(q+t<p)%Q)).
Proof.
  intros. split.
- split.
  + assert(Cauchy CSeq ->exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    apply CauchySeqBounded_weak. assert(exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    { apply H0. apply H. } destruct H1. destruct H1. exists (-x0-1)%Q.
    exists 1. split. unfold Qlt. simpl. omega. exists (S x). intros. assert(Qabs p<x0). apply H1 with n.
    omega. auto. assert(p==--p)%Q.  { rewrite Qopp_opp. reflexivity. }
    rewrite H5. assert(-x0-1+1==-x0)%Q.
    { unfold Qminus. rewrite<-Qplus_assoc. rewrite Qplus_comm. 
      assert(-(1)+1==0)%Q. rewrite Qplus_comm.  apply Qplus_opp_r.
      rewrite H6. apply Qplus_0_l. } rewrite H6.
     apply QArith_base_ext.Qopp_lt_compat.
    apply Qle_lt_trans with (Qabs p). rewrite<-Qabs_opp. apply Qle_Qabs.
    apply H4. 
  + assert(Cauchy CSeq ->exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    apply CauchySeqBounded_weak. assert(exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    { apply H0. apply H. } destruct H1. destruct H1. exists x0.
    unfold not. intros. destruct H2. destruct H2. destruct H3. destruct H.
    assert( exists q : Q, CSeq (x+x2+1)%nat q).
    apply Cauchy_exists. destruct H.
    assert( x0+x1<x3). apply H3 with (x+x2+1)%nat. omega. apply H. 
    assert(Qabs x3<x0). apply H1 with(x+x2+1)%nat. omega. auto.
    apply Qlt_irrefl with x0. apply Qlt_le_trans with x3.
    apply Qlt_le_trans with (x0+x1)%Q. rewrite Qplus_comm.
    assert(x0==0+x0)%Q. rewrite Qplus_0_l. reflexivity.
    rewrite H6. apply Qplus_lt_le_compat. apply H2. rewrite Qplus_0_l.
    apply Qle_refl. apply Qlt_le_weak. apply H4.  
    apply QOrderedType.QOrder.le_trans with (Qabs x3).
    apply Qle_Qabs. apply Qlt_le_weak. apply H5.
- intros. destruct H0. destruct H0. destruct H0. exists x. split.
  apply H0. destruct H2. exists x0. intros. assert (p + x < p0).
  apply H2 with n. auto. auto. apply QOrderedType.QOrder.le_lt_trans with (p+x)%Q.
  apply Qplus_le_compat. apply H1. apply Qle_refl. apply H5.
- intros. destruct H0. destruct H0. destruct H1. exists(p+(x*(1#2)))%Q.
  split.
    + exists (x*(1#2))%Q. split.
      unfold Qlt. simpl. unfold Qlt in H0. simpl in H0.
      assert(Qnum x * 1=Qnum x)%Z. omega. rewrite H2. apply H0.
      exists x0. intros. assert(p+x<p0)%Q. apply H1 with n.
      auto. auto. assert(x * (1 # 2) + x * (1 # 2)==x)%Q.
      rewrite<-Qmult_plus_distr_r. assert((1 # 2) + (1 # 2)==1)%Q.
      unfold Qplus. simpl. unfold Qeq. simpl. reflexivity. rewrite H5.
      apply Qmult_1_r. rewrite<-Qplus_assoc. rewrite H5. apply H4.
    + rewrite Qplus_comm. assert(p==0+p)%Q. rewrite Qplus_0_l. reflexivity.
    rewrite H2. apply Qplus_lt_le_compat. 
    unfold Qlt.  simpl. unfold Qlt in H0. simpl in H0.  assert(Qnum x * 1=Qnum x)%Z. omega. 
    rewrite H3.  apply H0. rewrite <-H2. apply Qle_refl. 
- intros. destruct H1. destruct H1. destruct H2. exists x. split.
  apply H1. exists x0. intros. rewrite<-H0. apply H2 with n. omega. auto.
Qed.

Definition C2D (A:C1.Real):D1.Real :=
match A with
|Real_intro CSeq H =>
Real_cons (fun q=>exists (t:Q),(t>0)%Q/\(exists(N:nat),forall (n:nat)(p:Q),(n>N)%nat->CSeq n p->(q+t<p)%Q))(Dedekind_CSeq CSeq H) end.

Theorem C2D_properity1:forall (x y:C1.Real),
  ( (C2D x)+(C2D y)==C2D (x+y))%D.
Proof.
  intros. destruct x. destruct y. unfold "=="%D. split.
- unfold Rle. unfold "+"%D. simpl. intros. destruct H1.
  destruct H1. destruct H1. destruct H1. destruct H1. destruct H2.
  destruct H2. destruct H2.  exists (x2+x3)%Q.
  split. assert(0==0+0)%Q. symmetry. apply Qplus_0_r. rewrite H6.
  apply Qplus_lt_le_compat. apply H1. apply Qlt_le_weak. apply H2.
  destruct H3. destruct H5. exists (x4+x5)%nat. intros. unfold C1.CauchySeqPlus in H7.
  destruct H. destruct H0. destruct Cauchy_exists with n. destruct Cauchy_exists0 with n.
  assert(p==x6+x7)%Q. apply H7. auto. auto. rewrite H8. rewrite<-H4. 
  assert(x0 + x2 < x6)%Q. apply H3 with n.
  apply Nat.le_lt_trans with (x4+x5)%nat.
  apply le_plus_l. apply H6. auto.
  assert(x1 + x3 < x7)%Q. apply H5 with n.
  apply Nat.le_lt_trans with (x4+x5)%nat.
  apply le_plus_r. apply H6. auto.
  rewrite Qplus_assoc. rewrite Qplus_comm. rewrite Qplus_assoc.
  assert(x0 + x1==x1+x0)%Q. rewrite Qplus_comm. reflexivity.
  rewrite H11. rewrite Qplus_assoc.
  assert(x3 + x1 + x0 + x2==(x3+x1)+(x0+x2))%Q.
  symmetry. rewrite Qplus_assoc. reflexivity. rewrite H12.
  rewrite Qplus_comm. apply Qplus_lt_le_compat. auto.
  rewrite Qplus_comm. apply Qlt_le_weak. auto.
- unfold Rle. unfold "+"%D. simpl. intros. unfold D3.Cut_plus_Cut.
  destruct H1. destruct H1. 
  (*destruct H. destruct H0. destruct H2.
  unfold CauchySeqPlus in *. exists ((1#2)*x)%Q,((1#2)*x)%Q.
  split. exists ((1#2)*x0)%Q. split. apply H1. exists x1. intros.
 destruct Cauchy_exists with x1. 
  destruct Cauchy_exists0 with x1.*)
Theorem C2D_properity2:forall (x y:C1.Real),
  ((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.

Admitted.
Lemma Qminus_Qplus:forall(a b c:Q),a<=b+c<->a-b<=c.
Proof.
  intros. split.
- intros. unfold Qminus. assert(a + -b<= b + c +-b).
  { Search Qle Qplus. apply Qplus_le_compat. auto. apply Qle_refl. }
  assert(b+ c+ -b==c)%Q. rewrite Qplus_comm. rewrite Qplus_assoc.
  rewrite Qplus_comm. assert(-b+b==0)%Q. rewrite Qplus_comm. apply Qplus_opp_r.
  rewrite H1. Search Qplus 0. apply Qplus_0_r. rewrite<-H1. auto.
- intros. unfold Qminus in H. assert(a + -b +b<= c+b).
  apply Qplus_le_compat. auto. apply Qle_refl.
  rewrite Qplus_comm. assert( a + - b + b==a)%Q.
  assert(- b + b ==0)%Q. rewrite Qplus_comm. apply Qplus_opp_r.
  rewrite<-Qplus_assoc. rewrite H1. apply Qplus_0_r.
  rewrite <-H1. auto.
Qed.
  
Theorem C2D_properity3:forall (x y:C1.Real),
(x==y)%C->  ((C2D x)==(C2D y)).
Proof.
intros.
unfold "==". split. 
- unfold D2.Rle. destruct x. destruct y. unfold C2D. unfold C1.Real_equiv in H.
  intros. destruct H2. destruct H2. destruct H3. destruct H with ((1#2)*x0)%Q.
  apply mult_lt_0. reflexivity. auto. exists ((1#2)*x0)%Q. split.
  apply mult_lt_0. reflexivity. auto. exists (x1+x2)%nat. intros. destruct H0.
  destruct Cauchy_exists with n. assert(x + x0 < x3). apply H3 with n.
  apply Nat.le_lt_trans with (x1+x2)%nat. omega. apply H5. apply H0.
  assert(Qabs(x3-p)<(1 # 2) * x0). apply H4 with n. apply Nat.le_lt_trans with (x1+x2)%nat. omega.
  apply H5. auto. auto. assert(x3 -(1#2)*x0<=p). 
  assert(x3-p<=(1 # 2) * x0). Search Qle "trans". 
  apply QOrderedType.QOrder.le_trans with (Qabs (x3 - p)).
  apply Qle_Qabs. apply Qlt_le_weak. auto. rewrite<-Qminus_Qplus.
  rewrite<-Qminus_Qplus in H9. rewrite Qplus_comm. auto.
  rewrite<- Qminus_Qplus in H9. assert(x + x0 <(1 # 2) * x0 + p).
  apply QOrderedType.QOrder.lt_le_trans with x3. auto.
  auto. assert(x + (1 # 2) * x0 +(1 # 2) * x0< p+(1 # 2) * x0).
  rewrite<- Qplus_assoc. assert(p + (1 # 2) * x0==(1 # 2) * x0+p)%Q.
  apply Qplus_comm. assert((1 # 2) * x0 + (1 # 2) * x0==x0)%Q.
  rewrite<- Qmult_plus_distr_l. assert((1 # 2) + (1 # 2)==1)%Q.
  reflexivity. rewrite H12. apply Qmult_1_l. rewrite H12. auto. 
  rewrite H11. auto. apply Qplus_lt_l with ((1 # 2) * x0)%Q.
  auto.
- unfold D2.Rle. destruct x. destruct y. unfold C2D. unfold C1.Real_equiv in H.
  intros. destruct H2. destruct H2. destruct H3. destruct H with ((1#2)*x0)%Q.
  apply mult_lt_0. reflexivity. auto. exists ((1#2)*x0)%Q. split.
  apply mult_lt_0. reflexivity. auto. exists (x1+x2)%nat. intros. destruct H1.
  destruct Cauchy_exists with n. assert(x + x0 < x3). apply H3 with n.
  apply Nat.le_lt_trans with (x1+x2)%nat. omega. apply H5. apply H1.
  assert(Qabs(p-x3)<(1 # 2) * x0). apply H4 with n. apply Nat.le_lt_trans with (x1+x2)%nat. omega.
  apply H5. auto. auto. assert(x3 -(1#2)*x0<=p). 
  assert(x3-p<=(1 # 2) * x0). Search Qle "trans". 
  apply QOrderedType.QOrder.le_trans with (Qabs (x3 - p)).
  apply Qle_Qabs. rewrite Qabs_Qminus. apply Qlt_le_weak. auto. rewrite<-Qminus_Qplus.
  rewrite<-Qminus_Qplus in H9. rewrite Qplus_comm. auto.
  rewrite<- Qminus_Qplus in H9. assert(x + x0 <(1 # 2) * x0 + p).
  apply QOrderedType.QOrder.lt_le_trans with x3. auto.
  auto. assert(x + (1 # 2) * x0 +(1 # 2) * x0< p+(1 # 2) * x0).
  rewrite<- Qplus_assoc. assert(p+ (1 # 2) * x0==(1 # 2) * x0+p)%Q.
  apply Qplus_comm. assert((1 # 2) * x0 + (1 # 2) * x0==x0)%Q.
  rewrite<- Qmult_plus_distr_l. assert((1 # 2) + (1 # 2)==1)%Q.
  reflexivity. rewrite H12. apply Qmult_1_l. rewrite H12. 
  rewrite H11. auto. apply Qplus_lt_l with ((1 # 2) * x0)%Q.
  auto.
Qed.

