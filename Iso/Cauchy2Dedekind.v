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
From CReal Require Import Cauchy.RBase.
From CReal Require Import Cauchy.RArith.
From CReal Require Import Cauchy.ROrder.
From CReal Require Import Cauchy.RAbs.
From CReal Require Import Cauchy.RComplete.
From CReal Require Import Cauchy.RFloor.
From CReal Require Import Cauchy.RFunc.
From Coq Require Import PArith.BinPosDef.
From Coq Require Import Psatz.
Import Pos.

Module C1:= Cauchy.RBase.
Module C2 := Cauchy.ROrder.
Module C3 := Cauchy.RArith.
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
Notation "a + b" :=(C3.Rplus a b):CReal_Scope.
Notation "a * b" :=(C3.Rmult a b):CReal_Scope.
Notation "a - b" :=(D3.Rminus a b):DReal_Scope.
Notation "a - b" :=(C3.Rminus a b):CReal_Scope.
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
Definition C2D_Seqpre(CSeq:nat->Q->Prop):Q->Prop:=
fun q=>(exists (t:Q),(t>0)%Q/\(exists(N:nat),forall (n:nat)(p:Q),(n>N)%nat->CSeq n p->(q+t<p)%Q)).
Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (C2D_Seqpre CSeq).
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
Real_cons (C2D_Seqpre CSeq)(Dedekind_CSeq CSeq H) end.

Theorem C2D_property1:forall (x y:C1.Real),
  ( (C2D x)+(C2D y)==C2D (x+y))%D.
Proof.
  intros. destruct x. destruct y. unfold "=="%D. split.
- unfold Rle. unfold "+"%D. simpl. intros. destruct H1.
  destruct H1. destruct H1. destruct H1. destruct H1. destruct H2.
  destruct H2. destruct H2.  exists (x2+x3)%Q.
  split. assert(0==0+0)%Q. symmetry. apply Qplus_0_r. rewrite H6.
  apply Qplus_lt_le_compat. apply H1. apply Qlt_le_weak. apply H2.
  destruct H3. destruct H5. exists (x4+x5)%nat. intros. unfold C3.CauchySeqPlus in H7.
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
  destruct H. assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q,
               CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#4)*x0).
  apply Cauchy_def. apply mult_lt_0. reflexivity. apply H1.
  destruct H0. assert(exists n : nat,
                forall m1 m2 : nat,
                (m1 > n)%nat ->
                (m2 > n)%nat ->
                forall q1 q2 : Q,
                CSeq0 m1 q1 -> CSeq0 m2 q2 -> Qabs (q1 - q2) < (1#4)*x0).
  apply Cauchy_def0. apply mult_lt_0. reflexivity. auto.
  destruct H. destruct H0. destruct H2.
  assert(exists q : Q, CSeq (x1+x2+x3+1)%nat q).
  apply Cauchy_exists. destruct H3.
  assert(exists q : Q, CSeq0 (x1+x2+x3+1)%nat q).
  apply Cauchy_exists0. destruct H4. exists (x4-(1#2)*x0)%Q,(x-x4+(1#2)*x0)%Q.
  split.
    + exists ((1#4)*x0)%Q. split. apply mult_lt_0. reflexivity.
      auto. exists (x1+x2+x3)%nat. intros. 
      assert(Qabs (x4 - p) < (1 # 4) * x0).
      apply H with (x1 + x2 +x3 + 1)%nat n. omega.
      apply Nat.le_lt_trans with (x1+x2+x3)%nat. omega. auto. auto. auto.
      assert((x4 - p) < (1 # 4) * x0).
      apply QOrderedType.QOrder.le_lt_trans with (Qabs (x4 - p)).
      apply Qle_Qabs. apply H7.
      assert(x4 - (1#2)*x0 + (1 # 4) * x0==x4-(1 # 4) * x0)%Q.
      assert(- ((1 # 2) * x0)==((-(1#2))*x0))%Q. 
      assert( forall (a b:Q),-(a)*b==-(a*b))%Q.
        intros. unfold Qmult. simpl. unfold Qeq. simpl. rewrite Z.mul_opp_l. reflexivity.
      symmetry. apply H9.
       unfold Qminus. rewrite H9. rewrite<-Qplus_assoc.
       rewrite<-Qmult_plus_distr_l. assert((- (1#2) + (1 # 4))==-(1#4))%Q.
        reflexivity. rewrite H10. assert(- (1 # 4) * x0==- ((1 # 4) * x0))%Q.
        assert( forall (a b:Q),-(a)*b==-(a*b))%Q.
        intros. unfold Qmult. simpl. unfold Qeq. simpl. rewrite Z.mul_opp_l. reflexivity.
        apply H11. rewrite H11. reflexivity. rewrite H9. 
        rewrite Qlt_minus_iff. rewrite Qlt_minus_iff in H8.
        assert(forall (a b:Q),-(a-b)==-a+b)%Q.
        intros. unfold Qminus. assert((a + - b)+ - (a + - b) == (a + - b)- a + b)%Q.
        rewrite Qplus_opp_r. symmetry.
        rewrite Qplus_comm. assert((a + - b - a)==-b)%Q.
         unfold Qminus. rewrite<- Qplus_assoc. rewrite Qplus_comm .
        rewrite <-Qplus_assoc. rewrite Qplus_comm .  assert(- a + a ==0)%Q.
        rewrite Qplus_comm. apply Qplus_opp_r. rewrite H10.
        apply Qplus_0_l. rewrite H10. apply Qplus_opp_r. apply Qplus_inj_l with (a + - b )%Q.
        rewrite H10. unfold Qminus. rewrite Qplus_assoc. reflexivity.
        rewrite H10. rewrite H10 in H8. rewrite Qplus_assoc in H8. rewrite Qplus_comm.
        assert( - x4 + (1 # 4) * x0 ==(1 # 4) * x0 + - x4)%Q.
        rewrite Qplus_comm . reflexivity. rewrite H11. apply H8.
    + split.
        * exists ((1#4)*x0)%Q. split.  apply mult_lt_0. reflexivity.
      auto. exists (x1+x2+x3)%nat. intros. apply Qlt_trans with ( x4+x5 -x0- x4 + (1#2)*x0 + (1 # 4) * x0 )%Q.
      unfold Qminus.  
      apply Qplus_lt_l.
      apply Qplus_lt_l.  apply Qplus_lt_l. 
      assert(x+x0<x4+x5)%Q. apply H2 with (x1+x2+x3+1)%nat.
      omega. unfold C3.CauchySeqPlus. intros.
      assert(x4==q1)%Q. apply Cauchy_unique with (x1+x2+x3+1)%nat.
      apply H3. apply H7. assert(x5==q2)%Q. apply Cauchy_unique0 with (x1+x2+x3+1)%nat.
      apply H4. apply H8. rewrite H9. rewrite H10. reflexivity.
      assert(x +x0< x4 + x5 + - x0+x0)%Q.
      rewrite <-Qplus_assoc. assert(- x0 + x0==0)%Q.
      rewrite Qplus_comm. apply Qplus_opp_r. rewrite H8.
      rewrite<-Qplus_assoc. rewrite Qplus_0_r. auto.
      apply Qplus_lt_l with x0. auto.
      assert(x4 + x5 - x0 - x4 + (1 # 2) * x0 + (1 # 4) * x0==x5-(1 # 4) * x0)%Q.
      unfold Qminus. assert(x4 + x5==x5+x4)%Q. symmetry. apply Qplus_comm.
      rewrite H7. rewrite <-Qplus_assoc. rewrite<-Qmult_plus_distr_l.
      assert(((1 # 2) + (1 # 4))==3#4)%Q. reflexivity.
      rewrite H8. assert(x5 + x4 + - x0 + - x4==x5 +-x0)%Q. 
      assert(- x0==x4 + - x0 + - x4)%Q.
      rewrite <-Qplus_comm. rewrite Qplus_assoc.
      assert( - x4 + x4 ==0)%Q. rewrite Qplus_comm.
      apply Qplus_opp_r. rewrite H9. rewrite Qplus_comm.
      symmetry. apply Qplus_0_r.
      assert(x5 + x4 + - x0 + - x4==x5 + (x4 + - x0 + - x4))%Q.
      rewrite Qplus_assoc. rewrite Qplus_assoc. reflexivity.
      rewrite H10. rewrite<-H9. reflexivity. rewrite H9.
      assert(- x0==-(1)*x0)%Q. reflexivity. rewrite H10.
      rewrite<-Qplus_assoc. rewrite<-Qmult_plus_distr_l.
      assert(- (1) + (3 # 4)==-(1#4))%Q. reflexivity.
      rewrite H11. assert(- (1 # 4) * x0==- ((1 # 4) * x0))%Q.
        assert( forall (a b:Q),-(a)*b==-(a*b))%Q.
        intros. unfold Qmult. simpl. unfold Qeq. simpl. rewrite Z.mul_opp_l. reflexivity.
      apply H12. rewrite H12. reflexivity. rewrite H7.
      assert(Qabs (x5 - p) < (1 # 4) * x0).
      apply H0 with (x1 + x2 +x3 + 1)%nat n. omega.
      apply Nat.le_lt_trans with (x1+x2+x3)%nat. omega. auto. auto. auto.
      assert((x5 - p) < (1 # 4) * x0).
      apply QOrderedType.QOrder.le_lt_trans with (Qabs (x5 - p)).
      apply Qle_Qabs. apply H8.
      assert(x5 - (1#2)*x0 + (1 # 4) * x0==x5-(1 # 4) * x0)%Q.
      assert(- ((1 # 2) * x0)==((-(1#2))*x0))%Q. 
      assert( forall (a b:Q),-(a)*b==-(a*b))%Q.
        intros. unfold Qmult. simpl. unfold Qeq. simpl. rewrite Z.mul_opp_l. reflexivity.
      symmetry. apply H10.
       unfold Qminus. rewrite H10. rewrite<-Qplus_assoc.
       rewrite<-Qmult_plus_distr_l. assert((- (1#2) + (1 # 4))==-(1#4))%Q.
        reflexivity. rewrite H11. assert(- (1 # 4) * x0==- ((1 # 4) * x0))%Q.
        assert( forall (a b:Q),-(a)*b==-(a*b))%Q.
        intros. unfold Qmult. simpl. unfold Qeq. simpl. rewrite Z.mul_opp_l. reflexivity.
        apply H12. rewrite H12. reflexivity. rewrite<- H10. 
        rewrite Qlt_minus_iff. rewrite Qlt_minus_iff in H9.
        assert(forall (a b:Q),-(a-b)==-a+b)%Q.
        intros. unfold Qminus. assert((a + - b)+ - (a + - b) == (a + - b)- a + b)%Q.
        rewrite Qplus_opp_r. symmetry.
        rewrite Qplus_comm. assert((a + - b - a)==-b)%Q.
         unfold Qminus. rewrite<- Qplus_assoc. rewrite Qplus_comm .
        rewrite <-Qplus_assoc. rewrite Qplus_comm .  assert(- a + a ==0)%Q.
        rewrite Qplus_comm. apply Qplus_opp_r. rewrite H11.
        apply Qplus_0_l. rewrite H11. apply Qplus_opp_r. apply Qplus_inj_l with (a + - b )%Q.
        rewrite H11. unfold Qminus. rewrite Qplus_assoc. reflexivity.
        rewrite H10. rewrite H11 in H9. rewrite Qplus_assoc in H9. rewrite Qplus_comm.
        assert( - x4 + (1 # 4) * x0 ==(1 # 4) * x0 + - x4)%Q.
        rewrite Qplus_comm . reflexivity. rewrite H11. 
        rewrite Qplus_comm. rewrite Qplus_assoc.
        rewrite Qplus_comm. assert((p + - x5)==(-x5+p))%Q.
        apply Qplus_comm. rewrite H13. rewrite Qplus_assoc.
         apply H9.
    * unfold Qminus. assert((x + - x4 + (1 # 2) * x0)==(1 # 2) * x0+-x4+x)%Q.
      rewrite<- Qplus_assoc. rewrite Qplus_comm. assert(- x4 + (1 # 2) * x0==(1 # 2) * x0+-x4)%Q.
      apply Qplus_comm. rewrite H5. reflexivity. rewrite H5.
      rewrite Qplus_assoc. rewrite Qplus_comm.
      assert((x4 + - ((1 # 2) * x0) + ((1 # 2) * x0 + - x4)==0))%Q.
      rewrite Qplus_assoc. rewrite Qplus_comm. rewrite<- Qplus_assoc.  
      assert((- ((1 # 2) * x0) + (1 # 2) * x0)==0)%Q.
      rewrite Qplus_comm. apply Qplus_opp_r. rewrite H6.
      rewrite Qplus_comm. rewrite Qplus_0_r. apply Qplus_opp_r.
      rewrite H6. apply Qplus_0_r.
Qed.

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
Theorem C2D_property3:forall (x y:C1.Real),
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
  assert(x3-p<=(1 # 2) * x0). apply QOrderedType.QOrder.le_trans with (Qabs (x3 - p)).
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

Notation "- a" :=(Ropp a):CReal_Scope. 
Notation "- a" :=(Dedekind.RArith.Ropp a):DReal_Scope.
Theorem C2D_property6:C2D (0%R)==RBase.Rzero.
Proof.
  hnf. split.
  - hnf. intros. destruct H. destruct H. destruct H0.
    assert(x+x0<0)%Q. apply H0 with (x1+1)%nat . omega. reflexivity.
    lra.
  - hnf. intros. exists ((-1#2)*x)%Q. split. lra.
    exists 0%nat. intros. rewrite H1. lra.
Qed.
Theorem C2D_property7:forall (x:C1.Real), C2D (-x)==-C2D x.
Proof.
  intros. assert(C2D (-x)+C2D x==-C2D x +C2D x).
  rewrite C2D_property1.
  assert(- x + x==Rzero)%C. rewrite C3.Rplus_comm. rewrite C3.Rplus_opp_r. reflexivity.
  assert(C2D(-x+x)==C2D(0%R))%D. apply C2D_property3. auto.
  rewrite H0. rewrite D3.Rplus_comm. rewrite D3.Rplus_opp.
  apply C2D_property6.
  rewrite D3.Rplus_comm in H. symmetry in H. rewrite D3.Rplus_comm in H.
  apply D3.Rplus_compat_l with (C2D x). symmetry. auto.
Qed.
Definition C2D_preop(x:C1.Real):=match x with Real_intro Seq H=>C2D_Seqpre Seq end.
Lemma Qsmall :forall (a b:Q),0<a->0<b->exists (q:Q),0<q/\q<=a/\q<=b.
Proof.
intros. assert(a<b\/~a<b) by apply classic. destruct H1.
+ exists a. split. lra. split. lra. lra.
+ exists b. split. lra. split. lra. lra.
Qed.

Lemma C2D_Rmultlemma1:forall(x y:C1.Real),PP (C2D_preop x)(C2D_preop y)->((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros. split.
  - destruct x,y. hnf. simpl. simpl in H.
  unfold Cut_mult. intros. destruct H2.
  + unfold CauchySeqMult. destruct H. destruct H2. 
  hnf in*. destruct H. destruct H. destruct H5. destruct H3.
  destruct H3. destruct H6. destruct H2. hnf in H2,H7.
  destruct H2. destruct H2. destruct H8. destruct H7.
  destruct H7. destruct H9. destruct H4. destruct H4.
  destruct H4.  destruct H10. destruct H11.
  destruct H12. hnf in H12,H11. destruct H11. destruct H11.
  destruct H12. destruct H12. destruct H14. destruct H15. 
  exists (x10*x11)%Q. split.
    apply QArith_base_ext.Qlt_mult0. 
    lra. auto. auto.
    assert(    exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#2)*x10).
    apply Cauchy_def. auto. lra.
    assert(    exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq0 m1 q1 -> CSeq0 m2 q2 -> Qabs (q1 - q2) < (1#2)*x11).
    apply Cauchy_def. auto. lra. destruct H17,H16.
    exists (x12+x13+x14+x15)%nat. intros.
    assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto. destruct H20.
    assert(exists q:Q,CSeq0 n q). apply Cauchy_exists. auto. destruct H21.
    assert(p==x16*x17)%Q. apply H19. auto. auto. rewrite H22.
    apply Qle_lt_trans with (x8*x9 +x10 * x11)%Q. lra.
    assert(x8+x10<x16). apply H14 with n. lia. auto.
    assert(x9+x11<x17). apply H15 with n. lia. auto.
    apply Qlt_trans with ((x8 + x10)*(x9 + x11))%Q. rewrite Qmult_plus_distr_l.
    rewrite Qmult_plus_distr_r. rewrite Qmult_plus_distr_r.
    rewrite Qplus_assoc. assert(0<x8*x11). apply QArith_base_ext.Qlt_mult0.
    auto. auto. assert(0<x10*x9). apply QArith_base_ext.Qlt_mult0.
    auto. auto. lra. apply QArith_base_ext.Qmult_lt_compat_nonneg. 
    lra. lra. auto. auto.
  + destruct H2.
    ++ destruct H2. hnf in H2. hnf in H.
    destruct H2. assert False. hnf in H2. destruct H2.
    destruct H2. apply H5. destruct H. 
    assert(Dedekind (C2D_Seqpre CSeq)).
    { apply Dedekind_CSeq. auto. }
    apply Dedekind_properties2 with 0. auto. split.
    auto. lra. destruct H5.
    ++ destruct H2.
    +++ destruct H2. hnf in H2. hnf in H.
    destruct H2. assert False. hnf in H4. destruct H4.
    destruct H4. apply H5. destruct H. 
    assert(Dedekind (C2D_Seqpre CSeq0)).
    { apply Dedekind_CSeq. auto. }
    apply Dedekind_properties2 with 0. auto. split.
    auto. lra. destruct H5.
    +++ destruct H2.
    ++++ destruct H2. hnf in H2. hnf in H.
    destruct H2. assert False. hnf in H2. destruct H2.
    destruct H2. apply H5. destruct H. 
    assert(Dedekind (C2D_Seqpre CSeq)).
    { apply Dedekind_CSeq. auto. }
    apply Dedekind_properties2 with 0. auto. split.
    auto. lra. destruct H5.
    ++++ destruct H2. hnf in H2. hnf in H.
    destruct H2.
    +++++ assert False. destruct H2. apply H2. apply H.
    destruct H4.
    +++++ assert False. destruct H2. apply H2. apply H.
    destruct H4.
  - destruct x,y. hnf. simpl. simpl in H.
  unfold Cut_mult. intros. left. split. 
  + auto.
  + hnf. hnf in*. destruct H. destruct H2. destruct H2. destruct H4.
    unfold CauchySeqMult in H4. hnf in H,H3. destruct H. destruct H. destruct H5. destruct H3. destruct H3. destruct H6.
    assert(exists n : nat,forall m1 m2 : nat,(m1 > n)%nat ->(m2 > n)%nat ->
forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) <(1#4)*x2)%Q as P1.
    { apply Cauchy_def. auto. lra. }
    assert(exists n : nat,forall m1 m2 : nat,(m1 > n)%nat ->(m2 > n)%nat ->
forall q1 q2 : Q, CSeq0 m1 q1 -> CSeq0 m2 q2 -> Qabs (q1 - q2) <(1#4)*x4)%Q as P2.
    { apply Cauchy_def. auto. lra. } destruct P1 as [a1 P1]. destruct P2 as [b1 P2].
    
    assert(exists q:Q,CSeq (x1+x3+x5+a1+b1+1)%nat q). apply Cauchy_exists. auto.
    assert(exists q:Q,CSeq0 (x1+x3+x5+a1+b1+1)%nat q). apply Cauchy_exists. auto.
    destruct H7. destruct H8.
    assert(exists q:Q,0<q/\q<=x2/\q<=(1#2)*x0/(x7+x4))%Q. { apply Qsmall. lra.
    apply Qlt_shift_div_l.  assert(0+x4<x7)%Q. apply H6 with (x1 + x3 + x5+a1+b1 + 1)%nat. lia. auto. lra.
    lra. } destruct H9.
    assert(exists q:Q,0<q/\q<=x4/\q<=(1#2)*x0/(x6+x2))%Q. { apply Qsmall. lra.
    apply Qlt_shift_div_l.  assert(0+x2<x6)%Q. apply H5 with (x1 + x3 + x5+a1+b1 + 1)%nat. lia. auto. lra.
    lra. } destruct H10.
    assert(exists n : nat,forall m1 m2 : nat,(m1 > n)%nat ->(m2 > n)%nat ->
forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#2)*x8)%Q as P3.
    { apply Cauchy_def. auto. lra. }
    assert(exists n : nat,forall m1 m2 : nat,(m1 > n)%nat ->(m2 > n)%nat ->
forall q1 q2 : Q, CSeq0 m1 q1 -> CSeq0 m2 q2 -> Qabs (q1 - q2) <(1#2)* x9)%Q as P4.
    { apply Cauchy_def. auto. lra. } destruct P3 as [a2 P3]. destruct P4 as [b2 P4].
    assert(exists q:Q,CSeq (x1+x3+x5+a1+b1+a2+b2+1)%nat q). apply Cauchy_exists. auto.
    assert(exists q:Q,CSeq0 (x1+x3+x5+a1+b1+a2+b2+1)%nat q). apply Cauchy_exists. auto.
    destruct H11,H12.
    exists (x10-x8)%Q,(x11-x9)%Q. split. 
    { assert(0+x2<x10). apply H5 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
    lia. auto. lra. }
    split.
    { assert(0+x4<x11). apply H6 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
    lia. auto. lra. }
    split.
    { hnf. exists ((1#2)*x8)%Q. split. lra. exists a2. intros.
    assert( Qabs(x10 -p)<(1 # 2) * x8)%Q. apply P3 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat n.
    lia. lia. auto. auto. assert((x10 - p) < (1 # 2) * x8)%Q. apply Qle_lt_trans with (Qabs(x10 -p))%Q.
    apply Qle_Qabs. auto. lra. }
    split.
    { hnf. exists ((1#2)*x9)%Q. split. lra. exists b2. intros.
    assert( Qabs(x11 -p)<(1 # 2) * x9)%Q. apply P4 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat n.
    lia. lia. auto. auto. assert((x11 - p) < (1 # 2) * x9)%Q. apply Qle_lt_trans with (Qabs(x11 -p))%Q.
    apply Qle_Qabs. auto. lra. }
    assert(x+x0<x10*x11)%Q. apply H4 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
    ++ lia. 
    ++ intros. assert(x10==q1)%Q. apply Cauchy_unique with CSeq (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
     auto. auto. auto. assert(x11==q2)%Q. apply Cauchy_unique with CSeq0 (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
     auto. auto. auto. rewrite H15. rewrite H16. reflexivity.
    ++ apply Qle_trans with (x10*x11-x0)%Q. lra. apply Qle_trans with 
    (x10*x11-x10*x9-x8*x11)%Q. 
    +++ assert(x10 * x9 + x8 * x11<=x0)%Q.
     { assert(x10 * x9 <=(1#2)*x0)%Q.
     { assert(x10<x6+x2)%Q. assert(x10-x6<(1#4)*x2)%Q. apply Qle_lt_trans with (Qabs(x10-x6))%Q.
       apply Qle_Qabs. apply P1 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat (x1 + x3 + x5 + a1 + b1 + 1)%nat.
       lia. lia. auto. auto. lra. apply Qle_trans with (((1 # 2) * x0 / (x6 + x2))*x10)%Q.
       rewrite Qmult_comm. apply Qmult_le_compat_r. lra.
       assert(0+x2<x10)%Q. apply H5 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
       lia. auto. lra. unfold Qdiv. assert((1 # 2) * x0==(1 # 2) * x0*1)%Q. lra. rewrite H15.
       assert((1 # 2) * x0 *1 / (x6 + x2) * x10==((1 # 2) * x0) *(1* / (x6 + x2) * x10))%Q.
       { unfold Qdiv. lra. } rewrite H16. apply QArith_base_ext.Qmult_le_compat_l.
       rewrite Qmult_1_l. rewrite Qmult_comm. assert(x10 * / (x6 + x2)==x10 / (x6 + x2))%Q.
       reflexivity. rewrite H17. apply Qlt_le_weak. apply Qlt_shift_div_r.
       assert(0+x2<x6)%Q. apply H5 with (x1 + x3 + x5 +a1+b1 +1)%nat. lia. auto.
       lra. lra. lra.
      } 
     assert (x8 * x11 <=(1#2)*x0)%Q.
     { rewrite Qmult_comm. assert(x11<x7+x4)%Q. assert(x11-x7<(1#4)*x4)%Q. apply Qle_lt_trans with (Qabs(x11-x7))%Q.
       apply Qle_Qabs. apply P2 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat (x1 + x3 + x5 + a1 + b1 + 1)%nat.
       lia. lia. auto. auto. lra. apply Qle_trans with (((1 # 2) * x0 / (x7 + x4))*x11)%Q.
       rewrite Qmult_comm. apply Qmult_le_compat_r. lra.
       assert(0+x4<x11)%Q. apply H6 with (x1 + x3 + x5 + a1 + b1 + a2 + b2 + 1)%nat.
       lia. auto. lra. unfold Qdiv. assert((1 # 2) * x0==(1 # 2) * x0*1)%Q. lra. rewrite H16.
       assert((1 # 2) * x0 *1 / (x7 + x4) * x11==((1 # 2) * x0) *(1* / (x7 + x4) * x11))%Q.
       { unfold Qdiv. lra. } rewrite H17. apply QArith_base_ext.Qmult_le_compat_l.
       rewrite Qmult_1_l. rewrite Qmult_comm. assert(x11 * / (x7 + x4)==x11 / (x7 + x4))%Q.
       reflexivity. rewrite H18. apply Qlt_le_weak. apply Qlt_shift_div_r.
       assert(0+x4<x7)%Q. apply H6 with (x1 + x3 + x5 +a1+b1 +1)%nat. lia. auto.
       lra. lra. lra. } 
     lra. }
     lra.
    +++ unfold Qminus. rewrite Qmult_plus_distr_r. rewrite Qmult_plus_distr_l.
    rewrite Qmult_plus_distr_l. rewrite Qplus_assoc.
    assert(x10*x9==x9*x10)%Q by apply Qmult_comm.  rewrite H14. rewrite QArith_base_ext.Qmult_opp_assoc_l.
    assert(x8*x11==x11*x8)%Q by apply Qmult_comm.  rewrite H15. rewrite QArith_base_ext.Qmult_opp_assoc_l.
    assert(0<(- x8 * - x9))%Q. Search Qmult 0%Q Qlt. rewrite<- QArith_base_ext.Qmult_opp_assoc_l.
    rewrite Qmult_comm. rewrite <-QArith_base_ext.Qmult_opp_assoc_l. rewrite Qopp_opp. 
    apply mult_lt_0. lra. lra. lra. 
Qed.
    
Lemma C2D_Rmultlemma2:forall(x y:C1.Real),NP (C2D_preop x)(C2D_preop y)->((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros.
  assert(- (C2D x * C2D y) == -C2D (x * y))%D.
  - rewrite D3.Rmult_opp_l. rewrite<- C2D_property7.
  rewrite<- C2D_property7. assert(C2D (- (x * y))==C2D ( (-x) * y))%D.
  + apply C2D_property3. ring.
  + rewrite H0. apply C2D_Rmultlemma1. split.
  ++ destruct H. destruct x. hnf in H. hnf. destruct H.
  destruct H. exists ((1#4)*x)%Q. split.
  +++ lra.
  +++ unfold C2D_preop in H3. unfold C2D_Seqpre in H3.
  unfold Cauchy_opp. rewrite D2.not_exists_dist in H3.
  specialize H3 with ((1#2)*x)%Q. apply not_and_or in H3.
  destruct H3.
  ++++ lra.
  ++++ rewrite D2.not_exists_dist in H3. 
  assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#4)*x).
  apply Cauchy_def. auto. lra. destruct H4.
  specialize H3 with x0%nat.
  exists x0%nat. intros. assert(exists q:Q, CSeq n q). apply Cauchy_exists. 
  auto. destruct H7. apply H6 in H7. rewrite H7.
  assert(0 + (1 # 4) * x < - x1\/~0 + (1 # 4) * x < - x1) by apply classic.
  destruct H8.
  +++++ auto.
  +++++ assert False. { apply H3. intros. specialize H4 with n n0 (-p)%Q p0.
  assert(Qabs (- p - p0) < (1 # 4) * x)%Q.  apply H4. auto. auto. 
  assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto. destruct H11.
  apply Cauchy_proper with  x2. assert(p==-x2)%Q. apply H6. auto. lra.
  auto. auto. rewrite H7 in H11.
  rewrite QArith_base_ext.Qabs_Qlt_condition in H11. destruct H11. lra. }
  destruct H9.
  ++ apply H.
  - rewrite D3.Ropp_opp. rewrite H0. rewrite<-D3.Ropp_opp. reflexivity.
Qed.
Lemma C2D_Rmultlemma3:forall(x y:C1.Real),PN (C2D_preop x)(C2D_preop y)->((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros.
  assert(- (C2D y * C2D x) == -C2D (y * x))%D.
  - rewrite D3.Rmult_opp_l. rewrite<- C2D_property7.
  rewrite<- C2D_property7. assert(C2D (- (y * x))==C2D ( (-y) * x))%D.
  + apply C2D_property3. ring.
  + rewrite H0. apply C2D_Rmultlemma1. split.
  ++ destruct H. destruct y. hnf in H1. hnf. destruct H1.
  destruct H1. exists ((1#4)*x0)%Q. split.
  +++ lra.
  +++ unfold C2D_preop in H3. unfold C2D_Seqpre in H3.
  unfold Cauchy_opp. rewrite D2.not_exists_dist in H3.
  specialize H3 with ((1#2)*x0)%Q. apply not_and_or in H3.
  destruct H3.
  ++++ lra.
  ++++ rewrite D2.not_exists_dist in H3. 
  assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#4)*x0).
  apply Cauchy_def. auto. lra. destruct H4.
  specialize H3 with x1%nat.
  exists x1%nat. intros. assert(exists q:Q, CSeq n q). apply Cauchy_exists. 
  auto. destruct H7. apply H6 in H7. rewrite H7.
  assert(0 + (1 # 4) * x0 < - x2\/~0 + (1 # 4) * x0 < - x2) by apply classic.
  destruct H8.
  +++++ auto.
  +++++ assert False. { apply H3. intros. specialize H4 with n n0 (-p)%Q p0.
  assert(Qabs (- p - p0) < (1 # 4) * x0)%Q.  apply H4. auto. auto. 
  assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto. destruct H11.
  apply Cauchy_proper with  x3. assert(p==-x3)%Q. apply H6. auto. lra.
  auto. auto. rewrite H7 in H11.
  rewrite QArith_base_ext.Qabs_Qlt_condition in H11. destruct H11. lra. }
  destruct H9.
  ++ apply H.
  - rewrite D3.Rmult_comm. rewrite D3.Ropp_opp. rewrite H0. rewrite<-D3.Ropp_opp. apply C2D_property3.
  rewrite C3.Rmult_comm. reflexivity.
Qed.
Lemma C2D_Rmultlemma4:forall(x y:C1.Real),NN (C2D_preop x)(C2D_preop y)->((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros.
  assert(-(C2D x * C2D y) == -C2D (x * y))%D.
  - rewrite D3.Rmult_opp_l. rewrite<- C2D_property7.
  rewrite<- C2D_property7. assert(C2D (- (x * y))==C2D ( (-x) * y))%D.
  + apply C2D_property3. ring.
  + rewrite H0. apply C2D_Rmultlemma3. split.
  ++ destruct H. destruct x. hnf in H. hnf. destruct H.
  destruct H. exists ((1#4)*x)%Q. split.
  +++ lra.
  +++ unfold C2D_preop in H3. unfold C2D_Seqpre in H3.
  unfold Cauchy_opp. rewrite D2.not_exists_dist in H3.
  specialize H3 with ((1#2)*x)%Q. apply not_and_or in H3.
  destruct H3.
  ++++ lra.
  ++++ rewrite D2.not_exists_dist in H3. 
  assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) < (1#4)*x).
  apply Cauchy_def. auto. lra. destruct H4.
  specialize H3 with x0%nat.
  exists x0%nat. intros. assert(exists q:Q, CSeq n q). apply Cauchy_exists. 
  auto. destruct H7. apply H6 in H7. rewrite H7.
  assert(0 + (1 # 4) * x < - x1\/~0 + (1 # 4) * x < - x1) by apply classic.
  destruct H8.
  +++++ auto.
  +++++ assert False. { apply H3. intros. specialize H4 with n n0 (-p)%Q p0.
  assert(Qabs (- p - p0) < (1 # 4) * x)%Q.  apply H4. auto. auto. 
  assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto. destruct H11.
  apply Cauchy_proper with  x2. assert(p==-x2)%Q. apply H6. auto. lra.
  auto. auto. rewrite H7 in H11.
  rewrite QArith_base_ext.Qabs_Qlt_condition in H11. destruct H11. lra. }
  destruct H9.
  ++ apply H.
  - rewrite D3.Ropp_opp. rewrite H0. rewrite<-D3.Ropp_opp. reflexivity.
Qed.
Lemma closetozero: forall (CSeq:nat->Q->Prop),Cauchy CSeq->(~ C2D_Seqpre CSeq 0 /\ ~ D3.Cut_opp (C2D_Seqpre CSeq) 0)->
(forall(q:Q),0<q->exists (N:nat),forall(n:nat)(p:Q),(N<n)%nat->CSeq n p->Qabs p<=q).
Proof.
  intros CSeq P H q. intros. destruct H.
  assert(exists N : nat, forall (n : nat) (p : Q), (N < n)%nat -> CSeq n p ->p <= q).
  { unfold C2D_Seqpre in H. rewrite D2.not_exists_dist in H. specialize H with ((1#2)*q)%Q.
    apply not_and_or in H. destruct H.
    - assert False. apply H. lra;destruct H2. destruct H2.
    - rewrite D2.not_exists_dist in H.
    assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) <(1#2)*q)%Q.
     apply Cauchy_def. auto. lra. destruct H2.
     specialize H with x%nat.
      exists x%nat. intros.
     unfold not in H. assert(p<=q\/~p<=q)%Q by apply classic.
     destruct H5.
     + auto.
     + assert False. 
     { apply H. intros. assert(Qabs (p - p0) < (1 # 2) * q)%Q.
     apply H2 with n n0. auto. auto. auto. auto. 
     assert(p-p0<(1 # 2) * q)%Q. apply Qle_lt_trans with (Qabs(p-p0)).
     apply Qle_Qabs. auto. lra. } destruct H6. }
  assert(exists N : nat, forall (n : nat) (p : Q), (N < n)%nat -> CSeq n p ->-q<=p).
  { unfold Cut_opp in H1. unfold C2D_Seqpre in H1.
  assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q, CSeq m1 q1 -> CSeq m2 q2 -> Qabs (q1 - q2) <(1#2)*q)%Q.
     apply Cauchy_def. auto. lra. destruct H3. exists x. intros.
  assert(- q <= p\/~- q <= p)by apply classic. destruct H6.
  - auto.
  - assert False. { apply H1. exists ((1 # 2) * q)%Q. split.
  lra. unfold not. intros. destruct H7. destruct H7. destruct H8.
  assert(exists q:Q,CSeq (x+x1+1)%nat q).  apply Cauchy_exists. auto.
  destruct H9. assert(- 0 + - ((1 # 2) * q) + x0 < x2)%Q.
  apply H8 with (x + x1 + 1)%nat. lia. auto.
  assert(x2-p<(1 # 2) * q)%Q. apply Qle_lt_trans with (Qabs(x2-p)).
  apply Qle_Qabs. apply H3 with (x+x1+1)%nat n. lia. auto. auto. auto.
  lra. } destruct H7. }
  destruct H2,H3.
  exists(x+x0)%nat.
  intros. apply Qabs_Qle_condition. split.
  - apply H3 with n. lia. auto.
  - apply H2 with n. lia. auto. 
Qed.
Lemma Qmult_compare:forall(a b c d:Q),0<=a->0<=b->0<c->a<=c->b<d->a*b<c*d.
Proof.
  intros. apply Qle_lt_or_eq in H2. destruct H2.
  - apply QArith_base_ext.Qmult_lt_compat_nonneg. auto.
  auto. auto.  auto.
  - rewrite H2. rewrite Qmult_comm.
  assert(c*d==d*c)%Q. 
  { rewrite Qmult_comm. reflexivity. } rewrite H4.
  apply Qmult_lt_compat_r. auto.
  auto.
Qed. 
Lemma C2D_Rmultlemma5:forall(x y:C1.Real),O (C2D_preop x)(C2D_preop y)->((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros. destruct H.
  + destruct H. split.
  ++ destruct x,y.  hnf. intros. hnf in H3. simpl in H. simpl in H0.
    destruct H3 as [|[|[|[|]]]].
  +++ destruct H3. hnf in H3. assert False.
  { apply H. apply H3. } destruct H5.
  +++ destruct H3. hnf in H3. assert False.
  { apply H0. apply H3. } destruct H5.
  +++ destruct H3. hnf in H3. assert False.
  { apply H. apply H3. } destruct H5.
  +++ destruct H3. assert False.
  { apply H0. destruct H3. apply H3. } destruct H5.
  +++ (* main branch  *)
  destruct H3 as [AbortH H3]. 
  hnf. unfold CauchySeqMult. unfold C2D_Seqpre in H,H0,H3.
  unfold Cut_mult0 in H3. unfold Cut_opp in H0.
  rewrite D2.not_exists_dist in H.
  rewrite D2.not_exists_dist in H0. 
  exists ((1#2)*(-x))%Q. split.
  - lra.
  - assert(exists M : Q, 0 < M /\ (forall (n : nat) (q : Q), CSeq0 n q -> Qabs q < M)).
    { apply CauchySeqBounded. auto. } destruct H4. destruct H4.
    assert(exists (N:nat),forall (n:nat)(q:Q),(N<n)%nat->CSeq n q->
    Qabs q<=(-(1#2)*x/x0)).
    { apply closetozero. auto. split. rewrite<- D2.not_exists_dist in H. auto.
      rewrite<- D2.not_exists_dist in H0. auto.  assert(0 < - (1 # 2) * x )%Q. 
      lra. apply Qlt_shift_div_l. auto. lra. }
    destruct H6. exists x1. intros.
    assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto.
    assert(exists q:Q,CSeq0 n q). apply Cauchy_exists. auto.
    destruct H9,H10.
    assert(p == x2 * x3)%Q. { apply H8. auto. auto. } rewrite H11.
    assert(Qabs x3<x0)%Q. { apply H5 with n. auto. }
    assert(Qabs x2 <= - (1 # 2) * x / x0)%Q. { apply H6 with n. auto. auto. }
    apply Qlt_le_trans with (-Qabs(x2*x3))%Q.
   -- assert((Qabs x2)*(Qabs x3)<(- (1 # 2) * x / x0)*x0)%Q.
      { apply Qmult_compare. apply Qabs_nonneg. apply Qabs_nonneg.
      apply Qlt_shift_div_l. lra. lra. auto. auto. } rewrite<-Qabs_Qmult in H14.
      assert(- (1 # 2) * x / x0 * x0==- (1 # 2) * x )%Q. { field. lra. }
      rewrite H15 in H14. assert(x + (1 # 2) * - x ==(1 # 2) * x)%Q. lra.
      rewrite H16. lra. 
   -- assert(-(x2 * x3)<=Qabs (-(x2 * x3)))%Q.  apply Qle_Qabs.
      rewrite Qabs_opp in H14. lra.
  ++ destruct x,y.  hnf. intros. hnf. hnf in H3. simpl in H. simpl in H0.
    right. right. right. right. split.
  +++ left. split;auto;auto.
  +++ unfold Cut_mult0. destruct H3. destruct H3. destruct H4.
    unfold CauchySeqMult in H4. 
    assert(forall(q:Q),0<q->exists (N:nat),forall(n:nat)(p:Q),(N<n)%nat->CSeq n p->Qabs p<=q)%Q.
    { apply closetozero. auto. 
     split;auto;auto. }
    assert(exists M : Q, 0 < M /\ (forall (n : nat) (q : Q), CSeq0 n q -> Qabs q < M)). apply CauchySeqBounded. auto.
    destruct H6. destruct H6.
    assert(exists N : nat, forall (n : nat) (p : Q), (N < n)%nat -> CSeq n p -> Qabs p <= (1#2)*x0/x2).
    { apply H5. apply Qlt_shift_div_l. auto. lra. }
    destruct H8.
    assert(exists q:Q,CSeq (x1+x3+1)%nat q). { apply Cauchy_exists. auto. }
    assert(exists q:Q,CSeq0 (x1+x3+1)%nat q). { apply Cauchy_exists. auto. }
    destruct H9,H10. assert(x + x0 < x4*x5)%Q. 
    { apply H4 with (x1+x3+1)%nat. lia. intros. assert(x4==q1)%Q. apply Cauchy_unique with CSeq (x1+x3+1)%nat.
    auto. auto. auto. assert(x5==q2)%Q. apply Cauchy_unique with CSeq0 (x1+x3+1)%nat.
    auto. auto. auto. rewrite H13,H14. reflexivity. }
    assert(x4*x5<(1#2)*x0)%Q. { assert(Qabs x4 <= (1 # 2) * x0 / x2)%Q. apply H8 with (x1+x3+1)%nat.
    lia. auto. assert(Qabs x5 <  x2 )%Q. apply H7 with (x1+x3+1)%nat . auto. apply Qle_lt_trans with (Qabs(x4*x5)).
    apply Qle_Qabs. rewrite Qabs_Qmult. assert((1 # 2) * x0==((1 # 2) * x0/x2)*x2)%Q.
    field. lra. rewrite H14. apply Qmult_compare. apply Qabs_nonneg. apply Qabs_nonneg.
      apply Qlt_shift_div_l. lra. lra. auto. auto. }
    lra.
  + destruct H. split.
  ++ destruct x,y.  hnf. intros. hnf in H3. simpl in H. simpl in H0.
    destruct H3 as [|[|[|[|]]]].
  +++ destruct H3. hnf in H3. assert False.
  { apply H. apply H3. } destruct H5.
  +++ destruct H3. hnf in H3. assert False.
  { apply H. apply H3. } destruct H5.
  +++ destruct H3. hnf in H3. assert False.
  { apply H0. apply H3. } destruct H5.
  +++ destruct H3. assert False.
  { destruct H3. apply H0.  apply H5. } destruct H5.
  +++ (* main branch  *)
  destruct H3 as [AbortH H3]. 
  hnf. unfold CauchySeqMult. unfold C2D_Seqpre in H,H0,H3.
  unfold Cut_mult0 in H3. unfold Cut_opp in H0.
  rewrite D2.not_exists_dist in H.
  rewrite D2.not_exists_dist in H0. 
  exists ((1#2)*(-x))%Q. split.
  - lra.
  - assert(exists M : Q, 0 < M /\ (forall (n : nat) (q : Q), CSeq n q -> Qabs q < M)).
    { apply CauchySeqBounded. auto. } destruct H4. destruct H4.
    assert(exists (N:nat),forall (n:nat)(q:Q),(N<n)%nat->CSeq0 n q->
    Qabs q<=(-(1#2)*x/x0)).
    { apply closetozero. auto. split. rewrite<- D2.not_exists_dist in H. auto.
      rewrite<- D2.not_exists_dist in H0. auto.  assert(0 < - (1 # 2) * x )%Q. 
      lra. apply Qlt_shift_div_l. auto. lra. }
    destruct H6. exists x1. intros.
    assert(exists q:Q,CSeq0 n q). apply Cauchy_exists. auto.
    assert(exists q:Q,CSeq n q). apply Cauchy_exists. auto.
    destruct H9,H10.
    assert(p == x3 * x2)%Q. { apply H8. auto. auto. } rewrite H11.
    assert(Qabs x3<x0)%Q. { apply H5 with n. auto. }
    assert(Qabs x2 <= - (1 # 2) * x / x0)%Q. { apply H6 with n. auto. auto. }
    apply Qlt_le_trans with (-Qabs(x2*x3))%Q.
   -- assert((Qabs x2)*(Qabs x3)<(- (1 # 2) * x / x0)*x0)%Q.
      { apply Qmult_compare. apply Qabs_nonneg. apply Qabs_nonneg.
      apply Qlt_shift_div_l. lra. lra. auto. auto. } rewrite<-Qabs_Qmult in H14.
      assert(- (1 # 2) * x / x0 * x0==- (1 # 2) * x )%Q. { field. lra. }
      rewrite H15 in H14. assert(x + (1 # 2) * - x ==(1 # 2) * x)%Q. lra.
      rewrite H16. lra. 
   -- assert(-(x2 * x3)<=Qabs (-(x2 * x3)))%Q.  apply Qle_Qabs.
      rewrite Qabs_opp in H14. lra.
  ++ destruct x,y.  hnf. intros. hnf. hnf in H3. simpl in H. simpl in H0.
    right. right. right. right. split.
  +++ right. split;auto;auto.
  +++ unfold Cut_mult0. destruct H3. destruct H3. destruct H4.
    unfold CauchySeqMult in H4. 
    assert(forall(q:Q),0<q->exists (N:nat),forall(n:nat)(p:Q),(N<n)%nat->CSeq0 n p->Qabs p<=q)%Q.
    { apply closetozero. auto. split;auto;auto. }
    assert(exists M : Q, 0 < M /\ (forall (n : nat) (q : Q), CSeq n q -> Qabs q < M)). apply CauchySeqBounded. auto.
    destruct H6. destruct H6.
    assert(exists N : nat, forall (n : nat) (p : Q), (N < n)%nat -> CSeq0 n p -> Qabs p <= (1#2)*x0/x2).
    { apply H5. apply Qlt_shift_div_l. auto. lra. }
    destruct H8.
    assert(exists q:Q,CSeq0 (x1+x3+1)%nat q). { apply Cauchy_exists. auto. }
    assert(exists q:Q,CSeq (x1+x3+1)%nat q). { apply Cauchy_exists. auto. }
    destruct H9,H10. assert(x + x0 < x5*x4)%Q. 
    { apply H4 with (x1+x3+1)%nat. lia. intros. assert(x5==q1)%Q. apply Cauchy_unique with CSeq (x1+x3+1)%nat.
    auto. auto. auto. assert(x4==q2)%Q. apply Cauchy_unique with CSeq0 (x1+x3+1)%nat.
    auto. auto. auto. rewrite H13,H14. reflexivity. }
    assert(x5*x4<(1#2)*x0)%Q. { assert(Qabs x4 <= (1 # 2) * x0 / x2)%Q. apply H8 with (x1+x3+1)%nat.
    lia. auto. assert(Qabs x5 <  x2 )%Q. apply H7 with (x1+x3+1)%nat . auto. apply Qle_lt_trans with (Qabs(x4*x5)).
    rewrite Qmult_comm. apply Qle_Qabs. rewrite Qabs_Qmult. assert((1 # 2) * x0==((1 # 2) * x0/x2)*x2)%Q.
    field. lra. rewrite H14. apply Qmult_compare. apply Qabs_nonneg. apply Qabs_nonneg.
      apply Qlt_shift_div_l. lra. lra. auto. auto. }
    lra. 
Qed.
Theorem C2D_property2:forall (x y:C1.Real),
  ((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
  intros.
  assert(PP (C2D_preop x)(C2D_preop y)\/NP (C2D_preop x)(C2D_preop y)\/PN (C2D_preop x)(C2D_preop y)\/NN (C2D_preop x)(C2D_preop y)\/O (C2D_preop x)(C2D_preop y)).
  apply Rmult_situation. destruct x. apply Dedekind_CSeq. auto. destruct y.
  apply Dedekind_CSeq. auto.
  destruct H. apply C2D_Rmultlemma1. auto. destruct H.
  apply C2D_Rmultlemma2. auto. destruct H. 
  apply C2D_Rmultlemma3. auto. destruct H.
  apply C2D_Rmultlemma4. auto. apply C2D_Rmultlemma5. auto.
Qed.

Notation "a <= b" :=(Rle a b):CReal_Scope.
Notation "a < b" :=(Rlt a b):CReal_Scope.
Notation "a <= b" :=(Dedekind.ROrder.Rle a b):DReal_Scope.
Notation "a < b" :=(Dedekind.ROrder.Rlt a b):DReal_Scope.

Theorem C2D_property4:forall (x y:C1.Real),
(x<y)%C->  ((C2D x)<(C2D y)).
Proof.
  intros. hnf. destruct x,y. simpl.
  split.
  - intros. destruct H2. destruct H2. destruct H3.
    hnf in H. destruct H. destruct H. destruct H4.
    simpl in H4. unfold CauchySeqPlus,Cauchy_opp in H4.
    exists x0. split. auto. exists(x1+x3)%nat.
    intros.
    assert(exists (t:Q),CSeq  n t). apply H0. destruct H7.
    assert(x+x0<x4)%Q. apply H3 with n. omega. apply H7.
    assert(x4<=p)%Q. 
    assert(x2<=(p-x4))%Q. apply H4 with n. omega.
    intros. assert(q2==-x4)%Q. apply H10. auto.
    rewrite H11. unfold Qminus. assert(p==q1)%Q.
    apply Cauchy_unique with CSeq0 n. auto.
    auto. auto. rewrite H12. reflexivity.
    assert(0<=(p-x4))%Q. lra.
    apply Qle_minus_iff. unfold Qminus in H10. auto.
    apply Qlt_le_trans with x4. auto. auto.
  - hnf in*. simpl in H. destruct H. destruct H.
    destruct H2. unfold CauchySeqPlus,Cauchy_opp in H2.
    assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q,
               CSeq m1 q1 -> CSeq m2 q2 -> (Qabs (q1 - q2) < (1#4)*x))%Q.
    apply H0. lra. destruct H3.
    assert(exists n : nat,
               forall m1 m2 : nat,
               (m1 > n)%nat ->
               (m2 > n)%nat ->
               forall q1 q2 : Q,
               CSeq0 m1 q1 -> CSeq0 m2 q2 -> (Qabs (q1 - q2) < (1#4)*x))%Q.
    apply H1. lra. destruct H4.
    assert(exists q:Q,CSeq0 (x0+x1+x2+1)%nat q) by apply H1.
    destruct H5. exists(x3-(1#2)*x)%Q. split.
    + exists ((1#4)*x)%Q. split. lra. exists (x0+x1+x2)%nat.
      intros. assert(x3 - (1 # 2) * x + (1 # 4) * x==x3-(1#4)*x)%Q.
      lra. rewrite H8.
      assert(Qabs(x3-p)<(1#4)*x)%Q.
      apply H4 with (x0+x1+x2+1)%nat n.
      lia. lia. auto. auto.
      assert(x3<p+(1#4)*x)%Q. 
      assert(x3-p<=Qabs (x3 - p))%Q. apply Qle_Qabs.
      assert(x3-p<(1 # 2) * x)%Q. lra. lra.
      lra.
    + unfold not. intros. destruct H6. destruct H6. destruct H7.
      assert(exists q:Q,CSeq (x0+x1+x2+x5+1)%nat q) by apply H0.
      destruct H8. assert(x3 - (1 # 2) * x + x4 < x6)%Q.
      apply H7 with (x0+x1+x2+x5+1)%nat . lia. auto.
      assert(exists q:Q, CSeq (x0+x1+x2+1)%nat q)%Q.
      apply H0. destruct H10.
      assert(Qabs(x7-x6)<(1#4)*x)%Q.
      apply H3 with (x0+x1+x2+1)%nat (x0+x1+x2+x5+1)%nat.
      lia. lia. auto. auto.
      assert(x6-x7<=Qabs (x6 - x7))%Q. apply Qle_Qabs.
      assert(Qabs(x6-x7)==Qabs(x7-x6))%Q.
      rewrite<- Qabs_opp. assert(- (x6 - x7)==x7-x6)%Q. lra.
      rewrite H13. reflexivity.
      assert(x6-x7<(1 # 4) * x)%Q. lra.
      assert(x<=x3-x7)%Q. apply H2 with (x0+x1+x2+1)%nat.
      lia. intros. assert(q2==-x7)%Q. apply H16. auto.
      rewrite H17. assert(x3==q1)%Q.
      apply Cauchy_unique with CSeq0 (x0 + x1 + x2 + 1)%nat.
      auto. auto. auto. lra.
      assert(x6+x<x3+(1 # 4) * x)%Q. lra.
      assert(x3-(1#2)*x<x6)%Q by lra.
      assert(x6+(3#4)*x<x3)%Q by lra.
      assert(x3 - (1 # 2) * x <x3-(1 # 2) * x)%Q by lra.
      apply QOrderedType.QOrder.lt_irrefl with (x3 - (1 # 2) * x )%Q.
      auto.
Qed.   
Theorem C2D_property5:forall (x y:C1.Real),
(x<=y)%C->  ((C2D x)<=(C2D y)).
Proof.
  intros. unfold Rle in H. destruct H.
  - assert(C2D x < C2D y). apply C2D_property4. apply H.
    apply D2.Rlt_le_weak. apply H0.
  - assert(C2D x == C2D y). apply C2D_property3. apply H.
    apply Rle_lt_eq. left;auto.
Qed.

Theorem C2D_property8:C2D (1%R)==RBase.Rone.
Proof.
  hnf. split.
  - hnf. intros. destruct H. destruct H. destruct H0.
    assert(x+x0<1)%Q. apply H0 with (x1+1)%nat . omega. reflexivity.
    lra.
  - hnf. intros. exists ((-1#2)*(x-1))%Q. split. lra.
    exists 0%nat. intros. rewrite H1. lra.
Qed.
Lemma notC2Dzero :forall (x:C1.Real)(H:~(x==0%R)%C),~C2D x==RBase.Rzero.
Proof.
  intros. unfold not. intros. apply H.
  assert(C2D 0%R == RBase.Rzero). apply C2D_property6. assert(C2D x==C2D 0%R).
  rewrite H0,H1. reflexivity.
  assert(x==0%R\/~x==0%R)%C by apply classic. destruct H3.
  auto.
  assert(~x<0%R)%C. unfold not. intro. assert(C2D x<C2D 0%R).
  apply C2D_property4. auto. apply D3.Rlt_not_refl with (C2D x).
  rewrite <-H2 in H5. auto.
  assert(~0%R<x)%C. unfold not. intro. apply C2D_property4 in H5.
  rewrite H2 in H5. apply D3.Rlt_not_refl with (C2D 0%R). auto.
  apply Rnot_lt_le in H4. unfold C2.Rge in H4. unfold C2.Rle in H4.
  destruct H4. assert False. apply H5. auto. destruct H6.
  symmetry. auto.
Qed.

Theorem C2D_property9:forall (x:C1.Real)(H:~(x==0%R)%C), C2D (Rinv (exist _ x H))==Dedekind.RArith.Rinv (C2D x) (notC2Dzero x H).
Proof.
  intros. assert(~C2D x==RBase.Rzero). apply notC2Dzero.
  auto. assert((C2D (/ exist (fun a0 : Real => ~ (a0 == 0)%C) x H)%R)*(C2D x)==(Dedekind.RArith.Rinv (C2D x) (notC2Dzero x H))*(C2D x)).
  rewrite C2D_property2. rewrite D3.Rmult_comm. rewrite Rmult_inv.
  assert((/ exist (fun a0 : Real => ~ (a0 == 0)%C) x H)%R * x==1%R)%C.
  rewrite C3.Rmult_comm. apply Rmult_inv_r'.
  assert(C2D ((/ exist (fun a0 : Real => ~ (a0 == 0)%C) x H)%R * x)==C2D 1%R).
  apply C2D_property3. auto. rewrite H2. apply C2D_property8.
  Search D3.Rmult RBase.Rone.
  rewrite <-D3.Rmult_1_r. symmetry. rewrite<-D3.Rmult_1_r. symmetry.
  assert(RBase.Rone==(C2D x)*(Dedekind.RArith.Rinv (C2D x) (notC2Dzero x H) )).
  rewrite Rmult_inv. reflexivity. rewrite H2. rewrite<- D3.Rmult_assoc. rewrite H1.
  rewrite D3.Rmult_assoc. reflexivity.
Qed.

