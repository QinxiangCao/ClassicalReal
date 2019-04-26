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

Lemma Trouble1: forall(CSeq :nat->Q->Prop)(p:Q)(x:nat),
Cauchy CSeq->(forall (n : nat) (p0 : Q),(n > x)%nat -> CSeq n p0 -> p < p0)->
(exists r : Q,  (exists N : nat,forall (n : nat) (p0 : Q),(n > N)%nat -> CSeq n p0 -> r < p0) /\  p < r).
Proof.
Admitted.   

Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (fun q=>exists (N:nat),forall (n:nat)(p:Q),(n>N)%nat->CSeq n p->(q<p)%Q).
Proof. 
  intros. split.
- split.
  + assert(Cauchy CSeq ->exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    apply CauchySeqBounded_weak. assert(exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    { apply H0. apply H. } destruct H1. destruct H1. exists (-x0)%Q.
    exists (S x). intros. assert(Qabs p<x0). apply H1 with n.
    omega. auto. assert(p==--p)%Q.  { rewrite Qopp_opp. reflexivity. }
    rewrite H5. apply QArith_base_ext.Qopp_lt_compat.
    apply Qle_lt_trans with (Qabs p). rewrite<-Qabs_opp. apply Qle_Qabs.
    apply H4. 
  + assert(Cauchy CSeq ->exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    apply CauchySeqBounded_weak. assert(exists (N : nat) (M : Q),
    forall (n : nat) (q : Q), (n > N)%nat -> CSeq n q -> Qabs q < M).
    { apply H0. apply H. } destruct H1. destruct H1. exists x0.
    unfold not. intros. destruct H2. destruct H. 
    assert( exists q : Q, CSeq (x+x1+1)%nat q).
    apply Cauchy_exists. destruct H.
    assert( x0<x2). apply H2 with (x+x1+1)%nat. omega. apply H.
    assert(Qabs x2<x0). apply H1 with(x+x1+1)%nat. omega. auto.
    apply Qlt_irrefl with x0. apply Qlt_le_trans with x2.
    auto. Search Qle. apply QOrderedType.QOrder.le_trans with (Qabs x2).
    apply Qle_Qabs. apply Qlt_le_weak. auto.
- intros. destruct H0. destruct H0. exists x.  intros.
  apply Qle_lt_trans with p. auto. apply H0 with n .
  auto. auto.
- intros. destruct H0. apply Trouble1 with x. auto. auto.
- intros. destruct H1. exists x. intros. rewrite<-H0. apply H1 with n.
  auto. auto.
Qed.

Definition C2D (A:C1.Real):D1.Real :=
match A with
|Real_intro CSeq H =>
Real_cons (fun q=>exists (N:nat),forall (n:nat)(p:Q),(n>N)%nat->CSeq n p->(q<p)%Q)(Dedekind_CSeq CSeq H) end.

Theorem C2D_properity1:forall (x y:C1.Real),
  ( (C2D x)+(C2D y)==C2D (x+y))%D.
Proof.
  intros. destruct x. destruct y. unfold "=="%D. split.
- unfold Rle. unfold "+"%D. simpl. intros. destruct H1.
  destruct H1. repeat destruct H1. destruct H2.
  destruct H2. exists (x2+x3)%nat. intros. unfold C1.CauchySeqPlus in H5.
  destruct H. destruct H0. destruct Cauchy_exists with n. destruct Cauchy_exists0 with n.
  assert(p==x4+x5)%Q. apply H5. auto. auto. rewrite H6. rewrite<-H3.
  apply Qplus_lt_le_compat.
  + apply H1 with n. omega. auto.
  + assert(x1<x5). apply H2 with n. omega. auto.
    apply Qlt_le_weak. auto.
- unfold Rle. unfold "+"%D. simpl. intros. destruct H1.
  unfold D3.Cut_plus_Cut.
  destruct H. destruct H0.
  destruct Cauchy_exists with x0. 
  destruct Cauchy_exists0 with x0.
  exists ((1#2)*x)%Q,((1#2)*x)%Q. split.
  + exists x0. intros. assert(x<(2#1)*p)%Q.
    { apply H1 with n. apply H2. unfold C1.CauchySeqPlus.
      intros. 

Theorem C2D_properity2:forall (x y:C1.Real),
  ((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.

Admitted.
Theorem C2D_properity3:forall (x y:C1.Real),
(x==y)%C->  ((C2D x)==(C2D y)).
Proof.
Admitted.


