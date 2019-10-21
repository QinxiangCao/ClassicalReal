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
Require Import CReal.Iso.Cauchy2Dedekind.
Require Import CReal.Iso.Dedekind2Cauchy.

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

(* the definition of D.Rabs *)
Definition cut_positive(A:Q->Prop):Prop:=
A 0.
Definition Cut_abs :(Q->Prop)->(Q->Prop):=
fun A x=>(cut_positive A/\A x)\/(~cut_positive A/\Cut_opp A x).
Theorem Dedekind_Rabs_pre(A:Q->Prop):Dedekind A->Dedekind (Cut_abs A).
Proof.
  intros. split.
  - split. unfold Cut_abs. unfold cut_positive. unfold Cut_opp.
    assert(A 0\/~A 0) by apply classic. destruct H0.
    exists 0. left. auto. exists (-1#1)%Q. right. split. auto. exists 1.
    split. lra. unfold not. intros. apply H0. apply Dedekind_properties4 with ((- (-1 # 1) + - (1)))%Q.
    auto. lra. auto. unfold Cut_abs. unfold cut_positive. unfold Cut_opp.
    assert(A 0\/~A 0) by apply classic. destruct H0.
    assert(exists q:Q,~A q). apply Dedekind_properties1. auto. destruct H1.
    exists x.
    apply and_not_or. split.
    apply or_not_and. right. auto. apply or_not_and. left. auto.
     assert(exists q:Q,A q) as P. apply Dedekind_properties1. auto.
    destruct P as [q P].
    exists (-q)%Q. apply and_not_or. split. apply or_not_and. left. auto.
    apply or_not_and. right. unfold not. intros. destruct H1. destruct H1.
    apply H2. apply Dedekind_properties2  with q. auto. split.
    auto. lra.
  - unfold Cut_abs. unfold cut_positive. unfold Cut_opp. intros.
    destruct H0. destruct H0.
    + left. split. apply H0. apply Dedekind_properties2 with p. auto.
      split. apply H0. auto.
    + right. split. apply H0. destruct H0. destruct H2. exists x.
      split. destruct H2. auto. destruct H2. unfold not. intros.
      apply H3. apply Dedekind_properties2 with (- q + - x)%Q.
      auto. split. auto. lra.
  - unfold Cut_abs. unfold cut_positive. unfold Cut_opp.
    intros. destruct H0.
    + destruct H0. assert(exists r : Q, A r /\ (p < r))%Q. apply Dedekind_properties3. auto. auto.
      destruct H2. exists x. split. left. split. auto. apply H2. apply H2.
    + destruct H0. destruct H1. destruct H1. exists (p+(1#2)*x)%Q.
      split. right. split. auto. exists ((1#2)*x)%Q. split.
      lra. unfold not. intros. apply H2. apply Dedekind_properties4 with (- (p + (1 # 2) * x) + - ((1 # 2) * x))%Q.
      auto. lra. auto. lra.
  - unfold Cut_abs. unfold cut_positive. unfold Cut_opp. intros.
    destruct H1. destruct H1. left. split. auto. apply Dedekind_properties4 with p.
    auto. auto. auto. destruct H1. right. split. auto.
    destruct H2. exists x. split. apply H2. destruct H2. unfold not. intros.
    apply H3. apply Dedekind_properties4 with (- q + - x)%Q. auto.
    lra. auto.
Qed.
Definition Dedekind_Rabs(A:D1.Real):D1.Real:=
match A with
| Real_cons A HA =>Real_cons (Cut_abs A) (Dedekind_Rabs_pre A HA) end.
Lemma DCut_lt :forall(Dcut:Q->Prop),Dedekind Dcut->forall (p q:Q),
Dcut p->~Dcut q->(p<q)%Q.
Proof. 
  intros. pose proof Dedekind_properties2 _ H p q.
assert(~q<=p)%Q;[tauto|]. apply Qnot_le_lt. apply H3.
Qed.
Lemma DRabs_positive:forall (A:D1.Real),(RBase.Rzero<A)%D->(A==Dedekind_Rabs A)%D.
Proof.
intros. unfold D2.Rlt in H. simpl in H. destruct A.
destruct H. destruct H1. destruct H1. hnf. split.
- hnf. intros. hnf. unfold cut_positive. unfold Cut_opp.
  assert(A 0\/~A 0). apply classic. destruct H4. left. split. auto. auto.
  right. split. auto. exists (-x0)%Q. split.
  assert(x0<0)%Q. apply DCut_lt with A. auto. auto. auto. lra.
  unfold not. intros. apply H4. apply Dedekind_properties2 with (- x0 + - - x0)%Q.
  auto. split. auto. lra.
- hnf. intros. hnf in H3. unfold cut_positive,Cut_opp in H3. destruct H3.
  apply H3. destruct H3. destruct H4. destruct H4. apply H.
  assert(0<=- x0 + - x1)%Q. assert(0 <= - x0 + - x1\/~0 <= - x0 + - x1)%Q by apply classic.
  destruct H6. auto. assert(- x0 + - x1<0)%Q by lra.
  assert False. apply H5. apply H. auto. destruct H8. lra.
Qed.
Lemma DRabs_notpositive:forall (A:D1.Real),(~RBase.Rzero<A)%D->(-A==Dedekind_Rabs A)%D.
Proof.
  intros. unfold D2.Rlt in H. simpl in H. destruct A.
  hnf. split.
  - hnf. unfold Cut_opp,Cut_abs. intros. unfold cut_positive,Cut_opp.
    apply not_and_or in H. destruct H. right. split. assert(A 0\/~A 0) by apply classic.
    destruct H2.
    assert False. apply H. intros. apply Dedekind_properties2 with 0. auto. split. auto. lra.
    destruct H3. auto. auto. assert(A 0\/~A 0)by apply classic. destruct H2.
    assert False. apply H. exists 0. split. auto. lra. destruct H3.
    right. split. auto. auto.
  - hnf. unfold Cut_opp,Cut_abs. intros. unfold cut_positive,Cut_opp.
    unfold cut_positive,Cut_opp in H1. 
    apply not_and_or in H. destruct H.
    + destruct H1. destruct H1. assert False.
      apply H. intros. apply Dedekind_properties2 with 0. auto. split. auto. lra. destruct H3.
      destruct H1. auto.
    + destruct H1. assert False. apply H. exists 0. split. apply H1. lra. destruct H2.
      destruct H1. auto.
Qed.
(* the definition of D.Rabs *)

Theorem C2D_property10:forall (x:C1.Real),C2D (Rabs x)==Dedekind_Rabs (C2D x).
Proof.
  intros. assert(0%R<x\/~0%R<x)%C by apply classic.
  destruct H.
  - assert(Rabs x==x)%C. apply Rabs_positive. apply C2.Rpositive_gt_0. apply H.
    assert (C2D (Rabs x)==C2D x)%D. apply C2D_property3. auto.
    rewrite H1. apply DRabs_positive. rewrite<- C2D_property6. apply C2D_property4. auto.
  - assert(Rabs x==-x)%C. apply C2.Rnot_lt in H. destruct H.
    + rewrite<-H. rewrite Rabs_zero. apply C2.Rzero_opp_zero.
    + apply Rabs_negative. apply C2.Rnegative_lt_0. auto.
    +  assert (C2D (Rabs x)==C2D (-x))%D. apply C2D_property3. auto.
       rewrite H1. rewrite C2D_property7. apply DRabs_notpositive.
       rewrite <-C2D_property6. apply  Rnot_lt_le in H.
       apply Rle_not_lt. apply C2D_property5. auto.
Qed.
Theorem D2C_property10:forall (x:D1.Real),(D2C (Dedekind_Rabs x)==Rabs (D2C x))%C.
Proof.
  intros. assert(RBase.Rzero<x\/~RBase.Rzero<x)%D by apply classic.
  destruct H.
  - assert(0%R<D2C x)%C. rewrite<- D2C_property6. apply D2C_property4. auto.
    rewrite Rabs_positive. 
    apply D2C_property3. symmetry. apply DRabs_positive. auto. apply C2.Rpositive_gt_0. auto.
  - assert(-x==Dedekind_Rabs x)%D. apply DRabs_notpositive. auto.
    assert(D2C (Dedekind_Rabs x)==D2C (-x))%C. apply D2C_property3. rewrite H0. reflexivity.
    rewrite H1. rewrite D2C_property7. symmetry.  apply Rabs_nonpositive.
    apply D2.Rnot_lt_le in H. 
    assert(x==RBase.Rzero\/~x==RBase.Rzero)%D by apply classic.
    destruct H2.
    + apply RSign.Rzero_not_positive. rewrite<- D2C_property6.
      apply D2C_property3. auto.
    + apply RSign.Rnegative_not_positive. apply Rnegative_lt_0.
      rewrite<- D2C_property6.
      apply D2C_property4. apply D3.Rle_lt_eq in H. destruct H.
      assert False. apply H2. auto. destruct H3. auto.
Qed.
(* Definition of D.Rlimit *)
Class DR_seq (RS: nat -> D1.Real -> Prop) : Prop := { 
  DRseq_exists : forall (n:nat), exists A1, RS n A1;
  DRseq_unique : forall (n:nat)  A1 A2,
      RS n A1 -> RS n A2 -> (A1 == A2)%D;
  DRseq_proper: forall n, Proper (Req ==> iff) (RS n);
}.
Inductive DReal_seq : Type :=
| DRseq_intro (RS : nat -> D1.Real -> Prop) (H: DR_seq RS).
Definition DRlimit (Rseq:DReal_seq) (Lim:D1.Real):Prop:=
forall Eps:D1.Real, (RBase.Rzero < Eps)%D -> exists N, forall n,
(n>=N)%nat -> forall A, 
(match Rseq with DRseq_intro RS _ => RS end) n A -> (Dedekind_Rabs (A - Lim) < Eps)%D.
(* Definition of D.Rlimit *)

Definition C2D_seq_pre (RS:nat->C1.Real->Prop):nat->D1.Real->Prop:=
fun n x=>exists (y:C1.Real),RS n y/\C2D y==x.

Theorem C2D_seq_limit:forall (A:nat->C1.Real->Prop),R_seq A->DR_seq (C2D_seq_pre A).
Proof.
  intros. destruct H. split.
- intros. assert(exists A1 : Real, A n A1). apply Rseq_exists.
  destruct H. exists (C2D x). hnf. exists x. split. auto. reflexivity.
- intros. hnf in H,H0. destruct H,H0. destruct H,H0.
  assert(x==x0)%C. apply Rseq_unique with n. auto. auto.
  rewrite<-H1. rewrite<-H2. apply C2D_property3. auto.
- intros. hnf. intros. split.
  + unfold C2D_seq_pre. intros. destruct H0. destruct H0.
     exists x0. split. auto. rewrite<-H. auto.
  + unfold C2D_seq_pre. intros. destruct H0. destruct H0.
    exists x0. split. auto. rewrite H. auto.
Qed.

Definition C2D_seq (A:Real_seq):DReal_seq:=
match A with
|Rseq_intro RS H =>DRseq_intro (C2D_seq_pre RS) (C2D_seq_limit RS H) end.

Lemma DRabs_eq: forall (A B:D1.Real),A==B->Dedekind_Rabs A==Dedekind_Rabs B.
Proof.
  intros. hnf. split.
- hnf in H. destruct H. destruct A,B. unfold Dedekind_Rabs.
  hnf. intros. hnf in H. hnf in H0. hnf in H3.
  hnf. unfold cut_positive,Cut_opp in H3 . unfold cut_positive,Cut_opp.
  destruct H3.
  + left. split. apply H. apply H3. apply H. apply H3.
  + right. split. unfold not. intros. destruct H3. apply H3. apply H0. auto.
    destruct H3. destruct H4. destruct H4. exists x0. split.
    auto. unfold not. intros. apply H5. apply H0. auto.
- hnf in H. destruct H. destruct A,B. unfold Dedekind_Rabs.
  hnf. intros. hnf in H. hnf in H0. hnf in H3.
  hnf. unfold cut_positive,Cut_opp in H3 . unfold cut_positive,Cut_opp.
  destruct H3.
  + left. split. apply H0. apply H3. apply H0. apply H3.
  + right. split. unfold not. intros. destruct H3. apply H3. apply H. auto.
    destruct H3. destruct H4. destruct H4. exists x0. split.
    auto. unfold not. intros. apply H5. apply H. auto.
Qed.
Theorem C2D_property11:forall (Climit:C1.Real)(Seq:Real_seq),
Rlimit Seq Climit->DRlimit (C2D_seq Seq) (C2D Climit).
Proof.
  intros. hnf. intros.
  hnf in H. destruct Seq. unfold C2D_seq. 
  destruct H with (D2C Eps). rewrite<- D2C_property6.
  apply D2C_property4. auto. exists x. intros.
  hnf in H4. destruct H4. destruct H4.
  assert(Rabs (x0 - Climit) < D2C Eps)%C. apply H2 with n.
  auto. auto.
  assert(C2D(Rabs (x0 - Climit)) < C2D(D2C Eps))%D.
  apply C2D_property4. auto.
  assert(C2D (D2C Eps)==Eps)%D. apply Bijection. reflexivity.
  rewrite H8 in H7. rewrite C2D_property10 in H7. unfold C3.Rminus in H7.
  assert((Dedekind_Rabs (C2D (x0 + - Climit))==(Dedekind_Rabs (A - C2D Climit))))%D.
  assert(C2D (x0 + - Climit)==(A - C2D Climit))%D. rewrite<- C2D_property1.
  rewrite H5. rewrite C2D_property7. reflexivity.
  apply DRabs_eq. auto.
  rewrite H9 in H7. auto.
Qed.
Definition D2C_seq_pre (RS:nat->D1.Real->Prop):nat->C1.Real->Prop:=
fun n x=>exists (y:D1.Real),RS n y/\(D2C y==x)%C.

Theorem D2C_seq_limit:forall (A:nat->D1.Real->Prop),DR_seq A->R_seq (D2C_seq_pre A).
Proof.
  intros. destruct H. split.
- intros. assert(exists A1 : D1.Real, A n A1). apply DRseq_exists0.
  destruct H. exists (D2C x). hnf. exists x. split. auto. reflexivity.
- intros. hnf in H,H0. destruct H,H0. destruct H,H0.
  assert(x==x0)%D. apply DRseq_unique0 with n. auto. auto.
  rewrite<-H1. rewrite<-H2. apply D2C_property3. auto.
- intros. hnf. intros. split.
  + unfold C2D_seq_pre. intros. destruct H0. destruct H0.
     exists x0. split. auto. rewrite<-H. auto.
  + unfold C2D_seq_pre. intros. destruct H0. destruct H0.
    exists x0. split. auto. rewrite H. auto.
Qed.

Definition D2C_seq (A:DReal_seq):Real_seq:=
match A with
|DRseq_intro RS H =>Rseq_intro (D2C_seq_pre RS) (D2C_seq_limit RS H) end.
Lemma CRabs_eq: forall (A B:C1.Real),(A==B)%C->(Rabs A==Rabs B)%C.
Proof.
  intros. unfold Rabs. destruct A,B. hnf. intros.
  hnf in H. destruct H with  eps. auto. exists x.
  intros. hnf in H5,H6. 
  assert(exists q:Q, CSeq m q). apply Cauchy_exists. auto.
  assert(exists q:Q, CSeq0 m q). apply Cauchy_exists. auto.
  destruct H7,H8. specialize H5 with x0. specialize H6 with x1.
  assert(Qabs (x0 - x1) < eps)%Q.
  apply H3 with m. auto. auto. auto.
  apply H5 in H7. apply H6 in H8. rewrite H7,H8.
  apply Qle_lt_trans with (Qabs (x0 - x1)).
  assert(Qabs x0 - Qabs x1<=0\/~Qabs x0 - Qabs x1<=0)by apply classic.
  destruct H10. rewrite Qabs_neg. rewrite Qabs_Qminus.
  apply Qle_trans with (Qabs x1-Qabs x0). lra. apply Qabs_triangle_reverse.
  auto. rewrite Qabs_pos. apply Qabs_triangle_reverse. lra.
  auto.
Qed.
Theorem D2C_property11:forall (Seq:DReal_seq)(Dlimit:D1.Real),
DRlimit Seq Dlimit->Rlimit (D2C_seq Seq) (D2C Dlimit).
Proof.
  intros. hnf. intros.
  hnf in H. destruct Seq. unfold D2C_seq. 
  destruct H with (C2D Eps). rewrite<- C2D_property6.
  apply C2D_property4. auto. exists x. intros.
  hnf in H4. destruct H4. destruct H4.
  assert(Dedekind_Rabs (x0 - Dlimit) < C2D Eps)%D. apply H2 with n.
  auto. auto.
  assert(D2C(Dedekind_Rabs (x0 - Dlimit)) < D2C(C2D Eps))%C.
  apply D2C_property4. auto.
  assert(D2C (C2D Eps)==Eps)%C. apply Bijection. reflexivity.
  rewrite H8 in H7. rewrite D2C_property10 in H7. unfold D3.Rminus in H7.
  assert(Rabs (D2C (x0 + - Dlimit))==Rabs (A - D2C Dlimit))%C.
  apply CRabs_eq. rewrite<- D2C_property1. rewrite H5.
  rewrite D2C_property7. reflexivity.
  rewrite H9 in H7. auto.
Qed.