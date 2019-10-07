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

Module C1 := Cauchy.RBase.
Module C2 := Cauchy.ROrder.
Module C3 := Cauchy.RArith.
Module D1 := Dedekind.RBase.
Module D2 := Dedekind.ROrder.
Module D3 := Dedekind.RArith.
Bind Scope CReal_Scope with Cauchy.RBase.Real.
Delimit Scope CReal_Scope with C.
Local Open Scope CReal_Scope.

Bind Scope DReal_Scope with Dedekind.RBase.Real.
Delimit Scope DReal_Scope with D.

Notation "a == b" :=(D2.Req a b):DReal_Scope.
Notation "a + b" :=(D3.Rplus a b):DReal_Scope.
Notation "a * b" :=(D3.Rmult a b):DReal_Scope.
Notation "a == b" :=(C1.Real_equiv a b):CReal_Scope.
Notation "a + b" :=(C3.Rplus a b):CReal_Scope.
Notation "a * b" :=(C3.Rmult a b):CReal_Scope.
Notation "a <= b" :=(D2.Rle a b):DReal_Scope.

Lemma Dcut_lt :forall(Dcut:Q->Prop),Dedekind Dcut->forall (p q:Q),
Dcut p->~Dcut q->p<q.
Proof. 
  intros. pose proof Dedekind_properties2 _ H p q.
assert(~q<=p);[tauto|]. apply Qnot_le_lt. apply H3.
Qed.
Lemma Qlt_Zlt :forall(a b:Z)(c:positive),(a#c<b#c)%Q->(a<b)%Z.
Proof.
  intros. unfold Qlt in H. simpl in H.
  apply Zmult_gt_0_lt_reg_r with (Z.pos c). 
  assert(0<Z.pos c)%Z. apply Pos2Z.is_pos. 
  omega. apply H.
Qed.
Lemma Qplus_sameden:forall(a b:Z)(c:positive),((a#c)+(b#c)==(a+b)#c)%Q.
Proof.
  intros. unfold Qplus. unfold Qeq. simpl.
  assert((a * Z.pos c + b * Z.pos c)%Z=(a+b)*Z.pos c)%Z. ring. rewrite H.
  assert(Z.pos (c * c)=Z.pos c*Z.pos c)%Z. tauto. rewrite H0. ring. 
Qed.

  
Lemma power_compare1:forall (n:nat),(of_nat n<2^of_nat n)%positive.
Proof.
  induction n.
  - simpl. reflexivity.
  - induction n. 
    + reflexivity.
    + assert(2 ^ of_nat (S(S n)) =2 ^ of_nat (S n)+2 ^ of_nat (S n))%positive.
    assert(of_nat (S(S n))=BinPos.Pos.succ (of_nat (S n))).
    rewrite<-Pos.of_nat_succ.
    symmetry.
    assert((S n)<>0%nat->BinPos.Pos.succ (of_nat (S n)) = of_succ_nat  (S n)).
    apply Pos.succ_of_nat.
    apply H. omega. rewrite H.
    rewrite Pos.pow_succ_r. rewrite Pos.add_diag. reflexivity.
    rewrite H.
    assert(of_nat (S(S n)) =(of_nat (S n))+1)%positive.
    rewrite<-Pos.of_nat_succ. rewrite Pos.add_1_r.
    symmetry. apply Pos.succ_of_nat. omega.
    rewrite H0.
    apply Pos.lt_le_trans with (2 ^ of_nat (S n) + 1 )%positive.
    apply Pos.add_lt_mono_r . apply IHn.
    apply Pos.add_le_mono_l. apply Pos.le_1_l.
Qed.

Lemma power_compare2:forall (n:nat),(n>0)%nat->(1#(2^of_nat n)<1#of_nat n)%Q.
Proof.
  intros. assert(of_nat n<2 ^ of_nat n )%positive. apply power_compare1.
  unfold Qlt. simpl. apply H0.
Qed.
Lemma inject_compare:forall (x1 n:nat)(x4:Q),0<x4->(x1<=n)%nat->1 / x4 <= inject_Z (Z.of_nat x1)->1 # of_nat n <= x4.
Proof.
  intros.  assert(1 / x4 *x4<= inject_Z (Z.of_nat x1)*x4)%Q.
      apply Qmult_le_compat_r. apply H1. apply Qlt_le_weak. apply H.
      assert(x4 * /x4==1)%Q. apply Qmult_inv_r.
      unfold not. intros.  rewrite H3 in H. 
      assert False. apply Qlt_irrefl with 0. apply H. destruct H4.
      assert((1 / x4) * x4 ==x4 * / x4)%Q.
      assert(1 / x4==/x4)%Q. field. unfold not. intros. 
      rewrite H4 in H. lra.
      rewrite<-H4. ring. rewrite H3 in H4. rewrite H4 in H2.
      unfold Qle in H2. simpl in H2.
      unfold Qle. simpl.
      apply Z.le_trans with (Z.of_nat x1 * Qnum x4 * 1)%Z.
      auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
      assert(Z.of_nat x1 <=Z.pos (of_nat n))%Z. 
      destruct n. simpl. assert(x1=0)%nat by omega. rewrite H5.
      simpl. omega. rewrite<-Pos.of_nat_succ.
      rewrite Zpos_P_of_succ_nat. omega.
      apply Z.mul_le_mono_nonneg_l. unfold Qlt in H. simpl in H.
      rewrite Z.mul_1_r in H. omega. apply H5.
Qed.
Lemma Zlt_1_contradiction :forall (a b:Z),(a<b->b<a+1->False)%Z.
Proof.
  intros. omega.
Qed.
Lemma power2_pos:forall ( b:positive),Z.pos(2^b)=(2^Z.pos b)%Z.
Proof.
  intros. simpl. rewrite<-Pos2Z.inj_pow_pos. reflexivity.
Qed.
  
Lemma power_Qlt_1 : forall (a c:Z) ( b  d:positive),((b<d)%positive->a#2^b<c#2^d->a#1<c#2^(d-b))%Q.
Proof.
  intros. unfold Qlt in H0. unfold Qlt. simpl. simpl in H0.
  assert(a * Z.pos (2 ^ (d - b))*Z.pos (2 ^ b) < c *Z.pos (2 ^ b))%Z.
  rewrite<-Z.mul_assoc.
  assert(Z.pos (2 ^ (d - b)) * Z.pos (2 ^ b)=Z.pos (2 ^ d))%Z.
  assert(Z.pos (2 ^ d)=2^(Z.pos d))%Z. apply power2_pos.
  assert(Z.pos (2 ^ b)=2^(Z.pos b))%Z. apply power2_pos.
  assert(Z.pos (2 ^ (d-b)%positive)=2^(Z.pos (d-b)%positive))%Z. apply power2_pos.
  rewrite H1,H2,H3.
  assert(2 ^ Z.pos (d - b) * 2 ^ Z.pos b=2^(Z.pos (d - b)+Z.pos b))%Z.
  symmetry.
  apply Z.pow_add_r. apply Pos2Z.is_nonneg. apply Pos2Z.is_nonneg.
  rewrite H4.
  assert(Z.pos (d - b) + Z.pos b=Z.pos d)%Z.
  assert(Z.pos (d - b)=Z.pos d-Z.pos b)%Z.
  apply Pos2Z.inj_sub. apply H. rewrite H5. omega.
  rewrite H5. reflexivity. rewrite H1. apply H0.
  rewrite Z.mul_1_r.
  apply Zmult_lt_reg_r with (Z.pos (2 ^ b)). reflexivity. apply H1.
Qed.
Lemma power_Qlt_2 : forall (a c:Z) ( b  d:positive),((d<b)%positive->a#2^b<c#2^d->a#2^(b-d)<c#1)%Q.
Proof.
  intros. unfold Qlt in H0. unfold Qlt. simpl. simpl in H0.
  assert(a * Z.pos (2 ^ d) < c *Z.pos (2 ^ (b-d))*Z.pos (2 ^ d))%Z.
  rewrite<-Z.mul_assoc.
  assert(Z.pos (2 ^ (b - d)) * Z.pos (2 ^ d)=Z.pos (2 ^ b))%Z.
  assert(Z.pos (2 ^ d)=2^(Z.pos d))%Z. apply power2_pos.
  assert(Z.pos (2 ^ b)=2^(Z.pos b))%Z. apply power2_pos.
  assert(Z.pos (2 ^ (b-d)%positive)=2^(Z.pos (b-d)%positive))%Z. apply power2_pos.
  rewrite H1,H2,H3.
  assert(2 ^ Z.pos (b - d) * 2 ^ Z.pos d=2^(Z.pos (b - d)+Z.pos d))%Z.
  symmetry.
  apply Z.pow_add_r. apply Pos2Z.is_nonneg. apply Pos2Z.is_nonneg.
  rewrite H4.
  assert(Z.pos (b - d) + Z.pos d=Z.pos b)%Z.
  assert(Z.pos (b - d)=Z.pos b-Z.pos d)%Z.
  apply Pos2Z.inj_sub. apply H. rewrite H5. omega.
  rewrite H5. reflexivity. rewrite H1. apply H0.
  rewrite Z.mul_1_r.
  apply Zmult_lt_reg_r with (Z.pos (2 ^ d)). reflexivity. apply H1.
Qed.

Lemma lt_Poslt :forall(a b:nat),(0<a->a<b->(of_nat a<of_nat b)%positive)%nat.
Proof.
  intros.
  generalize dependent b.
  induction a.
  - inversion H.
  - intros. assert(a=0\/~a=0)%nat by apply classic. destruct H1.
    * rewrite H1. rewrite H1 in H0. simpl. 
      destruct  b. inversion H0. destruct b. inversion H0.
      inversion H3. rewrite <-Pos.of_nat_succ. rewrite<- Pos.succ_of_nat.
      apply Pos.lt_1_succ. omega.
    * induction b.
        + inversion H0.
        + rewrite<- Pos.of_nat_succ. rewrite <-Pos.of_nat_succ.
          rewrite<- Pos.succ_of_nat. rewrite <-Pos.succ_of_nat.
          assert(of_nat a < of_nat b)%positive. apply IHa.
          omega. omega.
          rewrite<- Pos.succ_lt_mono. apply H2. omega. apply H1.
Qed.
Lemma Dcut_P: forall (n:positive)(Dcut:Q->Prop),Dedekind Dcut ->
exists (m:Z),Dcut (m#n)/\~Dcut (m+1#n).
Proof.
  intros. assert(exists (t:Z),Dcut (t#n)).
  { destruct H. destruct Dedekind_properties1. destruct H.
  destruct Inject_lemmas.le_inject_Z with x.
  exists (Zpos(n)*x0)%Z. assert(Z.pos n * x0 # n==inject_Z x0)%Q.
  rewrite Qmake_Qdiv. rewrite inject_Z_mult. field. 
  unfold not. assert(0<Z.pos n)%Z. apply Pos2Z.is_pos. 
  intros. assert(inject_Z 0<inject_Z (Z.pos n)). rewrite<- Zlt_Qlt.
  apply H2. rewrite H3 in H4. inversion H4. 
  assert(Z.pos n * x0 # n<= x) . rewrite H2. auto.
  apply Dedekind_properties2 with x. auto. }
  assert(exists (s:Z),~Dcut (s#n)).
  { destruct H. destruct Dedekind_properties1.  destruct H1.
  destruct Inject_lemmas.inject_Z_le with x.
  exists (Zpos(n)*x0)%Z. assert(Z.pos n * x0 # n==inject_Z x0)%Q.
  rewrite Qmake_Qdiv. rewrite inject_Z_mult. field. 
  unfold not. assert(0<Z.pos n)%Z. apply Pos2Z.is_pos.
  intros. assert(inject_Z 0<inject_Z (Z.pos n)). rewrite<- Zlt_Qlt.
  apply H3. rewrite H4 in H5. inversion H5. 
  assert(x<=Z.pos n * x0 # n) . rewrite H3. auto.
  unfold not. intros. assert (Dcut x).
  apply Dedekind_properties2 with (Z.pos n * x0 # n). auto.
  auto. } destruct H0. destruct H1.
  assert(forall (t:nat)(a b:Z),Dcut (a#n)->~Dcut (b#n)->
  Z.to_nat(b-a)=t->exists m : Z, Dcut (m # n) /\ ~ Dcut (m + 1 # n))%Q. 
  { intros. generalize dependent a. generalize dependent b.  induction t0. intros. assert(a#n<b#n)%Q. apply Dcut_lt with Dcut.
  apply H. apply H2. apply H3. assert(a<b)%Z. unfold Qlt in H5. simpl in H5.
  apply Zmult_gt_0_lt_reg_r with (Z.pos n). 
  assert(0<Z.pos n)%Z. apply Pos2Z.is_pos. 
  omega. apply H5. 
  assert (0<Z.to_nat (b - a))%nat.
  assert(0<b-a)%Z. omega. assert(0=Z.to_nat 0)%nat. reflexivity.
  rewrite H8. apply Z2Nat.inj_lt. reflexivity. omega. apply H7. intros. rewrite<- H4 in H7. assert False.
  apply Nat.lt_irrefl with (Z.to_nat (b - a)).
  apply H7. destruct H8. intros.
  assert(Dcut ((b-1)#n)%Q\/~ Dcut ((b-1)#n)%Q)%Q. apply classic.
    destruct H5.
    + exists (b-1)%Z. split. apply H5. assert(b-1+1=b)%Z.
      omega. rewrite H6. apply H3.
    + apply IHt0 with (b-1)%Z a. apply H5. apply H2.
      assert(Z.to_nat (b - a)=S(Z.to_nat (b - 1 - a))).
      assert(b - 1 - a=b-a-1)%Z. omega.
      rewrite H6. assert(Z.to_nat (b - a - 1)=Z.to_nat (b-a)-1)%nat.
      apply Z2Nat.inj_sub. omega.
      rewrite H7. omega. rewrite H6 in H4. apply eq_add_S. apply H4. }
  apply H2 with (Z.to_nat(x0-x)) x x0. apply H0. apply H1. reflexivity.
Qed.
Definition CSeq_pre (DCut: Q -> Prop): nat -> Q -> Prop :=
(fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).
Lemma D2C_Seqbounded: forall(DCut:Q->Prop),Dedekind DCut->exists (t:Q),forall(n:nat)(q:Q)(N:Z),
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q->
Qabs q<t.
Proof.
  intros.
  assert(exists x : Q, ~ DCut x). apply H.
  destruct H0.
  assert(exists x:Z, DCut (x#2)/\~DCut ((x+1)#2))%Q. apply Dcut_P. auto.
  destruct H1.
  assert(exists q:Q,Qabs(x0#2)<q/\Qabs x<q )%Q.
  exists (Qabs (x0 # 2)+Qabs x+1)%Q. split.
  assert(0<Qabs x + 1)%Q.
  assert(0==0+0)%Q by ring. rewrite H2.
  apply QArith_base_ext.Qplus_le_lt_compat. apply Qabs_nonneg. reflexivity.
  assert(Qabs (x0 # 2)==Qabs (x0 # 2)+0)%Q by ring.
  rewrite H3.
  assert( Qabs (x0 # 2) + 0 + Qabs x + 1== Qabs (x0 # 2) + (Qabs x + 1))%Q by ring.
  rewrite H4. apply QArith_base_ext.Qplus_le_lt_compat. apply Qle_refl. auto.
  assert(Qabs x ==(Qabs x )+0)%Q by ring. rewrite H2.
  assert(Qabs (x0 # 2) + (Qabs x + 0) + 1==Qabs x +(Qabs (x0 # 2) +  1))%Q by ring.
  rewrite H3. apply QArith_base_ext.Qplus_le_lt_compat. apply Qle_refl.
  assert(0==0+0)%Q by ring. rewrite H4.
  apply QArith_base_ext.Qplus_le_lt_compat. apply Qabs_nonneg. reflexivity.
  destruct H2.
  exists x1. destruct H1,H2. intros.
  assert(x0#2<=q).
  destruct H5. destruct H6. rewrite H7.
  assert(x0 # 2 <= N # 2 ^ of_nat n\/~x0 # 2 <= N # 2 ^ of_nat n) by apply classic.
  destruct H8. auto.
  apply QOrderedType.QOrder.not_ge_lt in H8.
  assert False.
  apply H6. assert(N + 1 # 2 ^ of_nat n<=x0 # 2)%Q.
  unfold Qlt in H8. unfold Qle. simpl. simpl in H8.
  assert(N * 2 +1<= x0 * Z.pos (2 ^ of_nat n))%Z. lia.
  assert(N * 2 + 1 = x0 * Z.pos (2 ^ of_nat n)\/~N * 2 + 1 = x0 * Z.pos (2 ^ of_nat n))%Z by apply classic.
  destruct H10. 
  assert False. 
  assert(exists x:Z,2*x=x0 * Z.pos (2 ^ of_nat n))%Z.
  destruct n. exists x0. rewrite Z.mul_comm. simpl.
  reflexivity.
  destruct n.
  exists x0. rewrite Z.mul_comm. reflexivity.
  exists(Z.pos (2 ^ of_nat (S n))*x0)%Z.
  rewrite Z.mul_assoc. symmetry. rewrite Z.mul_comm.
  rewrite Pos2Z.inj_pow_pos. rewrite Pos2Z.inj_pow_pos.
  Search Z.pow_pos.
  assert(2=Z.pow_pos 2 1)%Z. reflexivity. rewrite H11.
  rewrite<-Zpower_pos_is_exp.
  assert(of_nat (S (S n))=1 + of_nat (S n))%positive.
  rewrite<-Pos.of_nat_succ.
  rewrite<-Pos.succ_of_nat. rewrite<-Pos.add_1_l. reflexivity.
  omega.
  rewrite H12. reflexivity.
  destruct H11. rewrite<-H11 in H10.
  assert(N<=x2\/x2<N)%Z by apply Z.le_gt_cases.
  destruct H12. assert(N=x2\/~N=x2) by apply classic. destruct H13.
  rewrite H13 in H10. omega. assert(N<x2)%Z by lia. omega. omega. destruct H11.
  lia.
  apply Dedekind_properties2 with (x0 # 2).  auto.
  split. auto. auto. destruct H9.
  assert(q<x). apply Dcut_lt with DCut. auto.
  destruct H5. destruct H7. rewrite H8. auto. auto.
  apply QArith_base_ext.Qabs_Qlt_condition.
  split. apply Qlt_le_trans with (x0#2).
  apply QArith_base_ext.Qabs_Qlt_condition in H2. apply H2.
  auto. apply Qlt_trans with x.
  auto.  apply QArith_base_ext.Qabs_Qlt_condition in H4.
  apply H4.
Qed.
Theorem Cauchy_Dcut :forall (DCut:Q->Prop),
Dedekind DCut->Cauchy (CSeq_pre DCut).
Proof.
  intros.
  split.
- intros. unfold CSeq_pre. 
  assert(exists (N:Z), DCut (N # 2 ^ of_nat n) /\
  ~ DCut (N + 1 # 2 ^ of_nat n)). apply Dcut_P. apply H.
  destruct H0.
  exists( x # 2 ^ of_nat n). exists x.
  split. apply H0. split. apply H0. reflexivity.
- intros. unfold CSeq_pre in *. destruct H0. destruct H1.
  assert(x=x0)%Z.
  { assert(x<x0+1)%Z. pose proof Dedekind_properties2 _ H.
  assert(x # (2 ^ of_nat n)<x0 + 1 # (2 ^ of_nat n))%Q.
  apply Dcut_lt with DCut. auto. apply H0. apply H1.
  unfold Qlt in H3. simpl in H3. apply Zmult_lt_reg_r with (Z.pos (2 ^ of_nat n)).
  apply Pos2Z.is_pos. apply H3. 
  assert(x0<x+1)%Z. pose proof Dedekind_properties2 _ H.
  assert(x0 # (2 ^ of_nat n)<x + 1 # (2 ^ of_nat n))%Q.
  apply Dcut_lt with DCut. auto. apply H1. apply H0. 
  unfold Qlt in H4. simpl in H4. apply Zmult_lt_reg_r with (Z.pos (2 ^ of_nat n)).
  apply Pos2Z.is_pos. apply H4.   omega. }
  destruct H0.  destruct H3. rewrite H4.
  destruct H1. destruct H5. rewrite H6. rewrite H2. reflexivity.
- intros. destruct H1. unfold CSeq_pre. exists x.
  split. apply H1. split. apply H1. rewrite<-H0. apply H1.
- intros. assert(exists n:nat,1/eps<=inject_Z(Z.of_nat n)).
  apply Inject_lemmas.inject_Z_of_nat_le. destruct H1.
  exists (x+1)%nat. intros.
  assert(m1<=m2\/~m1<=m2)%nat. apply classic. destruct H6.
  + inversion H6. 
    * assert(q1==q2)%Q. {
      destruct H4. destruct H5. assert (x0=x1).
      assert(x0<x1+1)%Z. apply Qlt_Zlt with (2 ^ of_nat m1)%positive.
      apply Dcut_lt with DCut. auto. apply H4. rewrite H7. apply H5.
      assert(x1<x0+1)%Z. apply Qlt_Zlt with (2 ^ of_nat m1)%positive.
      apply Dcut_lt with DCut. auto. rewrite H7. apply H5. apply H4.
      omega.
      assert(q1 == x0 # 2 ^ of_nat m1)%Q. apply H4.
      assert(q2 == x1 # 2 ^ of_nat m2)%Q. apply H5.
      rewrite H9. rewrite H10. rewrite H7. rewrite H8. reflexivity. }
      assert(q1-q2==0)%Q. rewrite H8.  ring. rewrite H9. simpl. apply H0.
    * assert(m1<m2)%nat. omega.
      assert(q1<=q2)%Q.
      unfold CSeq_pre in *.
      destruct H4. destruct H4. destruct H10.
      destruct H5. destruct H5. destruct H12.
      assert(q1<=q2\/~q1<=q2) by apply classic. destruct H14. apply H14.
      assert(q2<q1). apply QOrderedType.QOrder.not_ge_lt. apply H14.
      rewrite H11,H13 in H15.
      assert(x1#2^(of_nat (m2-m1))<x0#1)%Q.
      assert(of_nat (m2 - m1)=(of_nat m2)-(of_nat m1))%positive.
      apply Nat2Pos.inj_sub. omega. rewrite H16.
      apply power_Qlt_2. apply lt_Poslt. omega. auto. apply H15.
      assert(x0 # 2 ^ of_nat m1<x1 + 1 # 2 ^ of_nat m2). apply Dcut_lt with DCut.
      auto. auto. auto.
      assert(x0 # 1<x1 + 1 # 2 ^ of_nat (m2-m1)).
      assert(of_nat (m2 - m1)=(of_nat m2)-(of_nat m1))%positive.
      apply Nat2Pos.inj_sub. omega. rewrite H18.
      apply power_Qlt_1. apply lt_Poslt. omega. auto. apply H17.
      unfold Qlt in H16,H18. simpl in H16,H18.
      rewrite Z.mul_1_r in H16,H18.
      assert False.
      apply Zlt_1_contradiction with x1 (x0 * Z.pos (2 ^ of_nat (m2 - m1)))%Z.
      auto. auto. destruct H19.
      assert(Qabs (q1 - q2)==q2-q1)%Q. assert(q1-q2<=0). 
      unfold Qle. simpl. unfold Qle in H10. 
      assert((Qnum q1 * QDen q2 + - Qnum q2 * QDen q1) * 1 =(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1))%Z. omega.
      rewrite H11. 
      assert(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1=Qnum q1 * QDen q2  - Qnum q2 * QDen q1)%Z.
      unfold Zminus. assert(- Qnum q2 * QDen q1=- (Qnum q2 * QDen q1))%Z.
      ring. ring. rewrite H12. apply Z.le_sub_0. apply H10.
      assert(Qabs (q1 - q2)==-(q1-q2))%Q. rewrite Qabs_neg.
      reflexivity. apply H11.
      rewrite H12. ring. 
      assert(q2-q1<1#2^of_nat m1)%Q.
      unfold CSeq_pre in H4,H5. destruct H4,H5.
      destruct H4. destruct H12. destruct H5. destruct H14.
      assert(x1 # 2 ^ of_nat m2<x0 + 1 # 2 ^ of_nat m1)%Q.
      apply Dcut_lt with DCut. auto. auto. auto.
      rewrite H13,H15.
      assert( 1# 2 ^ of_nat m1==((x0+1) # 2 ^ of_nat m1)-(x0 # 2 ^ of_nat m1))%Q.
      unfold Qminus.
      assert(- (x0 # 2 ^ of_nat m1)==(-x0 # 2 ^ of_nat m1))%Q.
      unfold Qeq. simpl. reflexivity.
      rewrite H17. rewrite Qplus_sameden.
      assert(x0 + 1 + - x0=1)%Z. ring. rewrite H18. reflexivity.    
      rewrite H17. unfold Qminus.
      apply Qplus_lt_l. auto.
      rewrite H11.
      assert(x=0\/~x=0)%nat by apply classic. destruct H13. rewrite H13 in H1. simpl in H1.
      unfold inject_Z in H1. assert(0<1/eps)%Q .
      assert(1 / eps==/eps)%Q. field. unfold not. intros.
      rewrite H14 in H0. apply Qlt_irrefl with 0. apply H0. rewrite H14. apply Qinv_lt_0_compat. apply H0.
      assert(0<0). apply QOrderedType.QOrder.lt_le_trans with (1 / eps). auto. auto.
      assert False. apply Qlt_irrefl with 0. apply H15. destruct H16.
      assert(1 # 2 ^ of_nat m1<=eps)%Q. assert(1 # 2 ^ of_nat m1<=1#of_nat m1)%Q.
      apply Qlt_le_weak. apply power_compare2. omega. 
      apply QOrderedType.QOrder.le_trans with (1 # of_nat m1). apply H14.
      unfold Qle. simpl.
      assert(1 / eps *eps<= inject_Z (Z.of_nat x)*eps)%Q.
      apply Qmult_le_compat_r. apply H1. apply Qlt_le_weak. apply H0.
      assert(eps * /eps==1)%Q. apply Qmult_inv_r.
      unfold not. intros.  rewrite H16 in H0. 
      assert False. apply Qlt_irrefl with 0. apply H0. destruct H17.
      assert((1 / eps) * eps ==eps * / eps)%Q.
      assert(1 / eps==/eps)%Q. field. unfold not. intros.  rewrite H17 in H0. 
      assert False. apply Qlt_irrefl with 0. apply H0. destruct H18.
      rewrite<-H17. ring. rewrite H16 in H17. rewrite H17 in H15.
      unfold Qle in H15. simpl in H15.
      apply Z.le_trans with (Z.of_nat x * Qnum eps * 1)%Z.
      auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
      assert(Z.of_nat x <=Z.pos (of_nat m1))%Z.
      assert(x<=m1)%nat. omega. 
      destruct m1. simpl. assert(x=0)%nat by omega. rewrite H19.
      simpl. omega. rewrite<-Pos.of_nat_succ.
      rewrite Zpos_P_of_succ_nat. omega.
      apply Z.mul_le_mono_nonneg_l. unfold Qlt in H0. simpl in H0.
      rewrite Z.mul_1_r in H0. omega. apply H18.
      apply Qlt_le_trans with (1 # 2 ^ of_nat m1). auto. auto.
    + assert(m2<m1)%nat. omega.
      assert(q2<=q1)%Q.
      unfold CSeq_pre in *.
      destruct H4. destruct H4. destruct H8.
      destruct H5. destruct H5. destruct H10.
      assert(q2<=q1\/~q2<=q1) by apply classic. destruct H12. apply H12.
      assert(q1<q2). apply QOrderedType.QOrder.not_ge_lt. apply H12.
      rewrite H9,H11 in H13.
      assert(x0#2^(of_nat (m1-m2))<x1#1)%Q.
      assert(of_nat (m1 - m2)=(of_nat m1)-(of_nat m2))%positive.
      apply Nat2Pos.inj_sub. omega. rewrite H14.
      apply power_Qlt_2. apply lt_Poslt. omega. auto. apply H13.
      assert(x1 # 2 ^ of_nat m2<x0 + 1 # 2 ^ of_nat m1). apply Dcut_lt with DCut.
      auto. auto. auto.
      assert(x1 # 1<x0 + 1 # 2 ^ of_nat (m1-m2)).
      assert(of_nat (m1 - m2)=(of_nat m1)-(of_nat m2))%positive.
      apply Nat2Pos.inj_sub. omega. rewrite H16.
      apply power_Qlt_1. apply lt_Poslt. omega. auto. apply H15.
      unfold Qlt in H14,H16. simpl in H14,H16.
      rewrite Z.mul_1_r in H16,H14.
      assert False.
      apply Zlt_1_contradiction with x0 (x1 * Z.pos (2 ^ of_nat (m1 - m2)))%Z.
      auto. auto. destruct H17.
      assert(Qabs (q1 - q2)==q1-q2)%Q. assert(0<=q1-q2). 
      unfold Qle. simpl. unfold Qle in H8. 
      assert((Qnum q1 * QDen q2 + - Qnum q2 * QDen q1) * 1 =(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1))%Z. omega.
      rewrite H9. 
      assert(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1=Qnum q1 * QDen q2  - Qnum q2 * QDen q1)%Z.
      unfold Zminus. assert(- Qnum q2 * QDen q1=- (Qnum q2 * QDen q1))%Z.
      ring. ring. rewrite H10. apply Zle_minus_le_0. apply H8.
      rewrite Qabs_pos.
      reflexivity. apply H9.
      rewrite H9. 
      assert(q1-q2<1#2^of_nat m2)%Q.
      unfold CSeq_pre in H4,H5. destruct H4,H5.
      destruct H4. destruct H10. destruct H5. destruct H12.
      assert(x0 # 2 ^ of_nat m1<x1 + 1 # 2 ^ of_nat m2)%Q.
      apply Dcut_lt with DCut. auto. auto. auto.
      rewrite H13,H11.
      assert( 1# 2 ^ of_nat m2==((x1+1) # 2 ^ of_nat m2)-(x1 # 2 ^ of_nat m2))%Q.
      unfold Qminus.
      assert(- (x1 # 2 ^ of_nat m2)==(-x1 # 2 ^ of_nat m2))%Q.
      unfold Qeq. simpl. reflexivity.
      rewrite H15. rewrite Qplus_sameden.
      assert(x1 + 1 + - x1=1)%Z. ring. rewrite H16. reflexivity.    
      rewrite H15. unfold Qminus.
      apply Qplus_lt_l. auto.
      assert(x=0\/~x=0)%nat by apply classic. destruct H11. rewrite H11 in H1. simpl in H1.
      unfold inject_Z in H1. assert(0<1/eps)%Q .
      assert(1 / eps==/eps)%Q. field. unfold not. intros.
      rewrite H12 in H0. apply Qlt_irrefl with 0. apply H0. rewrite H12. apply Qinv_lt_0_compat. apply H0.
      assert(0<0). apply QOrderedType.QOrder.lt_le_trans with (1 / eps). auto. auto.
      assert False. apply Qlt_irrefl with 0. apply H13. destruct H14.
      assert(1 # 2 ^ of_nat m2<=eps)%Q. assert(1 # 2 ^ of_nat m2<=1#of_nat m2)%Q.
      apply Qlt_le_weak. apply power_compare2. omega. 
      apply QOrderedType.QOrder.le_trans with (1 # of_nat m2). apply H12.
      unfold Qle. simpl.
      assert(1 / eps *eps<= inject_Z (Z.of_nat x)*eps)%Q.
      apply Qmult_le_compat_r. apply H1. apply Qlt_le_weak. apply H0.
      assert(eps * /eps==1)%Q. apply Qmult_inv_r.
      unfold not. intros.  rewrite H14 in H0. 
      assert False. apply Qlt_irrefl with 0. apply H0. destruct H15.
      assert((1 / eps) * eps ==eps * / eps)%Q.
      assert(1 / eps==/eps)%Q. field. unfold not. intros.  rewrite H15 in H0. 
      assert False. apply Qlt_irrefl with 0. apply H0. destruct H16.
      rewrite<-H15. ring. rewrite H14 in H15. rewrite H15 in H13.
      unfold Qle in H13. simpl in H13.
      apply Z.le_trans with (Z.of_nat x * Qnum eps * 1)%Z.
      auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
      assert(Z.of_nat x <=Z.pos (of_nat m2))%Z.
      assert(x<=m2)%nat. omega. 
      destruct m2. simpl. assert(x=0)%nat by omega. rewrite H17.
      simpl. omega. rewrite<-Pos.of_nat_succ.
      rewrite Zpos_P_of_succ_nat. omega.
      apply Z.mul_le_mono_nonneg_l. unfold Qlt in H0. simpl in H0.
      rewrite Z.mul_1_r in H0. omega. apply H16.
      apply Qlt_le_trans with (1 # 2 ^ of_nat m2). auto. auto.
Qed.
  
Definition D2C (B:D1.Real):C1.Real :=
match B with
|Real_cons DCut H =>
Real_intro (fun n q=>exists N:Z,DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q)
(Cauchy_Dcut DCut H) end.
Theorem D2C_property3:forall (x y:D1.Real),
(x==y)%D->  ((D2C x)==(D2C y)).
Proof.
  intros. unfold "==". destruct x,y. simpl. intros.
  unfold D2.Req in H. destruct H. unfold Rle in H.
  unfold Rle in H3. exists 0%nat. intros.
  destruct H5,H6.
  assert(x=x0)%Z.
  assert(A0 (x # 2 ^ of_nat m) /\ ~ A0 (x + 1 # 2 ^ of_nat m)).
  { split. apply H. apply H5. unfold not. intros. 
  assert(A (x + 1 # 2 ^ of_nat m)). apply H3.
  apply H7. apply H5. apply H8. }
  assert(x<x0+1)%Z.
  { assert (x # 2 ^ of_nat m<x0 + 1 # 2 ^ of_nat m)%Q.
  apply Dcut_lt with A0. auto. apply H7. apply H6. unfold Qlt in H8. simpl in H8.
  apply Zmult_gt_0_lt_reg_r with (Z.pos (2 ^ of_nat m)). 
  assert(0<Z.pos (2 ^ of_nat m))%Z. apply Pos2Z.is_pos. 
  omega. apply H8. }
  assert(x0<x+1)%Z.
  { assert (x0 # 2 ^ of_nat m<x + 1 # 2 ^ of_nat m)%Q.
  apply Dcut_lt with A0. auto. apply H6. apply H7. unfold Qlt in H9. simpl in H9.
  apply Zmult_gt_0_lt_reg_r with (Z.pos (2 ^ of_nat m)). 
  assert(0<Z.pos (2 ^ of_nat m))%Z. apply Pos2Z.is_pos. 
  omega. apply H9. }
  omega.
  assert(q1==q2)%Q.
  assert(q1 == x # 2 ^ of_nat m)%Q. apply H5.
  assert(q2 == x0 # 2 ^ of_nat m)%Q. apply H6.
  rewrite H8. rewrite H9. rewrite H7. reflexivity.
  assert(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1=0)%Z.
  unfold Qeq in H8. rewrite H8. assert((Qnum q2 * QDen q1 - Qnum q2 * QDen q1)%Z = 0%Z).
  omega. ring.
  rewrite H9. assert(Z.abs 0 # Qden q1 * Qden q2 ==0)%Q.
  assert (Z.abs 0=0)%Z. reflexivity. rewrite H10. reflexivity.
  rewrite H10. apply H2.
Qed.
Theorem D2C_property1:forall (x y:D1.Real),
  ((D2C x)+(D2C y))==(D2C ( x+ y)).
Proof.
  intros. destruct x,y. unfold "==". unfold D2C. hnf. intros.
  assert(exists n:nat,(1/eps+1/eps<=inject_Z(Z.of_nat n))).
  apply Inject_lemmas.inject_Z_of_nat_le. destruct H2.
  exists (x+2)%nat. intros.
  destruct H5. unfold C3.CauchySeqPlus in H4.
  assert(exists (t:Z),A (t#2 ^ of_nat m)/\~A (t+1#2 ^ of_nat m)).
  apply Dcut_P. auto. destruct H6.
  assert(exists (t:Z),A0 (t#2 ^ of_nat m)/\~A0 (t+1#2 ^ of_nat m)).
  apply Dcut_P. auto. destruct H7.
  assert(q1==(x1 # 2 ^ of_nat m)+(x2 # 2 ^ of_nat m))%Q.
  apply H4. exists x1. split. apply H6. split. apply H6. reflexivity.
  exists x2. split. apply H7. split. apply H7. reflexivity.
  rewrite Qplus_sameden in H8. destruct H5. destruct H9.
  rewrite H8. rewrite H10.
  assert((x1 + x2 # 2 ^ of_nat m) - (x0 # 2 ^ of_nat m)==x1+x2-x0#2 ^ of_nat m)%Q.
  unfold Qminus. assert(- (x0 # 2 ^ of_nat m)=(-x0 # 2 ^ of_nat m))%Q.
  unfold Qeq. simpl. reflexivity. 
  rewrite H11. unfold Zminus. apply Qplus_sameden. rewrite H11.
  assert(-2<=x1+x2-x0)%Z.
  unfold D3.Cut_plus_Cut in H5,H9. destruct H5. destruct H5.
  assert(x3<x1 + 1 # 2 ^ of_nat m)%Q.
  apply Dcut_lt with A. apply H. apply H5. apply H6.
  assert(x4<x2 + 1 # 2 ^ of_nat m)%Q.
  apply Dcut_lt with A0. apply H0. apply H5. apply H7.
  assert(x3+x4<(x1 + 1 # 2 ^ of_nat m)+(x2 + 1 # 2 ^ of_nat m))%Q.
  apply Qplus_lt_le_compat. auto. apply Qlt_le_weak. auto.
  destruct H5. destruct H15. rewrite H16 in H14.
  rewrite Qplus_sameden in H14.
  assert(x0<x1 + 1 + (x2 + 1))%Z.
  unfold Qlt in H14. simpl in H14. apply Zmult_lt_reg_r with (Z.pos (2 ^ of_nat m)).
  apply Pos2Z.is_pos. apply H14. apply Zlt_le_weak.
  apply Zlt_0_minus_lt. rewrite <-Z.lt_0_sub in H17.
  assert(x1 + 1 + (x2 + 1) - x0=x1 + x2 - x0 - -2)%Z by omega.
  rewrite<-H18. auto.
  assert(x1+x2-x0<=2)%Z.
  unfold D3.Cut_plus_Cut in H5,H9. destruct H5. destruct H5.
  unfold not in H9.
  assert(~ A (x3+(1 # 2 ^ of_nat m))%Q).
  unfold not. intros. apply H9.
  exists (x3 + (1 # 2 ^ of_nat m))%Q,x4.
  split. apply H13. split. apply H5.
  destruct H5. destruct H14.
  assert(x3 + (1 # 2 ^ of_nat m) + x4 ==x3 +x4+ (1 # 2 ^ of_nat m))%Q by ring.
  rewrite H16. rewrite H15. apply Qplus_sameden.
  assert(~ A0(x4+(1 # 2 ^ of_nat m))%Q).
  unfold not. intros. apply H9.
  exists x3 ,(x4+ (1 # 2 ^ of_nat m))%Q.
  split. apply H5. split. apply H14.
  destruct H5. destruct H15.
  assert(x3 + (x4+(1 # 2 ^ of_nat m))==x3 +x4+ (1 # 2 ^ of_nat m))%Q by ring.
  rewrite H17. rewrite H16. apply Qplus_sameden.
  assert(x1 # 2 ^ of_nat m<x3 + (1 # 2 ^ of_nat m))%Q.
  apply Dcut_lt with A. auto. apply H6. apply H13.
  assert(x2 # 2 ^ of_nat m<x4 + (1 # 2 ^ of_nat m))%Q.
  apply Dcut_lt with A0. auto. apply H7. apply H14.
  assert((x1# 2 ^ of_nat m)+(x2# 2 ^ of_nat m)<(x3 + (1 # 2 ^ of_nat m))+(x4 +( 1 # 2 ^ of_nat m)))%Q.
  apply Qplus_lt_le_compat. auto. apply Qlt_le_weak. auto.
  destruct H5. destruct H18.
  assert(x3 + (1 # 2 ^ of_nat m) + (x4 + (1 # 2 ^ of_nat m))==x3 +x4+ (1 # 2 ^ of_nat m) +  (1 # 2 ^ of_nat m))%Q. ring. rewrite H20 in H17.
  rewrite H19 in H17.
  rewrite Qplus_sameden in H17.
  rewrite Qplus_sameden in H17.
  rewrite Qplus_sameden in H17.
  assert(x1+x2<x0 + 1 + 1)%Z.
  unfold Qlt in H17. simpl in H17. apply Zmult_lt_reg_r with (Z.pos (2 ^ of_nat m)).
  apply Pos2Z.is_pos. apply H17. apply Zlt_le_weak.
  apply Zlt_0_minus_lt. rewrite <-Z.lt_0_sub in H21.
  assert(x0 + 1 + 1 - (x1 + x2)= 2 - (x1 + x2 - x0))%Z by omega.
  rewrite<-H22. auto.
  assert(Qabs (x1 + x2 - x0 # 2 ^ of_nat m)<=2# 2 ^ of_nat m).
  unfold Qabs.
  assert(Z.abs (x1 + x2 - x0) <=2)%Z.
  apply Z.abs_le. omega.
  unfold Qle. simpl.
  rewrite Pos2Z.pos_xO.
  apply Z.mul_le_mono_pos_r. reflexivity. auto.
  apply Qle_lt_trans with (2 # 2 ^ of_nat m).
  apply H14.
  apply QOrderedType.QOrder.lt_trans with (2 # of_nat m).
  unfold Qlt. simpl. rewrite Pos2Z.pos_xO.
  assert( Z.pos (2 ^ of_nat m)~0= 2*Z.pos (2 ^ of_nat m))%Z. rewrite Pos2Z.pos_xO. reflexivity.
  rewrite H15. apply Zmult_lt_compat_l. reflexivity.
  apply Pos2Z.pos_lt_pos. apply power_compare1. 
      assert((2#1)*(1 / eps) *eps<= inject_Z (Z.of_nat x)*eps)%Q.
      apply Qmult_le_compat_r.
      assert(1 / eps + 1 / eps==(2 # 1) * (1 / eps))%Q. ring.
      rewrite<-H15. apply H2. apply Qlt_le_weak. apply H1.
      assert(eps * /eps==1)%Q. apply Qmult_inv_r.
      unfold not. intros.  rewrite H16 in H1. 
      assert False. apply Qlt_irrefl with 0. apply H1. destruct H17.
      assert((1 / eps) * eps ==eps * / eps)%Q.
      assert(1 / eps==/eps)%Q. field. unfold not. intros.  rewrite H17 in H1. 
      assert False. apply Qlt_irrefl with 0. apply H1. destruct H18.
      rewrite<-H17. ring. rewrite H16 in H17.
      assert((2 # 1) * (1 / eps) * eps==(1 / eps) * eps*(2#1))%Q. ring. rewrite H18 in H15.
      rewrite H17 in H15.
      unfold Qle in H15. simpl in H15.
      unfold Qlt. simpl.
      apply Z.le_lt_trans with (Z.of_nat x * Qnum eps * 1)%Z.
      auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
      assert(Z.of_nat x <Z.pos (of_nat m))%Z.
      assert(x<m)%nat. omega. 
      destruct m. simpl. assert(x=0)%nat by omega. rewrite H20.
      simpl. omega. rewrite<-Pos.of_nat_succ.
      rewrite Zpos_P_of_succ_nat. omega.
      apply Zmult_gt_0_lt_compat_l. unfold Qlt in H1. simpl in H1.
      rewrite Z.mul_1_r in H1. omega.
      apply H19.
Qed.
Theorem D2C_property6:D2C (RBase.Rzero)==0%R.
Proof.
  hnf. intros. 
  assert(exists n:nat,(1/eps<=inject_Z(Z.of_nat n)))%Q.
  apply Inject_lemmas.inject_Z_of_nat_le. 
  destruct H0. exists x%nat. intros.
  destruct H2. rewrite H3. assert(q1-0==q1)%Q. ring. rewrite H4.
  destruct H2. destruct H5. destruct H3,H4.
  assert(x0=-1)%Z.
  assert(x0<0)%Z. unfold Qlt in H2. simpl in H2. 
  rewrite Z.mul_1_r in H2. apply H2.
  apply Qnot_lt_le in H5. assert(0<=x0+1)%Z.
  unfold Qle in H5. simpl in H5. rewrite Z.mul_1_r in H5.
  apply H5. assert(-1<=x0)%Z. omega.
  assert(x0=-1\/~x0=-1)%Z by apply classic.
  destruct H8. auto.
  assert(-1<x0)%Z. apply Z.le_neq. split. auto. unfold not.
  intros. destruct H8. symmetry. apply H9.
  omega. rewrite H3 in H6. rewrite H6.
  simpl.  assert(1 # 2 ^ of_nat m<1#of_nat m)%Q.
  apply power_compare2. omega.
  apply Qlt_le_trans with (1 # of_nat m)%Q. auto.
  unfold Qle. simpl. 
  assert(1 / eps *eps<= inject_Z (Z.of_nat x)*eps)%Q.
  apply Qmult_le_compat_r. apply H0. apply Qlt_le_weak. apply H.
  assert(eps * /eps==1)%Q. apply Qmult_inv_r.
  unfold not. intros.  rewrite H8 in H. 
  assert False. apply Qlt_irrefl with 0. apply H. destruct H9.
  assert((1 / eps) * eps ==eps * / eps)%Q.
  assert(1 / eps==/eps)%Q. field. unfold not. intros.  rewrite H9 in H. 
  assert False. apply Qlt_irrefl with 0. apply H. destruct H10.
  rewrite<-H9. ring. rewrite H8 in H9. rewrite H9 in H7.
  unfold Qle in H8. simpl in H8.
  unfold Qle in H7. simpl in H7.
  apply Z.le_trans with (Z.of_nat x * Qnum eps * 1)%Z.
  auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
  apply Zmult_le_compat_l. 
  assert(Z.of_nat x <=Z.pos (of_nat m))%Z.
  assert(x<=m)%nat. omega. 
  destruct m. simpl. assert(x=0)%nat by omega. rewrite H11.
  simpl. omega. rewrite<-Pos.of_nat_succ.
  rewrite Zpos_P_of_succ_nat. omega. apply H10.
  apply Zlt_le_weak. unfold Qlt in H . simpl in H.
  rewrite Z.mul_1_r in H. auto.
Qed.
Notation "- a" :=(Ropp a):CReal_Scope. 
Notation "- a" :=(Dedekind.RArith.Ropp a):DReal_Scope.
Theorem D2C_property7:forall (x:D1.Real), D2C (-x)==-D2C x.
Proof.
  intros. assert(D2C (-x)+D2C x==-D2C x +D2C x).
  rewrite D2C_property1.
  assert(- x + x==RBase.Rzero)%D. rewrite D3.Rplus_comm.
  apply D3.Rplus_opp. 
  assert(D2C(-x+x)==D2C(RBase.Rzero))%C. apply D2C_property3. auto.
  rewrite H0. rewrite C3.Rplus_comm. rewrite C3.Rplus_opp_r.
  apply D2C_property6.
  apply C3.Rplus_inj_r with (D2C x). auto.
Qed.
Lemma Q2Zrounding:forall (x:Q),exists(y:Z),y#1<=x/\x<(y+1)#1.
Proof.
  intros. destruct Inject_lemmas.le_inject_Z with x.
  destruct Inject_lemmas.inject_Z_le with x.
  assert(x0<=x1)%Z. rewrite Zle_Qle. apply Qle_trans with x.
  auto. auto. assert(x0=x1\/~x0=x1) by apply classic. destruct H2.
  - exists x0. split. apply H. apply Qle_lt_trans with (inject_Z x1).
  auto. rewrite<-H2. unfold Qlt. simpl. lia.
  - assert(x0<x1)%Z by lia. assert(exists x:nat,x=Z.to_nat (x1-x0))%nat.
    exists ((Z.to_nat (x1- x0)))%nat. reflexivity. destruct H4.
    assert(forall (n:nat)(x0 x1:Z),((x0<x1)%Z->inject_Z x0<=x/\x<=inject_Z x1->(Z.to_nat (x1-x0)=n)%nat->exists y : Z, y # 1 <= x /\ x < y + 1 # 1)).
    intros. generalize dependent x3. generalize dependent x4.  induction n.
    + intros.
    assert False. assert(x4-x3<=0)%Z. 
    assert(0<x4-x3\/~0<x4-x3)%Z by apply classic.
    destruct H8. rewrite<-Z2Nat.inj_0 in H7. 
    rewrite Z2Nat.inj_le.  omega. omega. omega. omega. omega. destruct H8.
    + intros. assert(x <= inject_Z (x4-1)\/~x <= inject_Z (x4-1)) by apply classic.
      destruct H8. assert(x3=x4-1\/~x3=x4-1)%Z as P by apply classic .
      destruct P as [P|P].
      assert (x== x4#1\/~x==x4#1)%Q as P1 by apply classic. destruct P1 as [P1|P1].
      exists x4. split. rewrite P1. lra.
      rewrite P1. unfold Qlt. simpl. lia. 
      exists (x4-1)%Z. split. rewrite<-P. apply H6.
      assert(x4 - 1 + 1=x4)%Z as P2 by lia. rewrite P2.
      apply QOrderedType.QOrder.le_neq_lt. apply H6. auto. 
      apply IHn with (x4-1)%Z x3. 
      omega. split. apply H6. auto.
      assert(Z.to_nat (x4 - x3)=S (Z.to_nat(x4-1-x3))) as P1.
      rewrite<-Z2Nat.inj_succ. assert(x4-x3=Z.succ (x4 - 1 - x3))%Z as P2.
      lia. rewrite P2. reflexivity. lia.
      rewrite P1 in H7. lia. 
      assert (x== x4#1\/~x==x4#1)%Q by apply classic. destruct H9.
      exists x4. split. rewrite H9. lra.
      rewrite H9. unfold Qlt. simpl. lia. 
      exists (x4-1)%Z. split. apply QOrderedType.QOrder.not_ge_lt in H8.
      apply Qlt_le_weak. apply H8. assert(x4 - 1 + 1=x4)%Z by lia. rewrite H10.
      assert( x <= inject_Z x4) by apply H6. apply Qle_lt_or_eq in H11.
      destruct H11. apply H11. assert False. apply H9. apply H11. destruct H12.
    + 
    apply H5 with x2 x0 x1. auto. split. lra. lra. rewrite H4;reflexivity.
Qed.
Lemma D2Cmult_lemma1:forall(A A0:Q->Prop)(H:D1.Dedekind A)(H0:D1.Dedekind A0),
D3.PP A A0-> D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0) ==
D2C (D1.Real_cons A H * D1.Real_cons A0 H0) .
Proof.
  intros.
  hnf. intros. hnf in H1.
  assert(exists (t:Q),forall(n:nat)(q:Q)(N:Z),
A (N#(2^(of_nat n)))/\~A((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q->
Qabs q<t) as P1. apply D2C_Seqbounded. auto.
  assert(exists (t:Q),forall(n:nat)(q:Q)(N:Z),
A0 (N#(2^(of_nat n)))/\~A0((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q->
Qabs q<t) as P2. apply D2C_Seqbounded. auto.
  destruct P1 as [t1 P1]. destruct P2 as [t2 P2].
  assert(exists n:nat,((t1+t2+(3#1))/eps<=inject_Z(Z.of_nat n))).
  apply Inject_lemmas.inject_Z_of_nat_le. destruct H3. exists x.
  intros. destruct H6. destruct H6. destruct H7. hnf in H5.
  assert((exists N : Z,
        A (N # 2 ^ of_nat m) /\
        ~ A (N + 1 # 2 ^ of_nat m))). apply Dcut_P. auto.
        destruct H9.
  assert((exists N : Z,
        A0 (N # 2 ^ of_nat m) /\
        ~ A0 (N + 1 # 2 ^ of_nat m))). apply Dcut_P. auto.
        destruct H10.
  specialize H5 with (x1 # 2 ^ of_nat m)(x2 # 2 ^ of_nat m).
  assert(q1 == (x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m))%Q.
  { apply H5. exists x1. split. apply H9.  split. apply H9. reflexivity.
  exists x2. split. apply H10. split. apply H10. reflexivity. }
  rewrite H8. rewrite H11. unfold D3.Cut_mult in *.
  apply not_or_and in H7. destruct H7.
  apply not_and_or in H7.
  destruct H6.
  + assert(0<(x1 # 2 ^ of_nat m)\/~0<(x1 # 2 ^ of_nat m)) as S1 by apply classic.
  destruct S1 as [S1 |S1].
  ++ assert(0<(x2 # 2 ^ of_nat m)\/~0<(x2 # 2 ^ of_nat m)) as S2 by apply classic.
  destruct S2 as [S2|S2].
  +++
  { destruct H7. assert False. apply H7;auto.
  destruct H13. destruct H6. unfold Cut_multPP in H7,H13.
  destruct H13. destruct H13. 
  assert(x0 # 2 ^ of_nat m<(x1 + 1 # 2 ^ of_nat m)*(x2 + 1 # 2 ^ of_nat m))%Q.
  { apply Qle_lt_trans with (x3 * x4)%Q. lra. apply Qmult_lt_compat. lra. lra.
  apply Dcut_lt with A. auto. apply H13. apply H9. apply Dcut_lt with A0. auto.
  apply H13. apply H10. }
  unfold Qminus. assert(- (x0 # 2 ^ of_nat m)==- (x0+1 # 2 ^ of_nat m)+ (1 # 2 ^ of_nat m))%Q.
  { assert(- (x0 + 1 # 2 ^ of_nat m)==(- (x0 + 1) # 2 ^ of_nat m))%Q.
    reflexivity. rewrite H15. rewrite Qplus_sameden. assert(- (x0 + 1) + 1 =-x0)%Z.
    lia. rewrite H16. reflexivity. } rewrite H15. rewrite Qplus_assoc.
    apply Qle_lt_trans with (Qabs(
  (x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) +
   (- (x0 + 1 # 2 ^ of_nat m))) + Qabs(1 # 2 ^ of_nat m))%Q.
   apply Qabs_triangle.
   assert(Qabs (1 # 2 ^ of_nat m)==1 # 2 ^ of_nat m)%Q.
   { apply Qabs_pos. unfold Qle. simpl. lia. }
   rewrite H16.
   assert(Qabs ((x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + - (x0 + 1 # 2 ^ of_nat m))
   ==- ((x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + - (x0 + 1 # 2 ^ of_nat m)))%Q.
   { apply Qabs_neg. assert((x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + - (x0 + 1 # 2 ^ of_nat m) <= 0
   \/~(x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + - (x0 + 1 # 2 ^ of_nat m) <= 0)%Q.
   apply classic. destruct H17.
   + auto.
   + assert False. apply H7. exists (x1 # 2 ^ of_nat m),(x2 # 2 ^ of_nat m).
   split. auto. split. auto. split. apply H9. split. apply H10. lra. destruct H18. }
   rewrite H17.
   assert(- ((x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + - (x0 + 1 # 2 ^ of_nat m))==
   (x0 + 1 # 2 ^ of_nat m)-(x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m))%Q. lra.
   rewrite H18. destruct H17. destruct H18.
   assert((x0 + 1 # 2 ^ of_nat m)==(x0 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m))%Q.
   rewrite Qplus_sameden. reflexivity. rewrite H17. destruct H17. 
   apply Qlt_le_trans with ((x1 + 1 # 2 ^ of_nat m) * (x2 + 1 # 2 ^ of_nat m)+ (1 # 2 ^ of_nat m) - (x1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) +
(1 # 2 ^ of_nat m))%Q. lra.
   assert((x1 + 1 # 2 ^ of_nat m)==(x1 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m))%Q.
   rewrite Qplus_sameden. reflexivity. rewrite H17. destruct H17.
   assert((x2 + 1 # 2 ^ of_nat m)==(x2 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m))%Q.
   rewrite Qplus_sameden. reflexivity. rewrite H17. destruct H17.
   rewrite Qmult_plus_distr_l. rewrite Qmult_plus_distr_r. rewrite Qmult_plus_distr_r.
   assert((x1 # 2 ^ of_nat m) * (1 # 2 ^ of_nat m) +
((1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m) + (1 # 2 ^ of_nat m) * (1 # 2 ^ of_nat m)) +
(1 # 2 ^ of_nat m) +(1 # 2 ^ of_nat m) <= eps)%Q.
{ assert(0<(1 # 2 ^ of_nat m))%Q. { unfold Qlt. simpl. lia. }
assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert((x1 # 2 ^ of_nat m) * (1 # 2 ^ of_nat m)<t1* (1 # 2 ^ of_nat m))%Q.
{ apply Qmult_lt_compat_r. lra. assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. apply Qle_lt_trans with ( Qabs (x1 # 2 ^ of_nat m) ).
apply Qle_Qabs. auto. }
assert((1 # 2 ^ of_nat m) * (x2 # 2 ^ of_nat m)<(1 # 2 ^ of_nat m)*t2)%Q.
{ assert((1 # 2 ^ of_nat m) * t2==t2*(1 # 2 ^ of_nat m))%Q. lra. rewrite H19.
rewrite Qmult_comm. apply Qmult_lt_compat_r. lra. assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. apply Qle_lt_trans with ( Qabs (x2 # 2 ^ of_nat m) ).
apply Qle_Qabs. auto.
 }
assert((1 # 2 ^ of_nat m) * (1 # 2 ^ of_nat m)<=(1 # 2 ^ of_nat m))%Q.
{ apply Qle_trans with ((1 # 2 ^ of_nat m)*1)%Q. apply QArith_base_ext.Qmult_le_compat_l.
unfold Qle. simpl. lia. lra. lra. }

apply Qle_trans with (t1* (1 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m)*t2+(1 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m)+(1 # 2 ^ of_nat m))%Q.
lra. assert(t1 * (1 # 2 ^ of_nat m) + (1 # 2 ^ of_nat m) * t2 + (1 # 2 ^ of_nat m) +
(1 # 2 ^ of_nat m) + (1 # 2 ^ of_nat m)==(t1+t2+1+1+1)*(1 # 2 ^ of_nat m))%Q.
lra. rewrite H21. destruct H21. apply Qlt_le_weak.
  assert(1 # 2 ^ of_nat m<eps/(t1+t2+(3#1)))%Q.
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
  apply inject_compare with x.
  apply Qlt_shift_div_l. lra. lra. omega.
  assert((t1 + t2 + (3#1)) / eps==1 / (eps / (t1 + t2 + (3#1))))%Q.
  field. split. lra. lra. rewrite<-H21. apply H3.
  apply Qle_lt_trans with ((t1 + t2 + (3#1))*(1 # 2 ^ of_nat m))%Q. lra.
  assert(eps==(eps / (t1 + t2 + (3#1)))*(t1 + t2 + (3#1)))%Q. field.
  lra. rewrite H22. rewrite Qmult_comm. apply Qmult_lt_compat_r.
  lra. auto.
 }
lra.
   }
   +++ assert(x2 # 2 ^ of_nat m<=0) by lra.
   assert(x2# 2 ^ of_nat m == 0\/~x2# 2 ^ of_nat m==0)%Q. apply classic.
   destruct H14.
   - rewrite H14. destruct H7.
   -- assert False. apply H7. hnf. auto. destruct H15.
   -- unfold Cut_multPP in *. rewrite Qmult_0_r. destruct H6.
    destruct H15. destruct H15. assert(0<(1 # 2 ^ of_nat m))%Q. { unfold Qlt. simpl. lia. }
    assert(Qabs (0 - (x0 # 2 ^ of_nat m)) ==Qabs(x0 # 2 ^ of_nat m))%Q.
    assert((0 - (x0 # 2 ^ of_nat m)==- (x0 # 2 ^ of_nat m)))%Q. lra.
    rewrite H17.
    apply Qabs_opp. rewrite H17.
    apply QArith_base_ext.Qabs_Qlt_condition.
    split.
   --- assert(x0 + 1 # 2 ^ of_nat m <= x3 * x4\/~x0 + 1 # 2 ^ of_nat m <= x3 * x4)%Q.
   apply classic. destruct H18.
   ---- assert False. apply H7. exists x3,x4. split. apply H15. split. apply H15.
   split. apply H15. split. apply H15. apply H18. destruct H19.
   ---- apply QOrderedType.QOrder.not_ge_lt in H18. rewrite<-Qplus_sameden in H18.
   apply Qlt_trans with ((x3*x4)-(1 # 2 ^ of_nat m))%Q.
   * apply Qlt_trans with (- (1 # 2 ^ of_nat m))%Q. 
   { assert(1 # 2 ^ of_nat m<eps)%Q. 
   { apply Qlt_trans with ((t1 + t2 + 1 + 1 + 1) * (1 # 2 ^ of_nat m) )%Q.
   rewrite Qmult_comm. rewrite<-Qmult_1_l.
   assert(1 * (1 # 2 ^ of_nat m) * (t1 + t2 + 1 + 1 + 1)== (t1 + t2 + 1 + 1 + 1)*(1 # 2 ^ of_nat m))%Q.
   lra. rewrite H19.
   apply Qmult_lt_compat_r. lra.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } lra.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } 
  assert(1 # 2 ^ of_nat m<eps/(t1+t2+(3#1)))%Q.
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
  apply inject_compare with x.
  apply Qlt_shift_div_l. lra. lra. omega.
  assert((t1 + t2 + (3#1)) / eps==1 / (eps / (t1 + t2 + (3#1))))%Q.
  field. split. lra. lra. rewrite<-H19. apply H3.
  apply Qle_lt_trans with ((t1 + t2 + (3#1))*(1 # 2 ^ of_nat m))%Q. lra.
  assert(eps==(eps / (t1 + t2 + (3#1)))*(t1 + t2 + (3#1)))%Q. field.
  lra. rewrite H20. rewrite Qmult_comm. apply Qmult_lt_compat_r.
  lra. auto. }
   lra. }
   assert(0<x3*x4)%Q. apply QArith_base_ext.Qlt_mult0. lra. lra. lra.
   * lra.
   --- apply Qle_lt_trans with (x3 * x4)%Q. lra.
   apply Qlt_le_trans with ((x2 + 1 # 2 ^ of_nat m)*x3)%Q.
   rewrite Qmult_comm. apply Qmult_lt_compat_r. lra. apply Dcut_lt with A0.
   auto. apply H15. apply H10. unfold Qeq in H14. simpl in H14. 
   rewrite Z.mul_1_r in H14. rewrite H14. simpl.
   apply Qle_trans with ((1 # 2 ^ of_nat m) * (t1+(1 # 2 ^ of_nat m)))%Q.
   apply QArith_base_ext.Qmult_le_compat_l.
   { apply Qle_trans with (x1 + 1 # 2 ^ of_nat m).
   apply Qlt_le_weak. apply Dcut_lt with A. auto. apply H15. apply H9.
   rewrite<-Qplus_sameden. assert( x1 # 2 ^ of_nat m<t1)%Q.
   apply Qle_lt_trans with (Qabs(x1 # 2 ^ of_nat m)). apply Qle_Qabs.
   apply P1 with m x1. split. apply H9. split. apply H9. reflexivity.
   lra. } lra. apply Qle_trans with ((t1 + t2 + 1 + 1 + 1) * (1 # 2 ^ of_nat m) )%Q.
   rewrite Qmult_comm. apply Qlt_le_weak. apply Qmult_lt_compat_r. lra.
   assert((1 # 2 ^ of_nat m) <=1)%Q. { unfold Qle. simpl. lia. } 
   assert(0<t2)%Q. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } lra. apply Qlt_le_weak.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
  assert(1 # 2 ^ of_nat m<eps/(t1+t2+(3#1)))%Q.
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
  apply inject_compare with x.
  apply Qlt_shift_div_l. lra. lra. omega.
  assert((t1 + t2 + (3#1)) / eps==1 / (eps / (t1 + t2 + (3#1))))%Q.
  field. split. lra. lra. rewrite<-H18. apply H3.
  apply Qle_lt_trans with ((t1 + t2 + (3#1))*(1 # 2 ^ of_nat m))%Q. lra.
  assert(eps==(eps / (t1 + t2 + (3#1)))*(t1 + t2 + (3#1)))%Q. field.
  lra. rewrite H19. rewrite Qmult_comm. apply Qmult_lt_compat_r.
  lra. auto.
   - assert(x2 # 2 ^ of_nat m<0)%Q by lra . 
   assert(0<x2+1 # 2 ^ of_nat m)%Q. apply Dcut_lt with A0.
   auto. apply H1. apply H10. unfold Qlt in H15,H16. simpl in H15,H16.
   omega. 
   ++ assert(x1 # 2 ^ of_nat m<=0) by lra.
   assert(x1# 2 ^ of_nat m == 0\/~x1# 2 ^ of_nat m==0)%Q. apply classic.
   destruct H14.
   - rewrite H14. destruct H7.
   -- assert False. apply H7. hnf. auto. destruct H15.
   -- unfold Cut_multPP in *. rewrite Qmult_0_l. destruct H6.
    destruct H15. destruct H15. assert(0<(1 # 2 ^ of_nat m))%Q. { unfold Qlt. simpl. lia. }
    assert(Qabs (0 - (x0 # 2 ^ of_nat m)) ==Qabs(x0 # 2 ^ of_nat m))%Q.
    assert((0 - (x0 # 2 ^ of_nat m)==- (x0 # 2 ^ of_nat m)))%Q. lra.
    rewrite H17.
    apply Qabs_opp. rewrite H17.
    apply QArith_base_ext.Qabs_Qlt_condition.
    split.
   --- assert(x0 + 1 # 2 ^ of_nat m <= x3 * x4\/~x0 + 1 # 2 ^ of_nat m <= x3 * x4)%Q.
   apply classic. destruct H18.
   ---- assert False. apply H7. exists x3,x4. split. apply H15. split. apply H15.
   split. apply H15. split. apply H15. apply H18. destruct H19.
   ---- apply QOrderedType.QOrder.not_ge_lt in H18. rewrite<-Qplus_sameden in H18.
   apply Qlt_trans with ((x3*x4)-(1 # 2 ^ of_nat m))%Q.
   * apply Qlt_trans with (- (1 # 2 ^ of_nat m))%Q. 
   { assert(1 # 2 ^ of_nat m<eps)%Q. 
   { apply Qlt_trans with ((t1 + t2 + 1 + 1 + 1) * (1 # 2 ^ of_nat m) )%Q.
   rewrite Qmult_comm. rewrite<-Qmult_1_l.
   assert(1 * (1 # 2 ^ of_nat m) * (t1 + t2 + 1 + 1 + 1)== (t1 + t2 + 1 + 1 + 1)*(1 # 2 ^ of_nat m))%Q.
   lra. rewrite H19.
   apply Qmult_lt_compat_r. lra.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } lra.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } 
  assert(1 # 2 ^ of_nat m<eps/(t1+t2+(3#1)))%Q.
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
  apply inject_compare with x.
  apply Qlt_shift_div_l. lra. lra. omega.
  assert((t1 + t2 + (3#1)) / eps==1 / (eps / (t1 + t2 + (3#1))))%Q.
  field. split. lra. lra. rewrite<-H19. apply H3.
  apply Qle_lt_trans with ((t1 + t2 + (3#1))*(1 # 2 ^ of_nat m))%Q. lra.
  assert(eps==(eps / (t1 + t2 + (3#1)))*(t1 + t2 + (3#1)))%Q. field.
  lra. rewrite H20. rewrite Qmult_comm. apply Qmult_lt_compat_r.
  lra. auto. }
   lra. }
   assert(0<x3*x4)%Q. apply QArith_base_ext.Qlt_mult0. lra. lra. lra.
   * lra.
   --- apply Qle_lt_trans with (x3 * x4)%Q. lra.
   apply Qlt_le_trans with ((x1 + 1 # 2 ^ of_nat m)*x4)%Q.
   apply Qmult_lt_compat_r. lra. apply Dcut_lt with A.
   auto. apply H15. apply H9. unfold Qeq in H14. simpl in H14. 
   rewrite Z.mul_1_r in H14. rewrite H14. simpl.
   apply Qle_trans with ((1 # 2 ^ of_nat m) * (t2+(1 # 2 ^ of_nat m)))%Q.
   apply QArith_base_ext.Qmult_le_compat_l.
   { apply Qle_trans with (x2 + 1 # 2 ^ of_nat m).
   apply Qlt_le_weak. apply Dcut_lt with A0. auto. apply H15. apply H10.
   rewrite<-Qplus_sameden. assert( x2 # 2 ^ of_nat m<t2)%Q.
   apply Qle_lt_trans with (Qabs(x2 # 2 ^ of_nat m)). apply Qle_Qabs.
   apply P2 with m x2. split. apply H10. split. apply H10. reflexivity.
   lra. } lra. apply Qle_trans with ((t1 + t2 + 1 + 1 + 1) * (1 # 2 ^ of_nat m) )%Q.
   rewrite Qmult_comm. apply Qlt_le_weak. apply Qmult_lt_compat_r. lra.
   assert((1 # 2 ^ of_nat m) <=1)%Q. { unfold Qle. simpl. lia. } 
   assert(0<t1)%Q. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. } lra. apply Qlt_le_weak.
  assert(0<t1)%Q as K1. { assert(Qabs(x1 # 2 ^ of_nat m)<t1)%Q.  apply P1 with m x1 .
split. apply H9. split. apply H9. reflexivity. assert(0<=Qabs (x1 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
assert(0<t2)%Q as K2. { assert(Qabs(x2 # 2 ^ of_nat m)<t2)%Q.  apply P2 with m x2 .
split. apply H10. split. apply H10. reflexivity. assert(0<=Qabs (x2 # 2 ^ of_nat m))%Q.
apply Qabs_nonneg. lra. }
  assert(1 # 2 ^ of_nat m<eps/(t1+t2+(3#1)))%Q.
  apply Qlt_le_trans with (1#of_nat m). apply power_compare2. omega.
  apply inject_compare with x.
  apply Qlt_shift_div_l. lra. lra. omega.
  assert((t1 + t2 + (3#1)) / eps==1 / (eps / (t1 + t2 + (3#1))))%Q.
  field. split. lra. lra. rewrite<-H18. apply H3.
  apply Qle_lt_trans with ((t1 + t2 + (3#1))*(1 # 2 ^ of_nat m))%Q. lra.
  assert(eps==(eps / (t1 + t2 + (3#1)))*(t1 + t2 + (3#1)))%Q. field.
  lra. rewrite H19. rewrite Qmult_comm. apply Qmult_lt_compat_r.
  lra. auto.
   - assert(x1 # 2 ^ of_nat m<0)%Q by lra . 
   assert(0<x1+1 # 2 ^ of_nat m)%Q. apply Dcut_lt with A.
   auto. apply H1. apply H9. unfold Qlt in H15,H16. simpl in H15,H16.
   omega.
   +
  destruct H6. destruct H6. hnf in H1,H6. destruct H6.
  assert False. hnf in H6. destruct H6. destruct H6.
  apply H15. apply Dedekind_properties2 with 0.
  auto. split. apply H1. lra. destruct H15.
  destruct H6. destruct H6. hnf in H1,H6. destruct H6.
  assert False. hnf in H14. destruct H14. destruct H14.
  apply H15. apply Dedekind_properties2 with 0.
  auto. split. apply H1. lra. destruct H15.
  destruct H6. destruct H6. hnf in H1,H6. destruct H6.
  assert False. hnf in H14. destruct H14. destruct H14.
  apply H15. apply Dedekind_properties2 with 0.
  auto. split. apply H1. lra. destruct H15.
  destruct H6. hnf in H1,H6. destruct H6. destruct H6.
  assert False. apply H6. apply H1. destruct H15.
  destruct H6. assert False. apply  H6. apply H1. destruct H15.
Qed.  
  
Lemma D2Cmult_lemma2:forall(A A0:Q->Prop)(H:D1.Dedekind A)(H0:D1.Dedekind A0),
D3.PN A A0-> D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0) ==
D2C (D1.Real_cons A H * D1.Real_cons A0 H0) .
Proof.
  intros.
  assert(-(D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0)) ==
-D2C (D1.Real_cons A H * D1.Real_cons A0 H0))%C.
  rewrite C3.Rmult_comm.
  rewrite C2.Ropp_mult_distr.
  rewrite<- D2C_property7. rewrite<- D2C_property7.
  assert(D2C (- (D1.Real_cons A H * D1.Real_cons A0 H0))==D2C ( (D1.Real_cons A H *(- D1.Real_cons A0 H0)))).
  apply D2C_property3.
  apply D3.Rmult_opp_r. rewrite H2.
  rewrite C3.Rmult_comm.
  apply D2Cmult_lemma1.
  hnf.  hnf in H1. apply H1.
  rewrite C3.Ropp_involutive. rewrite H2. rewrite<- C3.Ropp_involutive. reflexivity.
Qed.
Lemma D2Cmult_lemma3:forall(A A0:Q->Prop)(H:D1.Dedekind A)(H0:D1.Dedekind A0),
D3.NP A A0-> D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0) ==
D2C (D1.Real_cons A H * D1.Real_cons A0 H0) .
Proof.
  intros.
  assert(-(D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0)) ==
-D2C (D1.Real_cons A H * D1.Real_cons A0 H0))%C.
  rewrite C2.Ropp_mult_distr.
  rewrite<- D2C_property7. rewrite<- D2C_property7.
  assert(D2C (- (D1.Real_cons A H * D1.Real_cons A0 H0))==D2C ( (-(D1.Real_cons A H) *( D1.Real_cons A0 H0)))).
  apply D2C_property3.
  apply D3.Rmult_opp_l. rewrite H2.
  apply D2Cmult_lemma1.
  hnf.  hnf in H1. apply H1.
  rewrite C3.Ropp_involutive. rewrite H2. rewrite<- C3.Ropp_involutive. reflexivity.
Qed.
Lemma D2Cmult_lemma4:forall(A A0:Q->Prop)(H:D1.Dedekind A)(H0:D1.Dedekind A0),
D3.NN A A0-> D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0) ==
D2C (D1.Real_cons A H * D1.Real_cons A0 H0) .
Proof.
  intros.
  assert(--(D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0)) ==
--D2C (D1.Real_cons A H * D1.Real_cons A0 H0))%C.
  rewrite C2.Ropp_mult_distr.
  rewrite C3.Rmult_comm. rewrite C2.Ropp_mult_distr.
  rewrite<- D2C_property7. rewrite<- D2C_property7.
  rewrite<-D2C_property7. rewrite<- D2C_property7.
  assert(D2C (-- (D1.Real_cons A H * D1.Real_cons A0 H0))==D2C ( (-(D1.Real_cons A H) *(- D1.Real_cons A0 H0)))).
  apply D2C_property3.
  rewrite D3.Rmult_opp_r. rewrite D3.Rmult_opp_l. reflexivity. rewrite H2.
  rewrite C3.Rmult_comm.
  apply D2Cmult_lemma1.
  hnf.  hnf in H1. apply H1.
  rewrite C3.Ropp_involutive. rewrite H2. rewrite<- C3.Ropp_involutive. reflexivity.
Qed.
Lemma D2Cmult_lemma5:forall(A A0:Q->Prop)(H:D1.Dedekind A)(H0:D1.Dedekind A0),
D3.O A A0-> D2C (D1.Real_cons A H) * D2C (D1.Real_cons A0 H0) ==
D2C (D1.Real_cons A H * D1.Real_cons A0 H0) .
Proof.
  intros. hnf. hnf in*. intros.
  assert(exists t : Q,
  forall (n : nat) (q : Q) (N : Z),
  A (N # 2 ^ of_nat n) /\
  ~ A (N + 1 # 2 ^ of_nat n) /\ (q == N # 2 ^ of_nat n)%Q -> 
  Qabs q < t) as P1. apply D2C_Seqbounded. auto.
  assert(exists t : Q,
  forall (n : nat) (q : Q) (N : Z),
  A0 (N # 2 ^ of_nat n) /\
  ~ A0 (N + 1 # 2 ^ of_nat n) /\ (q == N # 2 ^ of_nat n)%Q -> 
  Qabs q < t) as P2. apply D2C_Seqbounded. auto. 
  destruct P1 as [t1 P1].
  destruct P2 as [t2 P2].
 
  assert(exists n:nat,((t1+t2+1)/eps<=inject_Z(Z.of_nat n))) as P3.
  apply Inject_lemmas.inject_Z_of_nat_le.
  destruct P3 as [s P3].
  exists (s+1)%nat.
  intros. hnf in H4. destruct H5.
  unfold D3.Cut_mult in H5. destruct H5.
  assert(exists N : Z,
        A (N # 2 ^ of_nat m) /\
        ~ A (N + 1 # 2 ^ of_nat m) ). apply Dcut_P.
  auto.
  assert(exists N : Z,
        A0 (N # 2 ^ of_nat m) /\
        ~ A0 (N + 1 # 2 ^ of_nat m) ). apply Dcut_P.
  auto.
  destruct H7,H8.
  assert(q1==(x0 # 2 ^ of_nat m)*(x1 # 2 ^ of_nat m))%Q.
  apply H4. exists x0. split. apply H7. split. apply H7. reflexivity.
  exists x1. split. apply H8. split. apply H8. reflexivity.
  destruct H6. apply Decidable.not_or in H6.
  destruct H6. apply Decidable.not_or in H11.
  destruct H11. apply Decidable.not_or in H12.
  destruct H12. apply Decidable.not_or in H13.
  destruct H13.
  assert(~ D3.Cut_mult0 A A0 (x + 1 # 2 ^ of_nat m)).
  unfold not. intros. apply H14. split;auto;auto.
  destruct H1.
  - destruct H5. assert False. destruct H5.
  unfold D3.PP in H5. destruct H5. destruct H1.
  apply H1. auto. destruct H16. destruct H5.
  assert False. destruct H5. unfold D3.NP in H5.
  destruct H1. apply H17. apply H5. destruct H16.
  destruct H5. assert False. 
  destruct H5. unfold D3.PN in H5. destruct H1. apply H1.
  apply H5. destruct H16.
  destruct H5. assert False. 
  destruct H5. unfold D3.NN in H5. destruct H1. 
  apply H17. apply H5. destruct H16.
  destruct H5.
  assert(x=-1)%Z. 
  destruct H1. unfold D3.Cut_mult0 in H15.
  apply QOrderedType.QOrder.not_gt_le in H15.
  unfold Qle in H15. simpl in H15.
  assert(-1<=x)%Z. lia.
  unfold D3.Cut_mult0 in H16. unfold Qlt in H16.
  simpl in H16. lia. rewrite H17 in H10.
  unfold Cut_opp in H1. destruct H1.
  assert(forall x:Q ,x<0->A x). intros.
  assert(A x2\/~A x2) by apply classic. destruct H20.
  auto. assert False. apply H18. exists (-x2)%Q.
  split. lra. assert(- 0 + - - x2==x2)%Q by lra.
  rewrite H21. auto. destruct H21.
  assert(x0=-1)%Z. destruct H7.
  assert((x0 # 2 ^ of_nat m)<0). apply Dcut_lt with A. auto.
  apply H7. auto. unfold Qlt in H21. simpl in H21.
  assert(0<=x0 + 1 # 2 ^ of_nat m). apply QOrderedType.QOrder.not_gt_le.
  unfold not . intros. destruct H8. apply H20.
  apply H19. auto. unfold Qle in H22. simpl in H22. lia.
  rewrite H9,H10. rewrite H20.
  assert(0<t1)%Q as P5.
  apply Qle_lt_trans with (Qabs (x0 # 2 ^ of_nat m)).
  apply Qabs_nonneg.
  apply P1 with m x0. split. apply H7. split. apply H7. reflexivity.
  assert(0<t2)%Q as P6. 
  apply Qle_lt_trans with (Qabs (x1 # 2 ^ of_nat m)).
  apply Qabs_nonneg.
  apply P2 with m x1. split. apply H8. split. apply H8. reflexivity.
  assert((-1 # 2 ^ of_nat m) * (x1 # 2 ^ of_nat m) - (-1 # 2 ^ of_nat m)==
  (-1 # 2 ^ of_nat m) * ((x1 # 2 ^ of_nat m) -1))%Q. lra.
  rewrite H21. rewrite Qabs_Qmult.
  assert((x1 # 2 ^ of_nat m) - 1==0\/~(x1 # 2 ^ of_nat m) - 1==0)%Q by apply classic.
  destruct H22. rewrite H22. simpl. lra.
  assert(Qabs (-1 # 2 ^ of_nat m)<eps/Qabs ((x1 # 2 ^ of_nat m) - 1)).
  assert(Qabs (-1 # 2 ^ of_nat m)==Qabs (1 # 2 ^ of_nat m))%Q.
  assert((-1 # 2 ^ of_nat m)==-(1 # 2 ^ of_nat m))%Q. unfold Qeq. simpl. reflexivity.
  rewrite H23. apply Qabs_opp. rewrite H23. rewrite Qabs_pos. apply Qlt_le_trans with (1#of_nat m).
  apply power_compare2. omega.
  apply Qle_trans with (eps/(t1+t2+1)).
  apply inject_compare with s. 
  
  assert(0<(t1 + t2 + 1))%Q by lra.
  apply Qlt_shift_div_l. auto. rewrite Qmult_0_l. auto.
  omega.
  assert(1 / (eps / (t1 + t2 + 1)) ==(t1 + t2 + 1) / eps )%Q.
  field. split. lra. lra.
  rewrite H24. auto. 
  assert(Qabs ((x1 # 2 ^ of_nat m) - 1)<t1+t2+1)%Q.
  apply Qle_lt_trans with (Qabs (x1 # 2 ^ of_nat m) + Qabs 1)%Q.
  Search Qabs Qminus Qplus.
  assert(x1 # 2 ^ of_nat m==(x1 # 2 ^ of_nat m)-0)%Q as P7 by lra.
  assert(Qabs 1==Qabs (0-1))%Q as P8. simpl. reflexivity.
  assert(Qabs ((x1 # 2 ^ of_nat m)) ==Qabs ((x1 # 2 ^ of_nat m) - 0) )%Q as P9.
  rewrite<-P7. reflexivity. rewrite P8. rewrite P9.
  apply QArith_base_ext.Qabs_triangle_extend. 
  assert(Qabs( x1 # 2 ^ of_nat m)<t2). apply P2 with m x1.
  split.  apply H8. split. apply H8. reflexivity. 
  assert(Qabs 1==1)%Q. simpl. reflexivity. rewrite H25. lra.
  apply Qle_shift_div_l.
  apply C1.Qnot_0_abs_pos. auto.
  unfold Qdiv. 
  assert(eps * / (t1 + t2 + 1) * Qabs ((x1 # 2 ^ of_nat m) - 1)==eps *Qabs ((x1 # 2 ^ of_nat m) - 1)*/ (t1 + t2 + 1))%Q. lra.
  rewrite H25. apply Qle_shift_div_r. auto.
  lra.
  apply Qmult_le_l. auto. lra.
  unfold Qle. simpl. omega.
  apply Qlt_le_trans with (eps / (Qabs ((x1 # 2 ^ of_nat m) - 1))* Qabs ((x1 # 2 ^ of_nat m) - 1))%Q.
  apply Qmult_lt_compat_r.
  apply C1.Qnot_0_abs_pos. auto. auto. 
  Search Qle Qeq.
  assert(eps / Qabs ((x1 # 2 ^ of_nat m) - 1) * Qabs ((x1 # 2 ^ of_nat m) - 1) ==eps)%Q.
  field. apply QArith_base_ext.Qnot_0_abs. auto. rewrite H24.
  apply Qle_refl.
  - destruct H5. assert False. destruct H5.
  unfold D3.PP in H5. destruct H5. destruct H1.
  apply H1. auto. destruct H16. destruct H5.
  assert False. destruct H5. unfold D3.NP in H5.
  destruct H1. apply H1. apply H5. destruct H16.
  destruct H5. assert False. 
  destruct H5. unfold D3.PN in H5. destruct H1. apply H17.
  apply H5. destruct H16.
  destruct H5. assert False. 
  destruct H5. unfold D3.NN in H5. destruct H1. 
  apply H17. apply H5. destruct H16.
  destruct H5.
  assert(x=-1)%Z. 
  destruct H1. unfold D3.Cut_mult0 in H15.
  apply QOrderedType.QOrder.not_gt_le in H15.
  unfold Qle in H15. simpl in H15.
  assert(-1<=x)%Z. lia.
  unfold D3.Cut_mult0 in H16. unfold Qlt in H16.
  simpl in H16. lia. rewrite H17 in H10.
  unfold Cut_opp in H1. destruct H1.
  assert(forall x:Q ,x<0->A0 x). intros.
  assert(A0 x2\/~A0 x2) by apply classic. destruct H20.
  auto. assert False. apply H18. exists (-x2)%Q.
  split. lra. assert(- 0 + - - x2==x2)%Q by lra.
  rewrite H21. auto. destruct H21.
  assert(x1=-1)%Z. destruct H8.
  assert((x1 # 2 ^ of_nat m)<0). apply Dcut_lt with A0. auto.
  apply H8. auto. unfold Qlt in H21. simpl in H21.
  assert(0<=x1 + 1 # 2 ^ of_nat m). apply QOrderedType.QOrder.not_gt_le.
  unfold not . intros. destruct H7. apply H20.
  apply H19. auto. unfold Qle in H22. simpl in H22. lia.
  rewrite H9,H10. rewrite H20.
  assert(0<t1)%Q as P5.
  apply Qle_lt_trans with (Qabs (x0 # 2 ^ of_nat m)).
  apply Qabs_nonneg.
  apply P1 with m x0. split. apply H7. split. apply H7. reflexivity.
  assert(0<t2)%Q as P6. 
  apply Qle_lt_trans with (Qabs (x1 # 2 ^ of_nat m)).
  apply Qabs_nonneg.
  apply P2 with m x1. split. apply H8. split. apply H8. reflexivity.
  assert((x0 # 2 ^ of_nat m) * (-1 # 2 ^ of_nat m) - (-1 # 2 ^ of_nat m)==
  (-1 # 2 ^ of_nat m) * ((x0 # 2 ^ of_nat m) -1))%Q. lra.
  rewrite H21. rewrite Qabs_Qmult.
  assert((x0 # 2 ^ of_nat m) - 1==0\/~(x0 # 2 ^ of_nat m) - 1==0)%Q by apply classic.
  destruct H22. rewrite H22. simpl. lra.
  assert(Qabs (-1 # 2 ^ of_nat m)<eps/Qabs ((x0 # 2 ^ of_nat m) - 1)).
  assert(Qabs (-1 # 2 ^ of_nat m)==Qabs (1 # 2 ^ of_nat m))%Q.
  assert((-1 # 2 ^ of_nat m)==-(1 # 2 ^ of_nat m))%Q. unfold Qeq. simpl. reflexivity.
  rewrite H23. apply Qabs_opp. rewrite H23. rewrite Qabs_pos. apply Qlt_le_trans with (1#of_nat m).
  apply power_compare2. omega.
  apply Qle_trans with (eps/(t1+t2+1)).
  apply inject_compare with s. 
  
  assert(0<(t1 + t2 + 1))%Q by lra.
  apply Qlt_shift_div_l. auto. rewrite Qmult_0_l. auto.
  omega.
  assert(1 / (eps / (t1 + t2 + 1)) ==(t1 + t2 + 1) / eps )%Q.
  field. split. lra. lra.
  rewrite H24. auto. 
  assert(Qabs ((x0 # 2 ^ of_nat m) - 1)<t1+t2+1)%Q.
  apply Qle_lt_trans with (Qabs (x0 # 2 ^ of_nat m) + Qabs 1)%Q.
  Search Qabs Qminus Qplus.
  assert(x0 # 2 ^ of_nat m==(x0 # 2 ^ of_nat m)-0)%Q as P7 by lra.
  assert(Qabs 1==Qabs (0-1))%Q as P8. simpl. reflexivity.
  assert(Qabs ((x0 # 2 ^ of_nat m)) ==Qabs ((x0 # 2 ^ of_nat m) - 0) )%Q as P9.
  rewrite<-P7. reflexivity. rewrite P8. rewrite P9.
  apply QArith_base_ext.Qabs_triangle_extend. 
  assert(Qabs( x0 # 2 ^ of_nat m)<t1). apply P1 with m x0.
  split.  apply H7. split. apply H7. reflexivity. 
  assert(Qabs 1==1)%Q. simpl. reflexivity. rewrite H25. lra.
  apply Qle_shift_div_l.
  apply C1.Qnot_0_abs_pos. auto.
  unfold Qdiv. 
  assert(eps * / (t1 + t2 + 1) * Qabs ((x0 # 2 ^ of_nat m) - 1)==eps *Qabs ((x0 # 2 ^ of_nat m) - 1)*/ (t1 + t2 + 1))%Q. lra.
  rewrite H25. apply Qle_shift_div_r. auto.
  lra.
  apply Qmult_le_l. auto. lra.
  unfold Qle. simpl. omega.
  apply Qlt_le_trans with (eps / (Qabs ((x0 # 2 ^ of_nat m) - 1))* Qabs ((x0 # 2 ^ of_nat m) - 1))%Q.
  apply Qmult_lt_compat_r.
  apply C1.Qnot_0_abs_pos. auto. auto. 
  Search Qle Qeq.
  assert(eps / Qabs ((x0 # 2 ^ of_nat m) - 1) * Qabs ((x0 # 2 ^ of_nat m) - 1) ==eps)%Q.
  field. apply QArith_base_ext.Qnot_0_abs. auto. rewrite H24.
  apply Qle_refl.
Qed.
Theorem D2C_property2:forall (x y:D1.Real),
 (D2C x)*(D2C y)==(D2C (x * y)).
Proof.
  intros.
  destruct x,y. 
  assert(D3.PP A A0\/D3.NP A A0\/D3.PN A A0\/D3.NN A A0\/D3.O A A0).
  apply Rmult_situation. auto. auto.
  destruct H1. apply D2Cmult_lemma1;auto.
  destruct H1. apply D2Cmult_lemma3;auto.
  destruct H1. apply D2Cmult_lemma2;auto.
  destruct H1. apply D2Cmult_lemma4;auto.
  apply D2Cmult_lemma5;auto.
Qed.

Notation "a <= b" :=(Rle a b):CReal_Scope.
Notation "a < b" :=(Rlt a b):CReal_Scope.
Notation "a <= b" :=(Dedekind.ROrder.Rle a b):DReal_Scope.
Notation "a < b" :=(Dedekind.ROrder.Rlt a b):DReal_Scope.

Theorem D2C_property4:forall (x y:D1.Real),
(x<y)%D->  ((D2C x)<(D2C y)).
Proof.
  intros. hnf.  destruct x,y. hnf in H. destruct H. destruct H2.
  destruct H2. simpl. unfold CauchySeqPlus. unfold Cauchy_opp.
  assert(exists t:Q,A0 t/\x<t)%Q. apply Dedekind_properties3. auto. auto.
  destruct H4. destruct H4.
  exists ((1#2)*(x0-x))%Q. split.
  - lra.
  - assert(exists n:nat,(1/(x0-x)<=inject_Z(Z.of_nat n)))%Q as Hi. apply Inject_lemmas.inject_Z_of_nat_le.
    destruct Hi as [t Hi].
    exists (t+1)%nat. intros.
    assert(exists N : Z, A0 (N # 2 ^ of_nat n) /\ ~ A0 (N + 1 # 2 ^ of_nat n)).
    apply Dcut_P.  auto. 
    assert(exists N : Z, A (N # 2 ^ of_nat n) /\ ~ A (N + 1 # 2 ^ of_nat n)).
    apply Dcut_P. auto. destruct H8. destruct H9.
    specialize H7 with (x1 # 2 ^ of_nat n)%Q (-x2 # 2 ^ of_nat n)%Q.
    assert((q == (x1 # 2 ^ of_nat n) + (-x2 # 2 ^ of_nat n)))%Q. apply H7.
    exists x1. split. apply H8. split. apply H8. reflexivity. intros.
    destruct  H10. destruct H10. destruct H11. assert(x2=x3)%Z.
    assert(x2# 2 ^ of_nat n<x3+1# 2 ^ of_nat n)%Q.
    apply Dcut_lt with A. auto. apply H9. auto.
    assert(x3# 2 ^ of_nat n<x2+1# 2 ^ of_nat n)%Q.
    apply Dcut_lt with A. auto. auto. apply H9.
    assert(x2<x3+1)%Z. unfold Qlt in H13. simpl in H13.
    apply Zmult_lt_reg_r with  (Z.pos (2 ^ of_nat n)).
    apply Pos2Z.is_pos. auto.
    assert(x3<x2+1)%Z. unfold Qlt in H14. simpl in H14.
    apply Zmult_lt_reg_r with  (Z.pos (2 ^ of_nat n)).
    apply Pos2Z.is_pos. auto.
    omega.
    rewrite H12. rewrite H13. reflexivity.
    rewrite H10. rewrite Qplus_sameden.
    destruct H8,H9,H10.
    assert(1 # 2 ^ of_nat n <= (1 # 2) * (x0 - x)\/~1 # 2 ^ of_nat n <= (1 # 2) * (x0 - x))%Q by apply classic.
    destruct H10.
    assert(x0-x<((x1+1)+-x2)# 2 ^ of_nat n)%Q.
    assert(x0<(x1+1)# 2 ^ of_nat n)%Q. apply Dcut_lt with A0.
    auto. auto. auto.
    assert(x2# 2 ^ of_nat n<x)%Q.
    apply Dcut_lt with A.
    auto. auto. auto.
    assert(-x< -(x2# 2 ^ of_nat n))%Q. lra.
    assert(x1 + 1 + - x2 # 2 ^ of_nat n==((x1 + 1)# 2 ^ of_nat n) + -( x2 # 2 ^ of_nat n))%Q.
    assert(- (x2 # 2 ^ of_nat n)==(- x2 # 2 ^ of_nat n))%Q.
    unfold Qeq. simpl. reflexivity. rewrite H16.
    rewrite Qplus_sameden. reflexivity. rewrite H16. lra.
    assert((1 # 2) * (x0 - x)+ (1 # 2) * (x0 - x)<= (x1 + - x2 # 2 ^ of_nat n)+(1 # 2) * (x0 - x))%Q.
    assert((1 # 2) * (x0 - x) + (1 # 2) * (x0 - x) ==x0-x)%Q. lra.
    rewrite H14. apply Qlt_le_weak. apply Qlt_le_trans with (x1 + 1 + - x2 # 2 ^ of_nat n)%Q.
    auto. assert(x1 + 1 + - x2 # 2 ^ of_nat n ==(x1 + - x2 # 2 ^ of_nat n)+(1 # 2 ^ of_nat n))%Q.
    rewrite Qplus_sameden. assert(x1 + 1 + - x2=x1 + - x2 + 1)%Z.
    omega. rewrite H15. reflexivity. rewrite H15.
    apply Qplus_le_r. auto.
    apply Qplus_le_l with ((1 # 2) * (x0 - x))%Q. auto.
    apply QOrderedType.QOrder.not_ge_lt in H10.
    apply Qlt_le_weak. apply Qlt_le_trans with (1 # 2 ^ of_nat n)%Q.
    auto.
    assert(x2<x1)%Z.
    assert(x2<x1+1)%Z.
    assert(x2#2 ^ of_nat n<x)%Q. apply Dcut_lt with A.
    auto. auto. auto.
    assert(x0<x1+1#2 ^ of_nat n)%Q. apply Dcut_lt with A0.
    auto. auto. auto. 
    assert(x2#2 ^ of_nat n<x1+1#2 ^ of_nat n)%Q. lra.
    unfold Qlt in H15. simpl in H15.
    apply Zmult_lt_reg_r with (Z.pos (2 ^ of_nat n)).
    apply Pos2Z.pos_is_pos. auto.
    assert(x2<=x1)%Z. omega. apply Zle_lt_or_eq in H14. destruct H14.
    auto. assert False.
    destruct H13,H10. apply H11. rewrite<-H14. rewrite<- H14 in H8.
    assert(x2 # 2 ^ of_nat n<x)%Q.
    apply Dcut_lt with A. auto. auto. auto.
    assert(x2 + 1 # 2 ^ of_nat n<x0)%Q.
    assert(1 # 2 ^ of_nat n<x0-x)%Q.
    apply Qlt_le_trans with (1 # of_nat n).
    apply power_compare2. omega.
    assert(exists q:Q,q==x0-x)%Q as Hj. exists (x0-x);reflexivity.
    destruct Hj as [s Hj]. rewrite<- Hj in*. unfold Qle. simpl.
    assert(1<=inject_Z (Z.of_nat t)*s)%Q as Hk.
    assert(1==1 / s*s)%Q. assert(s * /s==1)%Q. apply Qmult_inv_r.
    unfold not. intros.  rewrite H13 in Hj. lra.
    assert(1 / s==/s)%Q. field. unfold not. intros. lra.
    rewrite H15. symmetry. rewrite Qmult_comm.
    apply H13. rewrite H13. apply Qmult_le_compat_r. auto. rewrite Hj. lra.
    unfold Qle in Hk. simpl in Hk. rewrite Z.mul_1_r in Hk.
    apply Z.le_trans with (Z.of_nat t * Qnum s)%Z. auto.
    rewrite Z.mul_comm. apply Z.mul_le_mono_nonneg_l.
    assert(0<=s)%Q. lra. unfold Qle in H13. simpl in H13.
    rewrite Z.mul_1_r in H13. auto.
    destruct n. omega. rewrite <-Pos.of_nat_succ.
    rewrite Zpos_P_of_succ_nat. apply Z.le_trans with (Z.of_nat n).
    apply inj_le. omega. apply Z.le_succ_diag_r.
    assert(x2 + 1 # 2 ^ of_nat n ==(x2 # 2 ^ of_nat n)+( 1 # 2 ^ of_nat n ))%Q.
    rewrite Qplus_sameden. reflexivity. rewrite H15. lra. 
    apply Dedekind_properties2 with x0.
    auto. split. auto. lra. 
    destruct H15.
    unfold Qle. simpl.
    assert(Z.pos (2 ^ of_nat n)=1*Z.pos (2 ^ of_nat n))%Z.
    rewrite Z.mul_1_l. reflexivity. rewrite H14.
    apply Z.mul_le_mono_nonneg_r.
    rewrite Z.mul_1_l. apply Pos2Z.is_nonneg.
    lia.
Qed.
Theorem D2C_property5:forall (x y:D1.Real),
(x<=y)%D->  ((D2C x)<=(D2C y)).
Proof.
  intros. apply D3.Rle_lt_eq in H. destruct H.
  - assert(D2C x == D2C y). apply D2C_property3. auto.
    hnf. right. auto.
  - hnf. left. apply D2C_property4. auto.
Qed.


Theorem D2C_property8:D2C (RBase.Rone)==1%R.
Proof.
  hnf. intros. 
  assert(exists n:nat,(1/eps<=inject_Z(Z.of_nat n)))%Q.
  apply Inject_lemmas.inject_Z_of_nat_le. 
  destruct H0. exists x%nat. intros.
  destruct H2. rewrite H3.
  destruct H2. destruct H4. destruct H3.
  assert(q1-1==-1#2 ^ of_nat m)%Q.
  unfold Qlt in H2,H4.
  simpl in H2,H4. rewrite Z.mul_1_r in H2,H4.
  assert(x0= Z.pos (2 ^ of_nat m)-1)%Z.
  omega.
  rewrite H3 in H5. rewrite H5. 
  assert((Z.pos (2 ^ of_nat m) - 1 # 2 ^ of_nat m) - 1==(Z.pos (2 ^ of_nat m) - 1 -Z.pos (2 ^ of_nat m) # 2 ^ of_nat m))%Q.
  unfold Qeq. simpl. rewrite Z.mul_1_r. rewrite Pos.mul_1_r. unfold Z.sub.
  rewrite Pos2Z.opp_pos. reflexivity.
  rewrite H6. assert(Z.pos (2 ^ of_nat m) - 1 - Z.pos (2 ^ of_nat m) =-1)%Z. omega.
  rewrite H7. reflexivity.
  rewrite H3.
  simpl.  assert(1 # 2 ^ of_nat m<1#of_nat m)%Q.
  apply power_compare2. omega.
  apply Qlt_le_trans with (1 # of_nat m)%Q. auto.
  unfold Qle. simpl. 
  assert(1 / eps *eps<= inject_Z (Z.of_nat x)*eps)%Q.
  apply Qmult_le_compat_r. apply H0. apply Qlt_le_weak. apply H.
  assert(eps * /eps==1)%Q. apply Qmult_inv_r.
  unfold not. intros.  rewrite H8 in H. 
  assert False. apply Qlt_irrefl with 0. apply H. destruct H9.
  assert((1 / eps) * eps ==eps * / eps)%Q.
  assert(1 / eps==/eps)%Q. field. unfold not. intros.  rewrite H9 in H. 
  assert False. apply Qlt_irrefl with 0. apply H. destruct H10.
  rewrite<-H9. ring. rewrite H8 in H9. rewrite H9 in H7.
  unfold Qle in H8. simpl in H8.
  unfold Qle in H7. simpl in H7.
  apply Z.le_trans with (Z.of_nat x * Qnum eps * 1)%Z.
  auto. rewrite Z.mul_1_r. rewrite Z.mul_comm.
  apply Zmult_le_compat_l. 
  assert(Z.of_nat x <=Z.pos (of_nat m))%Z.
  assert(x<=m)%nat. omega. 
  destruct m. simpl. assert(x=0)%nat by omega. rewrite H11.
  simpl. omega. rewrite<-Pos.of_nat_succ.
  rewrite Zpos_P_of_succ_nat. omega. apply H10.
  apply Zlt_le_weak. unfold Qlt in H . simpl in H.
  rewrite Z.mul_1_r in H. auto.
Qed.
Lemma notD2Czero :forall (x:D1.Real)(H:~(x==RBase.Rzero)%D),~D2C x==0%R.
Proof.
  intros. unfold not. intros. apply H.
  assert(~ x<RBase.Rzero)%D. unfold not. intro. apply D2C_property4 in H1.
  rewrite H0 in H1. rewrite D2C_property6 in H1.
  apply C2.Rlt_irrefl with 0%R;auto.
  assert(~ RBase.Rzero<x)%D. unfold not. intro. apply D2C_property4 in H2.
  rewrite H0 in H2. rewrite D2C_property6 in H2.
  apply C2.Rlt_irrefl with 0%R;auto.
  apply D2.Rnot_lt_le in H1. apply D3.Rle_lt_eq in H1.
  destruct H1. symmetry. auto. assert False.
  apply H2;auto. destruct H3.
Qed.
Theorem D2C_property9:forall (x:D1.Real)(H:~(x==RBase.Rzero)%D), D2C (Dedekind.RArith.Rinv x H)==Rinv (exist _ (D2C x) (notD2Czero x H )%R).
Proof.
  intros. assert(D2C (Dedekind.RArith.Rinv x H)*(D2C x)==(/ exist (fun a0 : Real => ~ (a0 == 0)%C) (D2C x) (notD2Czero x H))%R*(D2C x))%C.
  rewrite D2C_property2.
  rewrite C3.Rmult_comm. rewrite C3.Rmult_inv_r'.
  assert((Dedekind.RArith.Rinv x H) * x==RBase.Rone)%D.
  rewrite D3.Rmult_comm. apply D3.Rmult_inv.
  apply D2C_property3 in H0. rewrite H0. apply D2C_property8.
  apply C3.Rmult_inj_r with (D2C x). apply notD2Czero. auto. auto.
Qed.




