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
From Coq Require Import PArith.BinPosDef.
Import Pos.

Module C := Cauchy.RBase.
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

Check Inject_lemmas.le_inject_Z. SearchAbout inject_Z Qdiv.
Notation "a == b" :=(D2.Req a b):DReal_Scope.
Notation "a + b" :=(D3.Rplus a b):DReal_Scope.
Notation "a * b" :=(D3.Rmult a b):DReal_Scope.
Notation "a == b" :=(C1.Real_equiv a b):CReal_Scope.
Notation "a + b" :=(C1.Rplus a b):CReal_Scope.
Notation "a * b" :=(C1.Rmult a b):CReal_Scope.
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
Lemma power_compare1:forall (n:nat),(of_nat n<2^of_nat n+1)%positive.
Proof.
  induction n.
  - simpl. reflexivity.
  - assert(2 ^ of_nat (S n) =2 ^ of_nat n+2 ^ of_nat n)%positive.
    Locate "^".
    Search BinPos.Pos.pow.
    admit.
    assert(of_nat (S n) =(of_nat n)+1)%positive.
    admit.
    rewrite H,H0.
    apply Pos.le_lt_trans with (2 ^ of_nat n + of_nat n )%positive. admit.
    assert(2 ^ of_nat n + 2 ^ of_nat n + 1=2 ^ of_nat n + (2 ^ of_nat n + 1))%positive.
    rewrite<- Pos.add_assoc. reflexivity. rewrite H1.
    apply Pos.add_lt_mono_l. auto.
Admitted.
Lemma power_compare2:forall (n:nat),(n>0)%nat->(1#(2^of_nat n+1)<1#of_nat n)%Q.
Proof.
  intros. assert(of_nat n<2 ^ of_nat n + 1)%positive. apply power_compare1.
  unfold Qlt. simpl. apply H0.
Qed.
Lemma Dcut_P: forall (n:positive)(Dcut:Q->Prop),Dedekind Dcut ->
exists (m:Z),Dcut (m#n)/\~Dcut (m+1#n).
Proof.
  intros. assert(exists (t:Z),Dcut (t#n)).
  { destruct H. destruct Dedekind_properties1. Search Z Q. destruct H.
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
      Search Z.to_nat . 
      apply Z2Nat.inj_sub. omega.
      rewrite H7. omega. rewrite H6 in H4. apply eq_add_S. apply H4. }
  apply H2 with (Z.to_nat(x0-x)) x x0. apply H0. apply H1. reflexivity.
Qed.
Definition CSeq_pre (DCut: Q -> Prop): nat -> Q -> Prop :=
(fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).

Theorem Cauchy_Dcut :forall (DCut:Q->Prop),
Dedekind DCut->Cauchy (CSeq_pre DCut). (*(fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).
*)
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
      assert(q1<q2)%Q. admit.
      assert(Qabs (q1 - q2)==q2-q1)%Q. assert(q1-q2<0). 
      unfold Qlt. simpl. unfold Qlt in H10. 
      assert((Qnum q1 * QDen q2 + - Qnum q2 * QDen q1) * 1 =(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1))%Z. omega.
      rewrite H11. 
      assert(Qnum q1 * QDen q2 + - Qnum q2 * QDen q1=Qnum q1 * QDen q2  - Qnum q2 * QDen q1)%Z.
      unfold Zminus. assert(- Qnum q2 * QDen q1=- (Qnum q2 * QDen q1))%Z.
      ring. ring. rewrite H12. apply Z.lt_sub_0. apply H10.
      assert(Qabs (q1 - q2)==-(q1-q2))%Q. rewrite Qabs_neg.
      reflexivity. apply Qlt_le_weak. apply H11.
      rewrite H12. ring. 
      assert(q2-q1<1#2^of_nat m1)%Q. admit.
      rewrite H11.
      assert(1 # 2 ^ of_nat m1<=eps)%Q. admit.
      apply QOrderedType.QOrder.lt_le_trans with (1 # 2 ^ of_nat m1).
      auto. auto.
  + assert(m2<m1)%nat. omega. (*similar to the former situation*)
Admitted.
  
Definition D2C (B:D1.Real):C1.Real :=
match B with
|Real_cons DCut H =>
Real_intro (fun n q=>exists N:Z,DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q)
(Cauchy_Dcut DCut H) end.

Theorem C2D_properity1:forall (x y:D1.Real),
<<<<<<< HEAD
  ((D2C x)+(D2C y))==(D2C ( x+ y)).
=======
 C.Real_equiv(C3.Rplus (D2C x)(D2C y))(D2C (D3.Rplus x y)).
>>>>>>> origin/master
Proof.
  intros. destruct x,y. unfold "==". unfold D2C. hnf. intros.
  assert(exists n:nat,(1/eps+1/eps<=inject_Z(Z.of_nat n))).
  apply Inject_lemmas.inject_Z_of_nat_le. destruct H2.
  exists (x+1)%nat. intros.
  destruct H5. unfold C1.CauchySeqPlus in H4.
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
  assert(0<=x1+x2-x0)%Z. admit.
  assert(x1+x2-x0<=2)%Z. admit.
  assert(Qabs (x1 + x2 - x0 # 2 ^ of_nat m)<=2# 2 ^ of_nat m).
  admit.
  apply Qle_lt_trans with (2 # 2 ^ of_nat m).
  apply H14.
  admit.
Admitted. 
Theorem C2D_properity2:forall (x y:D1.Real),
<<<<<<< HEAD
 (D2C x)*(D2C y)==(D2C (x * y)).
=======
 C.Real_equiv (C3.Rmult(D2C x)(D2C y))(D2C (D3.Rmult x y)).
>>>>>>> origin/master
Proof.
  intros. destruct x,y. unfold "==". hnf. intros.
  exists 0%nat. (*remaining*)
  intros.
  destruct H4. destruct H4. destruct H5.
  unfold C1.CauchySeqMult in H3.
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
  apply H3. exists x0. split. apply H7. split. apply H7. reflexivity.
  exists x1. split. apply H8. split. apply H8. reflexivity.
  
              
Admitted.

Theorem C2D_properity3:forall (x y:D1.Real),
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
(* Qed.
 *)


