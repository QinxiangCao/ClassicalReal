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

(*MCS refers to "monotone convergence sequence" *)

Record MCS (Sequp:nat->Q->Prop)(Seqdown:nat->Q->Prop):Prop:={
Pu1:forall(x:nat),exists (y:Q),Sequp x y/\(forall (z:Q),~z==y->~ Sequp x z);
Pu2:forall(x:nat),forall(y z:Q),y==z->Sequp x y->Sequp x z;
Pu3:(forall (n:nat)(p q:Q),Sequp n p->Sequp (S n) q->p<=q);
Pd1:forall(x:nat),exists (y:Q),Seqdown x y/\(forall (z:Q),~z==y->~ Seqdown x z);
Pd2:forall(x:nat),forall(y z:Q),y==z->Seqdown x y->Seqdown x z;
Pd3:(forall (n:nat)(p q:Q),Seqdown n p->Seqdown (S n) q->q<=p);
Pclose:forall (eps:Q),eps>0->(exists (N:nat),forall (n:nat)(p q:Q),(n>N)%nat->
Sequp n p->Seqdown n q->Qabs(p-q)<eps);}.

Inductive Real : Type :=
| Real_intro (x1 x2 : nat->Q ->Prop) (H:MCS x1 x2).

Definition Real_equiv (x1 x2:Real):=
match x1, x2 with
  | Real_intro Seqa1 Seqa2 H1,
    Real_intro Seqb1 Seqb2 H2 =>
      forall(eps:Q),eps>0->
      (exists N:nat,forall m  a b ,(m>N)%nat-> Seqa1 m a -> Seqb1 m b->Qabs(a-b)<eps)
                        end.

Notation "a == b" :=(Real_equiv a b).

Definition Rle (x1 x2:Real):=
match x1, x2 with
  | Real_intro Seqa1 Seqa2 H1,
    Real_intro Seqb1 Seqb2 H2 =>
      exists N:nat,forall m  a b ,(m>N)%nat-> Seqa1 m a -> Seqb1 m b->a<=b
                        end.

Notation "a <= b" :=(Rle a b).

Definition SeqPlus (A B: nat -> Q->Prop): (nat->Q->Prop) :=
  fun n q=> exists(a b:Q),A n a/\B n b/\(a+b==q)%Q.

Theorem MCSplusMCS:forall (a b c d:nat->Q->Prop),
MCS a b->MCS c d->MCS (SeqPlus a c) (SeqPlus b d).
Proof.
  intros. split.
- intros. destruct H. destruct H0. destruct Pu4 with x.
  destruct Pu7 with x. destruct H. destruct H0. exists (x0+x1).
  split.
  + unfold SeqPlus. exists x0. exists x1. split. apply H. split.
    apply H0. reflexivity.
  + intros. unfold SeqPlus. unfold not. intros. apply H3. destruct H4.
    destruct H4. destruct H4. destruct H5. assert(x2==x0\/~x2==x0)%Q.
    { apply classic. } destruct H7. assert(x3==x1\/~x3==x1)%Q.
    { apply classic. } destruct H8. rewrite<-H7. rewrite<-H8.
    rewrite H6. reflexivity. apply H2 in H8. apply H8 in H5.
    destruct H5. apply H1 in H7. apply H7 in H4. destruct H4. 
    (*only finish 1/7*)
Admitted.

Fixpoint Rplus (A B:Real):Real:=
match A,B with
|Real_intro Seqa1 Seqa2 H1,
    Real_intro Seqb1 Seqb2 H2 =>
Real_intro (SeqPlus Seqa1 Seqb1) (SeqPlus Seqa2 Seqb2) 
  (MCSplusMCS Seqa1 Seqa2 Seqb1 Seqb2 H1 H2) end.

Notation "A + B" := (Rplus A B).

Definition Seq_opp (A : nat->Q -> Prop) : nat->Q -> Prop :=
  (fun x q => A x (-q)).

Theorem MCS_opp : forall (A B:nat-> Q -> Prop) , 
MCS A  B -> MCS (Seq_opp B) (Seq_opp A).
Proof.
Admitted.

Definition Ropp (a : Real) : Real :=
  match a with
    | Real_intro A B H => Real_intro (Seq_opp B)(Seq_opp A)(MCS_opp A B H)
  end.

Definition Rminus (A B:Real):Real:=
Rplus A (Ropp B).

Notation "a - b":=(Rminus a b).

Definition SeqMult (A B: nat -> Q->Prop): (nat->Q->Prop) :=
  fun n q=> exists(a b:Q),A n a/\B n b/\(a*b==q)%Q.

Theorem MCSMultMCS:forall (a b c d:nat->Q->Prop),
MCS a b->MCS c d->MCS (SeqMult a c) (SeqMult b d).
Proof.
Admitted.

Fixpoint Rmult (A B:Real):Real:=
match A,B with
|Real_intro Seqa1 Seqa2 H1,
    Real_intro Seqb1 Seqb2 H2 =>
Real_intro (SeqMult Seqa1 Seqb1) (SeqMult Seqa2 Seqb2) 
  (MCSMultMCS Seqa1 Seqa2 Seqb1 Seqb2 H1 H2) end.

Notation "A * B" := (Rmult A B).

Definition Seq_inv (A : nat->Q -> Prop) : nat->Q -> Prop :=
  (fun x q => A x (Qinv q)).   (*Here I encounter problems*)

Theorem Q2R :forall (q:Q),(MCS (fun n x=>x==q) (fun n x=>x==q))%Q.
Proof.
intros. split.
  - intros. exists q. split. reflexivity. intros.
    unfold not. intros. apply H. rewrite H0. reflexivity.
  - intros. rewrite<-H0. rewrite H. reflexivity.
  - intros. rewrite H. rewrite H0. apply Qle_refl.
  - intros. exists q. split. reflexivity. intros. apply H.
  - intros. rewrite<-H. rewrite<-H0. reflexivity.
  - intros. rewrite H. rewrite<-H0. apply Qle_refl.
  - intros. exists O. intros. rewrite H1. rewrite H2.
    assert((q-q)==0)%Q. { unfold Qminus. apply Qplus_opp_r. }
    rewrite H3. simpl. apply H.
Qed.




