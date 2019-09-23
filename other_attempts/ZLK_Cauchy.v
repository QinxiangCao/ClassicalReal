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



Record Cauchy (Seq :nat->Q->Prop):Prop:={
P1:forall(x:nat),exists (y:Q),Seq x y/\(forall (z:Q),~z==y->~ Seq x z);
P2:forall(eps:Q),eps>0->(exists(N:nat),forall (m n:nat)(a b:Q),Seq m a->Seq n b ->
    (m>N)%nat->(n>N)%nat-> Qabs(a-b)<eps);
}.

Inductive Real:Type :=
|Real_intro (Seq:nat->Q->Prop) (H:Cauchy Seq).

Definition Real_equiv (x1 x2 : Real) : Prop :=
  match x1, x2 with
  | Real_intro CSeq1 H1,
    Real_intro CSeq2 H2 =>
      forall(eps:Q),eps>0->
      (exists N:nat,forall m  a b ,(m>N)%nat-> CSeq1 m a -> CSeq2 m b->Qabs(a-b)<eps)
                        end.
  

(*Some basic definition & properties of relations*)

Definition relation (X: Type) := X -> X -> Prop.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* We show that the equiv we've defined is an equivalence relation*)

Theorem Real_def_refl: reflexive Real_equiv.
Proof. unfold reflexive. unfold Real_equiv.
  intros. destruct a. destruct H. intros. destruct P4 with eps.
  apply H. exists x. intros. apply H0 with m m. apply H2.
  apply H3. apply H1. apply H1.
Qed.

Theorem Real_def_symm: symmetric Real_equiv.
Proof. unfold symmetric. unfold Real_equiv.
  intros. destruct a as [Seqa Ha]. destruct b as [Seqb Hb].
  intros. apply H in H0. destruct H0. exists x. intros.
  replace (Qabs(a-b)) with( Qabs(b-a)). apply H0 with m . apply H1.
  apply H3. apply H2. apply Qabs_Qminus. 
Qed.
(*A helping lemma in Qabs-related proofs.*)
Lemma Qabs_triangle_extend: forall (a b c:Q), Qabs (a - c) <=
   Qabs (a - b) + Qabs (b - c).
Proof. intros.
    assert (Heq: a - c == (a - b) + (b - c)) by ring.
    rewrite Heq.
    apply Qabs_triangle.
Qed.
Lemma eps_divide_2_positive: forall (eps:Q), 0 < eps -> eps * (1 # 2) > 0.
Proof. intros. unfold Qmult. unfold Qlt. simpl.
    rewrite <- Zmult_assoc. simpl. apply H.
Qed.
Lemma eps_over_2_plus : forall (eps:Q),  eps == eps *(1#2) + eps *(1#2).
Proof. intros. rewrite <- Qmult_plus_distr_r. unfold Qplus.
  simpl. assert (His1:(4 # 4) == 1) by reflexivity.
  rewrite His1. rewrite Qmult_1_r. reflexivity.
Qed.

Theorem Real_def_trans: transitive Real_equiv.
Proof. unfold transitive. unfold Real_equiv.
  intros a b c Hab Hbc. destruct a as [Seqa Ha].
  destruct b as [Seqb Hb]. destruct c as [Seqc Hc]. intros.
  destruct (Hab _ (eps_divide_2_positive eps H)) as [n1 H1].
  destruct (Hbc _ (eps_divide_2_positive eps H)) as [n2 H2].

assert (H7: eps == eps *(1#2) + eps *(1#2)) by (apply eps_over_2_plus).



Admitted.


Theorem Real_equiv_holds: equivalence Real_equiv.
Proof. unfold equivalence. split.
- apply Real_def_refl.
- split.
  + apply Real_def_symm.
  + apply Real_def_trans.
Qed.

Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_scope with R.
(** Make sure that your scope name is spelled correctly. -- Qinxiang *)
(*Next, define the plus operation *)
Definition CauchySeqPlus (A B: nat -> Q->Prop): (nat->Q->Prop) :=
  fun n q=> exists(a b:Q),A n a/\B n b/\a+b==q.

Theorem Cauchy_Plus_Cauchy: forall A B, Cauchy A -> Cauchy B
  -> Cauchy (CauchySeqPlus A B).

Proof. 
Admitted.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqPlus A B) (Cauchy_Plus_Cauchy A B HA HB)
                          end
  end.
Notation "A + B" := (Rplus A B).
Theorem Cauchy_Q : forall x1 : Q , Cauchy (fun n q=> q=x1).
Proof.
  split.
  - intros. exists x1. split.
    reflexivity. intros. unfold not. intros. 
    rewrite H0 in H. apply H. apply Qeq_refl.
  - intros. exists O. intros. rewrite H0. rewrite H1.
    assert(x1-x1==0). {unfold Qminus. apply Qplus_opp_r. }
    rewrite H4. simpl. apply H.
Qed.

Definition Rzero : Real := Real_intro (fun n q=> q=0) (Cauchy_Q 0).

Definition Rone : Real := Real_intro (fun n q => q = 1) (Cauchy_Q 1).

(** Next, we will define the plus operation and the mult operation. *)
(** First, we will define order of Real and proof some theorem about the order.*)
Definition Rle (a b:Real) : Prop :=
  match a with
    | Real_intro A HA => match b with
                    | Real_intro B HB => 
                    exists N:nat,(forall m  a b ,(m>N)%nat-> A m a -> B m b->a<=b)
                        end
  end.

Notation "a <= b" := (Rle a b).

Definition Rlt (a b:Real) : Prop :=
  match a with
    | Real_intro A HA => match b with
                          | Real_intro B HB => (forall m a b , A m a -> B m b->a<b)
                        end
  end.

Notation "a < b" := (Rlt a b).

Theorem Req:forall(A B:Real),
 A<= B/\B<= A<->(A==B)%R.
Proof.
Admitted.

Theorem Rle_refl: forall x : Real, x <= x.
Proof.
  intros.
  destruct x.
  unfold Rle.
  exists O. intros. destruct H. destruct P3 with m.
  destruct H. assert(a==x\/~a==x). apply classic.
  assert(b==x\/~b==x). apply classic.
  destruct H4. destruct H5. rewrite H4.  rewrite H5.
  apply Qle_refl. apply H3 in H5. apply H5 in H2.
  destruct H2. apply H3 in H4. apply H4 in H1. destruct H1.
Qed.

Theorem Rlt_le_weak: forall x y : Real, x < y -> x <= y.
Proof.
Admitted.

Theorem Rle_trans: forall x y z : Real, x <= y -> y <= z -> x <= z.
Proof.
Admitted.

Theorem Rlt_trans: forall x y z : Real, x < y -> y < z -> x < z.
Proof.
Admitted.

Theorem Rle_not_lt: forall x y : Real, x <= y -> ~ y < x.
Proof.
Admitted.

Theorem Rlt_not_le: forall x y : Real, x < y -> ~ y <= x.
Proof.
Admitted.

Theorem Rle_antisym: forall x y : Real, x <= y -> y <= x ->( x == y)%R.
Proof.
Admitted.

Theorem Rle_lt_trans: forall x y z : Real, x <= y -> y < z -> x < z.
Proof.
Admitted.
Theorem Rlt_le_trans: forall x y z : Real, x < y -> y <= z -> x < z.
Proof.
Admitted.
Theorem not_exists_not_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) <-> (forall x, P x).
Proof.
  split.
  - apply not_ex_not_all.
  - unfold not. intros. destruct H0. apply H0. apply H.
Qed.

Theorem not_exists_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, P x) <-> (forall x, ~ P x).
Proof.
  split.
  - apply not_ex_all_not.
  - unfold not. intros. destruct H0. apply H in H0. apply H0.
Qed.

Theorem Rnot_le_lt: forall x y : Real, ~ x <= y -> y < x.
Proof.
  Admitted.

Theorem Rnot_lt_le: forall x y : Real, ~ x < y -> y <= x.
Proof.
  Admitted.



Theorem Rplus_O_r : forall a : Real, (a + Rzero== a)%R.
Proof.
  Admitted.
Theorem Rplus_comm : forall a b : Real, (a + b == b + a)%R.
Proof.
Admitted.

Theorem Rplus_assoc : forall a b c : Real, (a + b + c == a + (b + c))%R.
Proof.
  Admitted.
Definition Seq_opp (A : nat->Q -> Prop) : nat->Q -> Prop :=
  (fun x q => A x (-q))
.

Theorem Cauchy_opp : forall A :nat-> Q -> Prop , Cauchy A -> Cauchy (Seq_opp A).
Proof.
  intros. unfold Seq_opp. destruct H. split.
- intros. destruct P3 with x. exists( - x0).
  assert((- - x0)==x0). rewrite Qopp_opp. reflexivity.
  split. destruct H.  
Admitted.

Definition Ropp (a : Real) : Real :=
  match a with
    | Real_intro A HA => Real_intro (Seq_opp A) (Cauchy_opp A HA)
  end.

Theorem Rplus_opp :
  forall a : Real, (a + (Ropp a) == Rzero)%R.
Proof.
  Admitted.

Theorem Rplus_l_compat :
  forall a b c : Real, (b == c -> a + b == a + c)%R.
Proof. 
  Admitted.

Theorem Rplus_compat_l :
  forall a b c : Real, (a + b == a + c -> b == c)%R.
Proof. 
Admitted.

Definition Rminus (A B :Real):Real:=
(A+Ropp B)%R.

Notation "a - b" :=(Rminus a b).

Definition Seq_mult (A B :nat->Q->Prop):nat->Q->Prop:=
fun m q=>exists (a b:Q),A m a/\B m b/\q==a*b.


Theorem Cauchy_mult:forall(A B:nat->Q->Prop),
Cauchy A->Cauchy B->Cauchy (Seq_mult A B).
Proof. Admitted. 
Definition Rmult(a b:Real):Real:=
match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (Seq_mult A B) (Cauchy_mult A B HA HB)
                          end
  end.

Notation "a * b":=(Rmult a b).



