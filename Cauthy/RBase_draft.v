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

From Coq Require Import Classes.RelationClasses.

Import ListNotations.


Definition Cauchy (CSeq :nat -> Q) : Prop :=
  forall (eps:Q), eps > 0 -> (exists (n:nat),
     forall (m1 m2:nat), (m1 > n)%nat /\ (m2 > n)%nat
         -> Qabs ((CSeq m1) + (- CSeq m2)) < eps).

Inductive Cauchy_Seq : Type :=
| Cauchy_Seq_intro (x : nat -> Q) (H:Cauchy x).

Definition Cauchy_Seq_equiv (x1 x2 : Cauchy_Seq) : Prop :=
  match x1 with
  | Cauchy_Seq_intro CSeq1 H1 =>
    match x2 with
    | Cauchy_Seq_intro CSeq2 H2 =>
      forall (eps:Q), eps>0 -> (exists (n:nat),
        forall (m:nat), (m > n)%nat ->
         Qabs (CSeq1 m + - CSeq2 m) < eps) end end.

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

Theorem Cauchy_Seq_def_refl: reflexive Cauchy_Seq_equiv.
Proof. unfold reflexive. unfold Cauchy_Seq_equiv.
  intros. destruct a. unfold Cauchy in *.
  intros eps. exists 0%nat. intros. rewrite Qplus_opp_r. apply H0.
Qed.

Theorem Cauchy_Seq_def_symm: symmetric Cauchy_Seq_equiv.
Proof. unfold symmetric. unfold Cauchy_Seq_equiv.
  intros. destruct a as [Seqa Ha]. destruct b as [Seqb Hb].
  intros. apply H in H0. destruct H0. exists x. intros.
  replace (Seqb m + - Seqa m) with (Seqb m - Seqa m) by reflexivity.
  rewrite (Qabs_Qminus (Seqb m) (Seqa m)). apply H0. apply H1.
Qed.
Theorem Cauchy_Seq_def_trans: transitive Cauchy_Seq_equiv.
Proof. unfold transitive. unfold Cauchy_Seq_equiv.
  intros a b c Hab Hbc. destruct a as [Seqa Ha].
  destruct b as [Seqb Hb]. destruct c as [Seqc Hc]. intros.
  assert (H': 0 < eps) by (apply H). apply Hab in H. apply Hbc in H'.
  destruct H as [n1 H1]. destruct H' as [n2 H2].

assert (H: forall m, Qabs (Seqa m - Seqc m) <= (Qabs (Seqa m - Seqb m)) + Qabs (Seqb m - Seqc m)).
{ intros.
  assert (Heq: Seqa m - Seqc m == (Seqa m - Seqb m) + (Seqb m - Seqc m)). 
  {
  rewrite <- (Qplus_assoc (Seqa m) (- Seqb m) (Seqb m + - Seqc m)).
  rewrite (Qplus_assoc (- Seqb m) (Seqb m) (- Seqc m)).
  rewrite (Qplus_comm (- Seqb m)). rewrite (Qplus_opp_r). rewrite Qplus_0_l. reflexivity. 
  }
  rewrite Heq.
  apply (Qabs_triangle (Seqa m - Seqb m) (Seqb m - Seqc m)).




  unfold Qminus.


  assert (H0: lt n1 n2 \/ ~ (lt n1 n2)). { apply classic. } destruct H0.
  * exists n2. intros. 





Theorem Cauchy_Seq_equiv_holds: equivalence Cauchy_Seq_equiv.
Proof. unfold equivalence. unfold Cauchy_Seq_equiv. split.
- unfold reflexive. intros. destruct a. unfold Cauchy in *.
  intros eps. exists 0%nat. intros. rewrite Qplus_opp_r. apply H0.
- split. + unfold symmetric.
  intros. destruct a as [Seqa Ha]. destruct b as [Seqb Hb].
  intros. apply H in H0. destruct H0. exists x. intros.
  replace (Seqb m + - Seqa m) with (Seqb m - Seqa m) by reflexivity.
  rewrite (Qabs_Qminus (Seqb m) (Seqa m)). apply H0. apply H1.
+ unfold transitive. intros a b c Hab Hbc. destruct a as [Seqa Ha].
  destruct b as [Seqb Hb]. destruct c as [Seqc Hc]. intros.
  assert (H': 0 < eps) by (apply H). apply Hab in H. apply Hbc in H'.
  destruct H as [n1 H1]. destruct H' as [n2 H2].
  assert (H0: lt n1 n2 \/ ~ (lt n1 n2)). { apply classic. } destruct H0.
  * exists n2. intros.
    









