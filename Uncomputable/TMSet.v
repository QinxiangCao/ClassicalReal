Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Export Field.
From Coq Require Export Omega.
Import ListNotations.


Module TM_0_0.
  Parameter TM : nat -> nat -> nat.
  (** The i-th Turing machine can stop in m steps or not . **)
Definition Halting : Type := forall i : nat , {exists j, TM i j = 1%nat} + {forall j , TM i j = 0%nat}.
Definition Halting_easy : Type := exists f : Halting , True.
Definition Halting_easy' : Type := forall i : nat , exists f : ({exists j, TM i j = 1%nat} + {forall j , TM i j = 0%nat}), True.
(** forall n,exists b : {P n} +{~ P n} , True *)

Theorem Halting_arrow : Halting -> Halting_easy.
Proof.
  unfold Halting_easy.
  unfold Halting.
  intros.
  exists H ; auto.
Qed.

Theorem Halting_arrow' : Halting_easy -> Halting_easy'.
Proof.
  unfold Halting_easy.
  unfold Halting_easy'.
  unfold Halting.
  intros.
  destruct H.
  exists (x i) ; auto.
Qed.

Axiom Turing_proper0 : forall (i j : nat) , TM i j = 0%nat \/ TM i j = 1%nat.
Axiom Turing_proper1 : forall (i j k: nat), (j <= k)%nat -> TM i j = 1%nat -> TM i k = 1%nat.
Theorem Turing_proper2 : forall (i j k: nat), (k <= j)%nat -> TM i j = 0%nat -> TM i k = 0%nat.
Proof.
  unfold not in *.
  intros.
  destruct (Turing_proper0 i k) ; auto.
  apply (Turing_proper1 i k j) in H1 ; auto.
  rewrite H0 in H1.
  discriminate H1.
Qed.

End TM_0_0.