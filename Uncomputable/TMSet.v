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
  Parameter TM : nat -> nat -> bool.
   (** change nat into bool *)
  (** The i-th Turing machine can stop in m steps or not . **)
  Definition Halting : Type := forall i : nat , {exists j, TM i j = true} + {forall j , TM i j = false}.
  Definition Halting_easy : Type := exists f : Halting , True.
  Definition Halting_easy' : Type := forall i : nat , exists f : ({exists j, TM i j = true} + {forall j , TM i j = false}), True.
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

  Axiom Turing_mono : forall (i j k: nat), (j <= k)%nat -> TM i j = true -> TM i k = true.
  Theorem Turing_mono' : forall (i j k: nat), (k <= j)%nat -> TM i j = false -> TM i k = false.
  Proof.
    unfold not in *.
    intros.
    destruct (TM i k) eqn : H1 ; auto.
    apply (Turing_mono i k j) in H1 ; auto.
    rewrite H0 in H1.
    discriminate H1.
  Qed.

End TM_0_0.

Module TM_1_2.
  Parameter TM12 : Type.
  Parameter eval_1_2 : TM12 -> nat -> nat -> option(nat * nat).
  Axiom Chruch_TM12_thesis : forall (f : nat -> (nat * nat)) , exists (i : TM12), forall (x : nat) , exists (j : nat),
                  eval_1_2 i x j = Some (f x).
  Axiom TM12_mono : forall (i : TM12) (x j1 j2: nat)(z : nat * nat), (j1 >= j2)%nat -> eval_1_2 i x j2 = Some z -> eval_1_2 i x j1 = Some z.
  Theorem TM12_mono' : forall (i : TM12) (x j1 j2 : nat) , (j1 <= j2)%nat -> eval_1_2 i x j2 = None -> eval_1_2 i x j1 = None.
  Proof.
    intros.
    destruct (eval_1_2 i x j1) eqn:H1 ; auto.
    pose proof TM12_mono i x j2 j1 p H H1.
    rewrite H0 in H2.
    discriminate H2.
  Qed.
  
  Definition Halting : Type := 
          forall (i : TM12)(x : nat), 
            {exists (j : nat) (z : nat * nat),eval_1_2 i x j = Some z}
          + {forall (j : nat) , eval_1_2 i x j = None}.
  Definition Halting_easy : Type := exists f : Halting , True.
  Definition Halting_easy' : Type := forall (i:TM12)(x:nat) ,exists f : 
        ({exists (j:nat)(z : nat * nat), eval_1_2 i x j = Some z} + 
        {forall (j:nat) , eval_1_2 i x j = None}), True.
  (** forall n,exists b : {P n} +{~ P n} , True *)

  Theorem Halting_arrow : Halting -> Halting_easy.
  Proof.
    unfold Halting_easy.
    unfold Halting.
    intros.
    exists X ; auto.
  Qed.

  Theorem Halting_arrow' : Halting_easy -> Halting_easy'.
  Proof.
    unfold Halting_easy.
    unfold Halting_easy'.
    unfold Halting.
    intros.
    destruct H.
    exists (x0 i x) ; auto.
  Qed.
  
End TM_1_2.