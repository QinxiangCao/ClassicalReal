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
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Field.
From Coq Require Import Omega.
From CReal Require Export Uncomputable.Countable.
Import ListNotations.

Module TM_u_u.
  Parameter TM : nat -> nat -> bool.
  Axiom TMuu_eqb : forall (i1 i2 : nat) , (forall j : nat , TM i1 j = TM i2 j) <-> i1 = i2.
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
End TM_u_u.

Module TM_1_1.
  Parameter TM11 : Type.
  Parameter eval_1_1 : TM11 -> nat -> nat -> option(nat).
  Parameter Countable_TM11 : Countable TM11.
  Definition Combine (f : nat -> nat) (i : TM11) : Prop := forall (x : nat) , exists (j : nat) , eval_1_1 i x j = Some (f x).
  Axiom Chruch_TM11_thesis : forall (f : nat -> nat) , exists (i : TM11), Combine f i.
  Definition TM11_eqb (i1 i2 : TM11) : Prop :=
    (forall (x j : nat) , eval_1_1 i1 x j = None /\ eval_1_1 i1 x j = eval_1_1 i2 x j) 
  \/(forall (x : nat) , exists j : nat , eval_1_1 i1 x j <> None /\ eval_1_1 i1 x j = eval_1_1 i2 x j).
  Axiom TM11_mono : forall (i : TM11) (x j1 j2 z: nat), (j1 >= j2)%nat -> eval_1_1 i x j2 = Some z -> eval_1_1 i x j1 = Some z.
  Theorem TM11_mono' : forall (i : TM11) (x j1 j2 z: nat) , (j1 <= j2)%nat -> eval_1_1 i x j2 = None -> eval_1_1 i x j1 = None.
  Proof.
    intros.
    destruct (eval_1_1 i x j1) eqn:H1 ; auto.
    pose proof TM11_mono i x j2 j1 _ H H1.
    rewrite H0 in H2.
    discriminate H2.
  Qed.
  Theorem Combine_unique : forall (f : nat -> nat) (i1 i2 : TM11) , Combine f i1 -> Combine f i2 -> TM11_eqb i1 i2.
  Proof.
    intros.
    unfold Combine , TM11_eqb in *.
    right.
    intros.
    pose proof H x.
    pose proof H0 x.
    clear H H0.
    destruct H1 ,H2.
    exists (max x0 x1).
    destruct (Nat.max_dec x0 x1).
    - rewrite e. split ; rewrite H.
      + unfold not. intros. inversion H1.
      + symmetry. apply (TM11_mono i2 x x0 x1 (f x)) ; auto.
        rewrite <- e. apply Nat.le_max_r.
    - rewrite e.
      assert (eval_1_1 i1 x x1 = Some (f x)).
        { apply (TM11_mono i1 x x1 x0 (f x)) ; auto. 
          rewrite <- e. apply Nat.le_max_l. } 
      split ; rewrite H1.
      + unfold not. intros. inversion H2.
      + auto. 
  Qed.
  
  Definition Halting : Type := 
          forall (i : TM11)(x : nat), 
            {exists (j z: nat) ,eval_1_1 i x j = Some z}
          + {forall (j : nat) , eval_1_1 i x j = None}.
  Definition Halting_easy : Type := exists f : Halting , True.
  Definition Halting_easy' : Type := forall (i:TM11)(x:nat) ,exists f : 
        ({exists (j z:nat), eval_1_1 i x j = Some z} + 
        {forall (j:nat) , eval_1_1 i x j = None}), True.
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
  
End TM_1_1.

Module TM_N_Q.
  Parameter TMNQ : Type.
  Parameter eval_N_Q : TMNQ -> nat -> nat -> option(Q).
  Parameter Countable_TMNQ : Countable TMNQ.
  Definition Combine (f : nat -> Q) (i : TMNQ) : Prop := forall (x : nat) , exists (j : nat) , eval_N_Q i x j = Some (f x).
  Axiom Chruch_TMNQ_thesis : forall (f : nat -> Q) , exists (i : TMNQ), Combine f i.
  Axiom TMNQ_eqb : forall (i1 i2 : TMNQ) , i1 = i2 <-> (
    (forall (x j : nat) , eval_N_Q i1 x j = None /\ eval_N_Q i1 x j = eval_N_Q i2 x j) 
  \/(forall (x : nat) , exists j : nat , eval_N_Q i1 x j <> None /\ eval_N_Q i1 x j = eval_N_Q i2 x j)).
  Axiom TMNQ_mono : forall (i : TMNQ) (x j1 j2: nat)(z : Q), (j1 >= j2)%nat -> eval_N_Q i x j2 = Some z -> eval_N_Q i x j1 = Some z.
  Theorem TMNQ_mono' : forall (i : TMNQ) (x j1 j2 : nat) , (j1 <= j2)%nat -> eval_N_Q i x j2 = None -> eval_N_Q i x j1 = None.
  Proof.
    intros.
    destruct (eval_N_Q i x j1) eqn:H1 ; auto.
    pose proof TMNQ_mono i x j2 j1 q H H1.
    rewrite H0 in H2.
    discriminate H2.
  Qed.
  
  Theorem image_defined_Combine : image_defined Combine.
  Proof.
    unfold image_defined.
    apply Chruch_TMNQ_thesis.
  Qed.
  
  Theorem partial_functional_Combine: partial_functional Combine.
  Proof.
    unfold partial_functional , Combine .
    intros.
    apply TMNQ_eqb.
    right.
    intros.
    pose proof H x.
    pose proof H0 x.
    clear H H0.
    destruct H1 ,H2.
    exists (max x0 x1).
    destruct (Nat.max_dec x0 x1).
    - rewrite e. split ; rewrite H.
      + unfold not. intros. inversion H1.
      + symmetry. apply (TMNQ_mono b2 x x0 x1 (a x)) ; auto.
        rewrite <- e. apply Nat.le_max_r.
    - rewrite e.
      assert (eval_N_Q b1 x x1 = Some (a x)).
        { apply (TMNQ_mono b1 x x1 x0 (a x)) ; auto. 
          rewrite <- e. apply Nat.le_max_l. } 
      split ; rewrite H1.
      + unfold not. intros. inversion H2.
      + auto. 
  Qed.
  
  Theorem injective_Combine : injective Combine.
  Proof.
    unfold injective , Combine .
    intros.
    apply functional_extensionality.
    intros.
    pose proof H x.
    pose proof H0 x.
    clear H H0.
    destruct H1 , H2.
    pose proof TMNQ_mono b x.
    destruct (Nat.lt_ge_cases x0 x1).
    - apply lt_le_weak in H2.
      pose proof (H1 _ _ (a1 x) H2 H).
      rewrite H0 in H3.
      inversion H3 ; auto.
    - pose proof (H1 _ _ (a2 x) H2 H0).
      rewrite H in H3.
      inversion H3 ; auto.
  Qed.
  
  Definition Halting : Type := 
          forall (i : TMNQ)(x : nat), 
            {exists (j : nat) (z : Q),eval_N_Q i x j = Some z}
          + {forall (j : nat) , eval_N_Q i x j = None}.
  Definition Halting_easy : Type := exists f : Halting , True.
  Definition Halting_easy' : Type := forall (i:TMNQ)(x:nat) ,exists f : 
        ({exists (j:nat)(z : Q), eval_N_Q i x j = Some z} + 
        {forall (j:nat) , eval_N_Q i x j = None}), True.
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
  
End TM_N_Q.