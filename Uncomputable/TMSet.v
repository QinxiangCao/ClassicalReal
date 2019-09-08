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


Module TM_N_Q.
  Parameter TMNQ : Type.
  Parameter eval_N_Q : TMNQ -> nat -> nat -> option(Q).
  
  Definition Combine (f : nat -> Q) (i : TMNQ) : Prop := forall (x : nat) , exists (j : nat) , eval_N_Q i x j = Some (f x).
  Axiom Chruch_TMNQ_thesis : forall (f : nat -> Q) , exists (i : TMNQ), Combine f i.
  Axiom TMNQ_mono : forall (i : TMNQ) (x j1 j2: nat)(z : Q), (j1 >= j2)%nat -> eval_N_Q i x j2 = Some z -> eval_N_Q i x j1 = Some z.
  Theorem TMNQ_mono' : forall (i : TMNQ) (x j1 j2 : nat) , (j1 <= j2)%nat -> eval_N_Q i x j2 = None -> eval_N_Q i x j1 = None.
  Proof.
    intros.
    destruct (eval_N_Q i x j1) eqn:H1 ; auto.
    pose proof TMNQ_mono i x j2 j1 q H H1.
    rewrite H0 in H2.
    discriminate H2.
  Qed.
  
  
  Definition TMNQ_eq (i1 i2 : TMNQ) := (forall x : nat , (forall (j : nat) , eval_N_Q i1 x j = None /\ eval_N_Q i1 x j = eval_N_Q i2 x j) 
  \/(exists j : nat , eval_N_Q i1 x j <> None /\ eval_N_Q i1 x j = eval_N_Q i2 x j)).

  Theorem TMNQeq_refl x : TMNQ_eq x x.
  Proof.
    hnf. intros.
    destruct (classic (forall j : nat , eval_N_Q x x0 j = None)).
    - left. intros. auto.
    - right. apply not_all_ex_not in H.
      destruct H. exists x1. auto.
  Qed.
  
  Theorem TMNQeq_sym x y : TMNQ_eq x y -> TMNQ_eq y x.
  Proof.
    intros.
    hnf in *. intros.
    specialize (H x0).
    destruct H.
    - left. intros. specialize (H j).
      destruct H. rewrite H0 in *. auto.
    - destruct H. right. exists x1.
      destruct H. rewrite H0 in *. auto.
  Qed.
  
  Theorem TMNQeq_trans x y z : TMNQ_eq x y -> TMNQ_eq y z -> TMNQ_eq x z.
  Proof.
    intros.
    hnf in *. intros.
    specialize (H x0). specialize (H0 x0).
    destruct H , H0.
    - left. intros. specialize (H j). specialize (H0 j).
      destruct H, H0. rewrite H1 in *. auto.
    - exfalso. destruct H0. destruct H0.
      specialize (H x1). destruct H.
      rewrite H in *. auto.
    - exfalso. destruct H , H.
      specialize (H0 x1). destruct H0. 
      rewrite H0 in *. auto. 
    - destruct H. destruct H0.
      destruct H , H0.
      right. exists (max x1 x2).
      split.
      + destruct (eval_N_Q x x0 x1) eqn : En ; auto.
        assert (eval_N_Q x x0 (max x1 x2) = Some q).
        { apply (TMNQ_mono _ _ _ x1) ; auto.
          apply Nat.le_max_l.
        }
        rewrite H3. auto.
      + destruct (classic (x1 >= x2)%nat).
        * destruct (eval_N_Q y x0 x2) eqn : En .
          ** assert ( eval_N_Q y x0 x1 = Some q).
             { apply (TMNQ_mono _ _ _ x2) ; auto. }
             rewrite H4 in *.
             assert (eval_N_Q x x0 (max x1 x2) = Some q).
             { apply (TMNQ_mono _ _ _ x1) ; auto.
               apply Nat.le_max_l.
             }
             rewrite H5. symmetry.
             apply (TMNQ_mono _ _ _ x2) ; auto.
             apply Nat.le_max_r.
          ** exfalso . auto.
        * apply not_ge in H3.
          destruct (eval_N_Q x x0 x1) eqn :En.
          ** assert ( eval_N_Q y x0 x2 = Some q).
             { apply (TMNQ_mono _ _ _ x1) ; auto. omega. }
             rewrite H4 in *.
             assert (eval_N_Q x x0 (max x1 x2) = Some q).
             { apply (TMNQ_mono _ _ _ x1) ; auto.
               apply Nat.le_max_l.
             }
             rewrite H5. symmetry.
             apply (TMNQ_mono _ _ _ x2) ; auto.
             apply Nat.le_max_r.
          ** exfalso. auto. 
  Qed.
  
  Instance TMNQ_Setoid : Equivalence TMNQ_eq.
  Proof.
    split ; hnf.
    - apply TMNQeq_refl.
    - apply TMNQeq_sym.
    - apply TMNQeq_trans.
  Qed.
  
  Parameter Countable_TMNQ : Countable TMNQ TMNQ_eq.
  
  Instance Combine_comp : Proper (eq ==> TMNQ_eq ==> iff) Combine.
  Proof.
    hnf ; red ; intros ; subst.
    split ; intros.
    - hnf. intros. destruct (H x). 
      specialize (H0 x). destruct H0.
      + specialize (H0 x1). destruct H0. rewrite H0 in *. inversion H1.
      + destruct H0. destruct H0. exists x2. 
        destruct (classic (x1 <= x2)%nat).
        * assert ( eval_N_Q x0 x x2 = Some (y x)).
          { apply (TMNQ_mono _ _ _ x1) ; auto. }
          rewrite H2 in *. auto.
        * apply not_ge in H3.
          destruct (eval_N_Q x0 x x2) eqn :En.
          ** assert ( eval_N_Q x0 x x1 = Some q).
             { apply (TMNQ_mono _ _ _ x2) ; auto. omega. }
             rewrite H4 in *.
             rewrite <- H2. auto.
          ** exfalso. auto. 
   - hnf. intros. destruct (H x). 
      specialize (H0 x). destruct H0.
      + specialize (H0 x1). destruct H0. rewrite H0 in *. rewrite H1 in *. inversion H2.
      + destruct H0. destruct H0. exists x2. 
        destruct (classic (x1 <= x2)%nat).
        * assert ( eval_N_Q y0 x x2 = Some (y x)).
          { apply (TMNQ_mono _ _ _ x1) ; auto. }
          rewrite H4 in *. auto.
        * apply not_ge in H3.
          destruct (eval_N_Q x0 x x2) eqn :En.
          ** assert ( eval_N_Q y0 x x1 = Some q).
             { apply (TMNQ_mono _ _ _ x2) ; auto. omega. }
             rewrite H4 in *. auto.
          ** exfalso. auto. 
  Qed.
  
  Theorem image_defined_Combine : image_defined Combine.
  Proof.
    unfold image_defined.
    apply Chruch_TMNQ_thesis.
  Qed.
  
  Theorem partial_functional_Combine: partial_functional TMNQ_eq Combine .
  Proof.
    unfold partial_functional , Combine .
    intros.
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
  
  Theorem injective_Combine : injective eq Combine.
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