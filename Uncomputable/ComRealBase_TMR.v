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
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Classes.Equivalence.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Classes.RelationClasses.
Require Import Ring.
From Coq Require Import Field.
From Coq Require Import Omega.
From CReal Require Import Uncomputable.TMSet.
From CReal Require Import INR_libs.
From CReal Require Import QArith_base_ext.
From CReal Require Import Uncomputable.ComRealBase.
From CReal Require Import Uncomputable.ComRealBase_Dec.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
Import TM_u_u.
Module TMR_Set (R : VIR_R).
  
  Module RLemmas := VirRLemmas (R).
  Module Dec := DEC_R (R).
  Import R RLemmas Dec.
  Local Open Scope R_scope.
  
  Definition limit : (nat -> Q) -> R -> Prop.
    intros.
    set (fun n q => q = H n).
    apply (Un_cv' P X).
  Defined.
  
  Definition Un_cv : (nat -> R) -> R -> Prop.
    intros.
    set (fun n r => r = X n).
    apply (Un_cv P X0).
  Defined.
  
  Definition TMR : nat -> R -> Prop.
    intros n r.
    apply ((forall m : nat , Dec_R r m (Nat.b2n(TM n m))) /\ In_Search r).
  Defined.
  
  Parameter Get_TMR : nat -> R.
  Axiom TMR_get : forall n : nat , TMR n (Get_TMR n).
  
  Parameter TM'r : nat -> R.
  Axiom TM'r_pro : forall (n m: nat), Dec_R (TM'r n) m (Nat.b2n(TM m n)).
  Theorem In_Search_TM'r : forall n : nat , In_Search (TM'r n).
  Proof.
  Admitted.
  Parameter limitTM'r : R.

  Theorem limit_of_TM'r : Un_cv TM'r limitTM'r.
  Proof.
    hnf. split ; hnf ; intros.
    - split ; hnf ; intros.
      + exists (TM'r a); auto.
      + subst ; auto.
    - admit.
  Admitted.
 (** the limitation of a list of Real Number *)
  Axiom limitTM'r_pro : forall (n : nat) , Dec_R limitTM'r n 1 <-> exists j : nat , TM n j = true.
  Theorem TMR_proper0 : forall (n:nat) (r:R) , TMR n r -> forall (j : nat), (Dec_R r j 1 -> TM n j = true) /\ (Dec_R r j 0 -> TM n j = false).
  Proof.
    intros. 
    destruct H.
    destruct (TM n j) eqn : H1; split ; auto ; intros ; pose proof H j ; 
    rewrite H1 in H3 ;  simpl in * ; 
    assert (1 = 0)%nat ;  try (apply (partial_functional_Dec_R r j) ; auto ) ; 
    inversion H4.
  Qed.

  Theorem TMR_proper1 : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Dec_R r j 1) -> (Dec_R r k 1)).
  Proof.
    intros.
    pose proof H.
    destruct H.
    pose proof H k.
    assert (H' : TM n j = true).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n k = true).
    { apply Turing_mono with j ; auto. }
    rewrite H'' in H4. apply H4.
  Qed.

  Theorem TMR_proper1' : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Dec_R r k 0) -> (Dec_R r j 0)).
  Proof.
    intros.
    pose proof H.
    destruct H.
    pose proof H j.
     assert (H' : TM n k = false).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n j = false).
    { apply Turing_mono' with k ; auto. }
    rewrite H'' in H4. apply H4.
  Qed.
  
  Theorem image_Defined_TMR : image_defined TMR.
  Proof.
    hnf ; intros.
    exists (Get_TMR a).
    apply TMR_get.
  Qed.
  Theorem injective_TMR : injective TMR.
  Proof.
    hnf ; intros.
    destruct H,  H0.
    apply TMuu_eqb. intros.
    specialize (H j).
    specialize (H0 j).
    apply Nat.b2n_inj. 
    apply (partial_functional_Dec_R b j) ; auto.
  Qed.
  
  Theorem partial_functional_TMR : partial_functional TMR.
  Proof.
    hnf ; intros.
    destruct H , H0.
    apply Dec_R_eq ; auto.
    intros. specialize (H j). specialize (H0 j).
    split ; intros.
    + assert (m = Nat.b2n (TM a j)). { apply (partial_functional_Dec_R b1 j) ; auto. }
      subst. auto.
    + assert (m = Nat.b2n (TM a j)). { apply (partial_functional_Dec_R b2 j) ; auto. }
      subst. auto.
  Qed.
  
  Theorem diffR_diffTMR : forall (n1 n2 : nat) (r1 r2 : R) , TMR n1 r1 -> TMR n2 r2 -> (r1 <> r2 <-> n1 <> n2).
  Proof.
    intros.
    pose proof injective_TMR.
    pose proof partial_functional_TMR.
    hnf in *.
    unfold not.
    split.
    - intros.
      subst. apply H3.
      apply (H2 n2 r1 r2) ; auto.
    - intros.
      subst. apply H3. apply (H1 n1 n2) in H0; auto.
  Qed.
  
  Theorem TM'r_pro0 : forall (n m : nat), Dec_R (TM'r n) m 1 <-> TM m n = true.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R (TM'r n) m) ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r_pro0' : forall (n m : nat), Dec_R (TM'r n) m 0 <-> TM m n = false.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R (TM'r n) m) ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r_pro1 : forall (n m : nat) , Dec_R (TM'r n) m 1 -> (forall (r : nat) , (r >= n)%nat -> Dec_R (TM'r r) m 1).
  Proof.
    intros.
    apply TM'r_pro0 in H.
    apply TM'r_pro0.
    pose proof Turing_mono m n r.
    apply H1 ; auto.
  Qed.
  
  Theorem TM'r_pro1' : forall (n m : nat) , Dec_R (TM'r n) m 0 -> (forall (r : nat) , (r <= n)%nat -> Dec_R (TM'r r) m 0).
  Proof.
    intros.
    apply TM'r_pro0' in H.
    apply TM'r_pro0'.
    pose proof Turing_mono' m n r.
    apply H1 ; auto.
  Qed.

  Theorem limitTM'r_pro' : forall (n : nat) , Dec_R limitTM'r n 0 <-> forall j : nat , TM n j = false. 
  Proof.
    intros.
    pose proof limitTM'r_pro n.
    unfold not in *.
    split ; intros.
    - destruct (TM n j) eqn:En ; auto.
      assert (exists j : nat , TM n j = true). { exists j. auto. }
      apply H in H1.
      apply Nat.b2n_inj. simpl.
      apply (partial_functional_Dec_R limitTM'r n) ; auto.
    - admit.
  Admitted.
  
  Theorem limitTM'r_pro0 : forall (n : nat) , Dec_R limitTM'r n 1 \/ Dec_R limitTM'r n 0.
  Proof.
    intros.
    destruct (classic (exists j : nat , TM n j = true)).
    - left. apply limitTM'r_pro. auto.
    - right. apply limitTM'r_pro'.
      pose proof (not_ex_all_not _ _ H). simpl in *.
      intros.
      specialize (H0 j).
      destruct (TM n j) ; auto.
      exfalso. auto.
  Qed.
  
  Theorem limitTM'r_pro1 : (forall (n : nat) , {Dec_R limitTM'r n 0} + {Dec_R limitTM'r n 1}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof H i.
    destruct H0.
    - rewrite (limitTM'r_pro' i) in d. auto.
    - rewrite (limitTM'r_pro i) in d. auto.
  Qed.
  
  Axiom limit_TM'r'_pro_pre : forall (f : nat -> Q) (n n0 m : nat), limit f limitTM'r -> 
      (Qabs (f n0 - f m) < 1 # Pos.of_nat (10 ^ n))%Q -> (Dec_R (IQR(f n0)) n 0 <-> Dec_R limitTM'r n 0).

End TMR_Set.