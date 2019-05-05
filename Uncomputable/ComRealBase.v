(** Uncomputable in the definition of Real function **)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Reals.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope R_scope.
Module Type Vir_Real.
  Parameter Real : Type.
  Parameter Rplus : Real -> Real -> Real.
  Parameter Rminus : Real -> Real -> Real.
  Parameter Rmult : Real -> Real -> Real.
  Parameter Ropp : Real -> Real.
  Parameter Rle : Real -> Real -> Prop.
  Parameter Rlt : Real -> Real -> Prop.
  Parameter Rge : Real -> Real -> Prop.
  Parameter Rgt : Real -> Real -> Prop.
  Parameter R0 : Real.
  Infix "+" := Rplus : Real_scope.
  Infix "*" := Rmult : Real_scope.
  Notation "- x" := (Ropp x) :Real_scope.
  Infix "-" := Rminus : Real_scope.
  Infix "<=" := Rle : Real_scope.
  Infix ">=" := Rge : Real_scope.
  Infix ">" := Rgt : R_scope.
  Parameter Rinv : {a0 : Real | ~(a0 = R0)} -> Real.
  Parameter Rpow : {a0 : Real | ~(a0 = R0)} -> nat ->Real. 
  Parameter Rlim : (nat -> Real) -> Real -> Prop.
  Definition Reqb (x y : Real) : Prop := Rle x y /\ Rle y x.
  Parameter Reqb_refl : forall (x : Real) , Reqb x x.
  Theorem Proper_Reqb : forall (x : Real),Proper Reqb x.
  Proof.
    intros.
    unfold Proper.
    apply Reqb_refl.
  Qed.
End Vir_Real.

(** The definition of Turing machine *)
Parameter TM : nat -> nat -> Prop.
Definition Halting : Type := forall (i j : nat), {TM i j} + {~(TM i j)}.
Axiom Turing_proper1 : forall (i j k: nat), (j <= k)%nat -> TM i j -> TM i k.
Theorem Turing_proper2 : forall (i j k: nat), (k <= j)%nat -> ~ (TM i j) -> ~ (TM i k).
Proof.
  unfold not in *.
  intros.
  apply H0.
  apply Turing_proper1 with k ; auto.
Qed.

(** The definition of Real Number matched with Turing machine *)
Parameter Bin_R : R -> nat -> nat.
Parameter TMR : nat -> R -> Prop.
Axiom Bin_R_pro1 : forall (r : R) (n : nat) , Bin_R r n = 1%nat /\  Bin_R r n = 0%nat.
Axiom Bin_R_pro2 : forall (r : R) (n : nat) , Bin_R r n = 1%nat <-> (Bin_R r n <> 0%nat).
Theorem Bin_R_pro2' : forall (r : R) (n : nat) , (Bin_R r n <> 1%nat) <-> (Bin_R r n = 0 %nat).
Proof.
  intros.
  split.
  - intros. apply NNPP. unfold not in *.
    intros. apply H. apply Bin_R_pro2. unfold not in *. apply H0.
  - unfold not in *. intros. rewrite Bin_R_pro2 in H0.
    apply H0. apply H.
Qed.

Axiom Bin_R_pro3  : forall (r1 r2 : R) , r1 = r2 <-> (forall (j : nat) , Bin_R r1 j = Bin_R r2 j).
Axiom Bin_R_pro3' : forall (r1 r2 : R) , r1 < r2 <-> 
                    exists (j : nat), (Bin_R r1 j < Bin_R r2 j)%nat /\ 
                                      (forall (k : nat) , (k <= j)%nat -> (Bin_R r1 k = Bin_R r2 k)%nat).

Theorem Bin_R_pro3'' : forall (r1 r2 : R) , r1 > r2 <-> 
                    exists (j : nat), (Bin_R r1 j > Bin_R r2 j)%nat /\ 
                                      (forall (k : nat) , (k <= j)%nat -> (Bin_R r1 k = Bin_R r2 k)%nat).
Proof.
  intros.
  pose proof (Bin_R_pro3' r2 r1).
  split.
  - intros.
    apply H in H0.
    inversion H0.
    exists x.
    split.
    + apply H1.
    + intros. destruct H1.
      symmetry.
      apply (H3 k H2).
  - intros.
    apply H.
    inversion H0.
    exists x.
    split.
    + apply H1.
    + intros. destruct H1.
      symmetry.
      apply (H3 k H2).
Qed.

Theorem Bin_R_pro3_ge : forall (r1 r2 : R) , r1 >= r2 -> 
                    exists (j : nat), (Bin_R r1 j >= Bin_R r2 j)%nat /\ 
                                      (forall (k : nat) , (k <= j)%nat -> (Bin_R r1 k = Bin_R r2 k)%nat).
Proof.
  intros.
  intros.
  inversion H.
  - pose proof (Bin_R_pro3'' r1 r2).
    rewrite H1 in H0.
    inversion H0.
    exists x.
    clear H1. clear H0.
    destruct H2.
    split.
    + apply Nat.lt_le_incl. apply H0.
    + intros. apply (H1 k H2).
  - pose proof (Bin_R_pro3 r1 r2).
    rewrite H1 in H0.
    exists 10%nat.
    split. 
    + apply Nat.eq_le_incl. symmetry. apply (H0 10%nat).
    + intros. apply (H0 k).
Qed.

Axiom R_is_TMR : forall (n:nat) (r:R) , TMR n r <-> (forall (j : nat), TM n j -> Bin_R r j = 1%nat) /\ (forall (j:nat) , ~TM n j -> Bin_R r j = 0%nat).
Theorem TMR_proper0 : forall (n:nat) (r:R) , TMR n r -> forall (j : nat), (Bin_R r j = 1%nat -> TM n j) /\ (Bin_R r j = 0%nat -> ~TM n j).
Proof.
  intros.
  rewrite R_is_TMR in H.
  destruct H.
  split.
  - intros.
    rewrite Bin_R_pro2 in H1.
    pose proof (H0 j).
    apply imply_to_or in H2.
    destruct H2.
    + apply NNPP in H2. auto.
    + exfalso. auto.
  - unfold not. intros.
    apply H in H2.
    rewrite Bin_R_pro2 in H2.
    auto.
Qed.

Theorem TMR_proper1 : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r j = 1%nat) -> (Bin_R r k = 1%nat)).
Proof.
  intros.
  pose proof H.
  rewrite R_is_TMR in H.
  destruct H.
  apply H.
  apply Turing_proper1 with j ; auto.
  assert (H4 : forall j : nat,  (Bin_R r j = 1%nat -> TM n j) /\ (Bin_R r j = 0%nat -> ~ TM n j)).
  { apply TMR_proper0. apply H2. }
  pose proof H4 j.
  clear H4.
  apply H5. 
  auto.
Qed.

Theorem TMR_proper1' : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r k = 0%nat) -> (Bin_R r j = 0%nat)).
Proof.
  intros.
  pose proof H.
  rewrite R_is_TMR in H.
  destruct H.
  apply H3.
  unfold not. intros.
  apply H in H4.
  apply (TMR_proper1 n r H2 j k H0) in H4.
  rewrite H1 in H4.
  discriminate H4.
Qed.

Axiom TM_ex_TMR : forall n : nat , exists (r : R) , TMR n r.
Axiom R_only_TMR : forall (n1 n2 : nat) (r : R) , TMR n1 r -> (n1 = n2 <-> TMR n2 r).
Axiom only_R_TMR : forall (n : nat) (r1 r2 : R) , TMR n r1 -> (r1 = r2 <-> TMR n r2).
Theorem diffR_diffTMR : forall (n1 n2 : nat) (r1 r2 : R) , TMR n1 r1 -> TMR n2 r2 -> (r1 <> r2 <-> n1 <> n2).
Proof.
  intros.
  pose proof R_only_TMR.
  pose proof only_R_TMR.
  unfold not.
  split.
  - intros.
    apply H3. apply (H1 n1 n2) in H.
    rewrite H in H4.
    apply (H2 n2 r1 r2) ; auto.
  - intros.
    apply H3. apply (H1 n1 n2) in H0; auto.
    apply (H2 n1 r1 r2) ; auto.
Qed.

Theorem sameR_sameTMR : forall (n1 n2 : nat) (r1 r2 : R) , r1 = r2 -> n1 = n2 -> (TMR n1 r1 <-> TMR n2 r2).
Proof.
  intros.
  split.
  - intros.
    apply (R_only_TMR n1 n2 r2) ; auto.
    apply (only_R_TMR n1 r1 r2) ; auto.
  - intros.
    apply (only_R_TMR n1 r2 r1) ; auto.
    apply (R_only_TMR n2 n1 r2) ; auto.
Qed.

Definition Req (r1 r2 : R) : Prop := r1 = r2.

Record Function_prop (f : R -> R -> Prop) : Prop := {
  propertise1 : forall x x1 y y1 : R ,  f x y -> f x1 y1 -> x = x1 ->y = y1;
  propertise2 : forall x :R , exists y : R , f x y;
  propertise3 : Proper(Req ==> Req ==> iff) f;
}.

Record Single_function_prop(f : R -> Prop) : Prop := {
  Propertise1 : forall x x1: R ,  f x -> f x1 -> x = x1;
  Propertise2 : exists x : R , f x;
  Propertise3 : Proper(Req ==> iff) f;
}.

Theorem TMR_obey_Single_function_prop : forall (n : nat) , Single_function_prop (TMR n).
Proof.
  intros.
  split.
  - apply only_R_TMR.
  - apply TM_ex_TMR.
  - split ; intros. 
    + apply (only_R_TMR n x y) ; auto.
    + apply (only_R_TMR n y x) ; auto.
Qed.

Axiom Lemma1 : forall (f : R -> Prop) , (exists x0 , f x0) -> R.

Definition G_signle_exists : {f : R -> Prop | Single_function_prop f} -> R.
  intros.
  destruct X.
  destruct s.
  apply (Lemma1 x).
  auto.
Defined.

Definition G_function_exists : {f : R -> R -> Prop | Function_prop f} -> (R -> R).
  intros.
  destruct X.
  destruct f.
  apply (Lemma1 (x H)).
  auto.
Defined.

Module Uncomputable_function.
  Parameter Rinv : {a0 : R | ~(a0 = 0)} -> R.
  Parameter Rpow : {a0 : R | ~(a0 = 0)} -> nat ->R. 
  Parameter CR : R -> Prop.
  
  Theorem Two_dimensions : (forall r1 r2 : R, {r1 = r2} + {r1 <> r2}) -> Halting.
  Proof.
    unfold Halting.
    intros.
  Admitted.
  
  Theorem Up_R : (forall (r : R), exists (z : Z) , up r = z) -> Halting.
  Proof.
    intros.
    apply Two_dimensions.
    intros.
    pose proof H r1.
    pose proof H r2.
    
  Admitted.
  (** This theorem also proves the uncomputability of Int_part frac_part *)
  
  Theorem P_OR_NP : (forall P : Prop, {P} + {~ P}) -> Halting.
  Proof. 
    intros.
    apply Two_dimensions.
    intros.
    apply X with (P := r1 = r2).
  Admitted.

  Theorem Three_dimensions : (forall r1 r2 : R, {r1 = r2} + {r1 > r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Two_dimensions.
    intros.
    pose proof (H r1 r2).
    clear H.
    destruct H0 ; auto.
    - destruct s ; auto.
      apply Rgt_not_eq in r ; auto.
    - apply Rlt_not_eq in r ; auto.
  Admitted.
  
  Theorem Two_dimensions2 : (forall r1 r2 : R, {r1 >= r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Three_dimensions.
    intros.
    pose proof (H r1 r2).
    destruct H0 ; auto.
    apply Rge_le in r. apply Rle_lt_or_eq_dec in r.
    left. destruct r ; auto.
  Admitted.
  
  (** This theorem also proves the uncomputability of Rmax Rmin Rabs Rdist*)
  (** Rmax Rmin Rabs Rdist are actually computable. Defined in an incorrect way in std. -- Qinxiang *)

  Theorem Rinv_def : forall (Rinv' : R -> R)(r: R) (H : r <> 0) ,Rinv' r = Rinv (exist _ r H) -> Halting.
  Proof.  intros. Admitted.
  Theorem Rpow_def : forall (Rpow' : R -> nat -> R)(r: R)(H : r <> 0) ,Rpow' r 0%nat = Rpow (exist _ r H) 0%nat -> Halting.
  Proof.  intros. Admitted.
  (** This theorem also proves the problem in the definition of powRZ *)
  Theorem lim_CN_NCN :forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> ~ CR l1.
  Proof. Admitted.
  
End Uncomputable_function.


