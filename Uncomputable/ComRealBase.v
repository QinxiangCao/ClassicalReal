(** Uncomputable in the definition of R function **)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Import QArith.
Import ListNotations.

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

Module Type Vir_R.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv : {a0 : R | ~(a0 = R0)} -> R.
  Parameter Rlt : R -> R -> Prop.
  Parameter up : R -> Z.
  Parameter IZR : Z -> R.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  Infix "-" := Rminus : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Parameter Rpow : {a0 : R | ~(a0 = R0)} -> nat ->R. 
  Parameter Rlim : (nat -> R) -> R -> Prop.
  Definition Reqb (x y : R) : Prop := x = y.
  Parameter Reqb_refl : forall (x : R) , Reqb x x.
  Theorem Proper_Reqb : forall (x : R),Proper Reqb x.
  Proof.
    intros.
    unfold Proper.
    apply Reqb_refl.
  Qed.  

  
  Record Function_prop (f : R -> R -> Prop) : Prop := {
    propertise1 : forall x x1 y y1 : R ,  f x y -> f x1 y1 -> x = x1 ->y = y1;
    propertise2 : forall x :R , exists y : R , f x y;
    propertise3 : Proper(Reqb ==> Reqb ==> iff) f;
  }.

  Record Single_function_prop(f : R -> Prop) : Prop := {
    Propertise1 : forall x x1: R ,  f x -> f x1 -> x = x1;
    Propertise2 : exists x : R , f x;
    Propertise3 : Proper(Reqb ==> iff) f;
  }.

  Definition G_signle_exists : {f : R -> Prop | Single_function_prop f} -> R.
    Admitted.

  Definition G_function_exists : {f : R -> R -> Prop | Function_prop f} -> (R -> R).
    (*
    intros.
    destruct X.
    destruct f.
    assert (H' : Single_function_prop (x X0)).
    { split ; auto. 
      - intros. apply (propertise4 X0 X0 x0 x1) ; auto.
      - split.
        + assert (H'' : Reqb X0 X0).
          { reflexivity. }
          destruct (propertise6 X0 X0 H'' x0 y) ; auto.
        + assert (H'' : Reqb X0 X0).
          { reflexivity. }
          destruct (propertise6 X0 X0 H'' x0 y) ; auto.
    }
    pose proof (G_single_exists x X0 H').
    auto.
  Defined.
    *)
    Admitted.

  (** The definition of R Number matched with Turing machine *)
  Parameter Bin_R : R -> nat -> nat.
  Parameter TMR : nat -> R -> Prop.
  Axiom Bin_R_pro1 : forall (r : R) (n : nat) , Bin_R r n = 1%nat /\  Bin_R r n = 0%nat.
  Axiom Bin_R_pro2 : forall (r : R) (n : nat) , Bin_R r n = 1%nat <-> (Bin_R r n <> 0%nat).
  Axiom Zero_Bin : forall (n : nat) , (Bin_R R0 n = 0)%nat.  
  Axiom One_Bin : forall (n : nat) , (Bin_R R1 n = 1) % nat.
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

  Theorem Bin_R_pro3_not : forall (r1 r2 : R) , r1 <> r2 <-> exists (j : nat), Bin_R r1 j <> Bin_R r2 j.
  Proof.
    intros.
    split.
    - intros.
      pose proof Bin_R_pro3 r1 r2.
      rewrite H0 in H.
      clear H0.
      apply not_all_ex_not.
      apply H.
    - intros.
      destruct H.
      unfold not in *.
      intros. apply H.
      apply (Bin_R_pro3 r1 r2) ; auto.
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

  Parameter Get_TMR : nat -> R.
  Axiom Zero_TMR : Get_TMR 0 = R0.
  Axiom One_TMR : Get_TMR 1 = R1.
  Axiom R_ex_TMR : forall n : nat , TMR n (Get_TMR n).
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

  Theorem TMR_obey_Single_function_prop : forall (n : nat) , Single_function_prop (TMR n).
  Proof.
    intros.
    split.
    - apply only_R_TMR.
    - exists (Get_TMR n). apply R_ex_TMR.
    - split ; intros. 
      + apply (only_R_TMR n x y) ; auto.
      + apply (only_R_TMR n y x) ; auto.
  Qed.


  Parameter CR : R -> Prop.
    
  Theorem P_OR_NP : (forall P : Prop, {P} + {~ P}) -> Halting.
  Proof. 
    unfold Halting.
    intros.
    apply X with (P := TM i j).
  Qed.

  Theorem Two_dimensions : (forall r1 r2 : R, {r1 = r2} + {r1 <> r2}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof R_ex_TMR i.
    remember (Get_TMR i) as X0.
    pose proof R_ex_TMR 0.
    rewrite Zero_TMR in *.
    pose proof X X0 R0.
    clear HeqX0 X.
    destruct H1.
    - rewrite Bin_R_pro3 in e.
      pose proof e j.
      clear e.
      rewrite Zero_Bin in H1.
      apply (TMR_proper0 i X0 H) in H1.
      auto.
    - apply Bin_R_pro3_not in n.

  Admitted.
  
  Theorem Up_R : (forall (r : R) (z : Z) , IZR z <= r /\ r <= IZR (z + 1) -> up r = z) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof R_ex_TMR i.
    remember (Get_TMR i) as X0.
    pose proof R_ex_TMR 0.
    rewrite Zero_TMR in *.
    clear HeqX0.
  Admitted.
  (** This theorem also proves the uncomputability of Int_part frac_part *)

  Theorem Three_dimensions : (forall r1 r2 : R, {r1 = r2} + {r1 > r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Two_dimensions.
    intros.
    pose proof (X r1 r2).
    clear X.
    destruct H ; auto.
    - destruct s ; auto.
      right.
      apply Bin_R_pro3_not.
      apply Bin_R_pro3'' in r.
      inversion r.
      exists x.
      unfold not.
      intros.
      rewrite H0 in H.
      inversion H.
      apply (Nat.lt_irrefl (Bin_R r2 x)) in H1. auto. 
    - right.
      apply Bin_R_pro3_not.
      apply Bin_R_pro3' in r.
      inversion r. exists x.
      unfold not. intros.
      rewrite H0 in H.
      inversion H.
      apply (Nat.lt_irrefl (Bin_R r2 x)) in H1. auto.
  Qed.
  
  Theorem Two_dimensions2 : (forall r1 r2 : R, {r1 >= r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Three_dimensions.
    intros.
    pose proof (X r1 r2).
    destruct H ; auto.
  Admitted.
  
  (** This theorem also proves the uncomputability of Rmax Rmin Rabs Rdist*)
  (** Rmax Rmin Rabs Rdist are actually computable. Defined in an incorrect way in std. -- Qinxiang *)

  Theorem Rinv_def : forall (Rinv' : R -> R)(r: R) (H : r <> R0) ,Rinv' r = Rinv (exist _ r H) -> Halting.
  Proof.  intros. Admitted.
  Theorem Rpow_def : forall (Rpow' : R -> nat -> R)(r: R)(H : r <> R0) ,Rpow' r 0%nat = Rpow (exist _ r H) 0%nat -> Halting.
  Proof.  intros. Admitted.
  (** This theorem also proves the problem in the definition of powRZ *)

  Parameter Un_cv : (nat -> R) -> R -> Prop. (** the limitation of a list of Real Number *)
  
  Theorem lim_CN_NCN :forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> ~ CR l1.
  Proof. Admitted.
  
End Vir_R.


(** Module Uncomputable_function <: Vir_R.
  
End Uncomputable_function. *)


