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
  Parameter Rlim : (nat -> Real) -> Real -> Prop.
  Definition Reqb (x y : R) : Prop := x <= y /\ y <= x.
  Parameter Reqb_refl : forall (x : R) , Reqb x x.
  Theorem Proper_Reqb : forall (x : R),Proper Reqb x.
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

Module Uncomputable_function .
  Parameter Rinv : {a0 : R | ~(a0 = 0)%R} -> R.
  Parameter Rpow : {a0 : R | ~(a0 = 0)%R} -> nat -> R. 
  Parameter CR : R -> Prop.
  Axiom R_ex_TMR : forall r : R , (exists (n : nat) , TMR n r).
  
  Theorem P_AND_NP : forall P : Prop, {P} + {~ P} -> Halting.
  Proof. Admitted.
  
  Theorem P_AND_NP' : (forall P : Prop, {P} + {~ P}) -> Halting.
  Proof. Admitted.

  Theorem Three_dimensions : forall r1 r2 : R, ({r1 = r2} + {r1 > r2} + {r1 < r2})%R -> Halting.
  Proof.
    intros.
    pose proof R_ex_TMR r1.
    pose proof R_ex_TMR r2.
    
  Admitted.

  Theorem Three_dimensions' : (forall r1 r2 : R, ({r1 = r2} + {r1 > r2} + {r1 < r2})%R) -> Halting.
  Proof. 
    intros.
  Admitted.

  Theorem Two_dimensions : forall r1 r2 : R, ({r1 = r2} + {r1 <> r2})%R -> Halting.
  Proof. intros. apply P_AND_NP in H. auto. Qed.

  Theorem Two_dimensions' : (forall r1 r2 : R, ({r1 = r2} + {r1 <> r2})%R) -> Halting.
  Proof. intros. Admitted.

  Theorem Two_dimensions2 : forall r1 r2 : R, ({r1 >= r2} + {r1 < r2})%R -> Halting.
  Proof. 
     intros. 
     apply (Three_dimensions r1 r2).
     destruct H.
     - unfold Rge in *.
  Admitted. 

  Theorem Two_dimensions2' : (forall r1 r2 : R, ({r1 >= r2} + {r1 < r2})%R) -> Halting.
  Proof. 
     intros. 
     apply Three_dimensions'.
  Admitted. 
  (** This theorem also proves the uncomputability of Rmax Rmin Rabs Rdist*)
  (** Rmax Rmin Rabs Rdist are actually computable. Defined in an incorrect way in std. -- Qinxiang *)

  Theorem Rinv_def : forall (Rinv' : R -> R)(r: R) (H : r <> 0%R) ,Rinv' r = Rinv (exist _ r H) -> Halting.
  Proof.  intros. Admitted.
  Theorem Rpow_def : forall (Rpow' : R -> nat -> R)(r: R)(H : r <> 0%R) ,Rpow' r 0%nat = Rpow (exist _ r H) 0%nat -> Halting.
  Proof.  intros. Admitted.
  (** This theorem also proves the problem in the definition of powRZ *)
  Theorem Up_R : forall (r : R)(z : Z), up r = z -> Halting.
  Proof.  
    intros.
    pose proof R_ex_TMR (IZR (up r)).
    pose proof R_ex_TMR (IZR z).
    assert (H' : IZR (up r) = IZR z).
    { apply Rle_le_eq.
      split ; apply IZR_le ; rewrite H ; apply Z.le_refl.
    }
    apply (Three_dimensions (IZR (up r)) (IZR z)).
    left. left. apply H'.
  Admitted.
  (** This theorem also proves the uncomputability of Int_part frac_part *)
  Theorem lim_CN_NCN :forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> ~ CR l1.
  Proof. Admitted.
  
End Uncomputable_function.


