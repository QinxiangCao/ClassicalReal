(** Uncomputablity in the definition of R function **)
(** For convenience's sake, we focus on real numbers in [0,1] **) 
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
Parameter A : Type.
Parameter TM : nat -> nat -> Prop.
Parameter TM_input : nat -> A -> nat -> Prop.
Definition Halting : Type := forall i : nat , {exists j, TM i j} + {forall j , ~ TM i j}.
Definition Halting_easy : Type := exists f : Halting , True.
Definition Halting_easy' : Type := forall i : nat , exists f : ({exists j, TM i j} + {forall j , ~ TM i j}), True.
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

  Axiom Up_same : forall (r1 r2 : R) , r1 = r2 -> (up r1 = up r2)%Z.
  Axiom Up_R0 : (up R0 = 0)%Z.
  Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Axiom Rlt_not_refl : forall r1 : R , ~ (r1 < r1).
  Theorem Req : forall (x y : R) , x <= y /\ y <= x <-> x = y.
  Proof.
    intros.
    split.
    - intros.
      destruct H ; auto.
      destruct H ; auto.
      destruct H0 ; auto.
      pose proof Rlt_trans x y x H H0.
      exfalso. apply (Rlt_not_refl x) ; auto.
    - intros.
      split ; unfold Rle in * ; unfold Rge in *; auto.
  Qed.
  
  Theorem Rle_ge : forall (x y : R) , x >= y <-> y <= x.
  Proof.
    intros.
    unfold Rge in *.
    unfold Rle in *.
    split ; intros ; destruct H ; auto.
  Qed.
  
  Parameter Rplus_0 : forall r1 r2 : R , r1 - r2 = R0 <-> r1 = r2.
  Parameter IZR_0 : forall z : Z , IZR z = R0 <-> (z = 0)%Z.
  Theorem IZR_0' : IZR 0 = R0.
  Proof.
    apply IZR_0 ; auto.
  Qed.
  Parameter Z_same_R : forall z1 z2 : Z , (z1 = z2)%Z <-> IZR z1 = IZR z2.
  Theorem Z_same_R' : forall z1 z2 : Z , (z1 <> z2)%Z <-> IZR z1 <> IZR z2.
  Proof.
    unfold not in *.
    intros. 
    split ; intros ; apply H ; apply Z_same_R ; auto.
  Qed.
  Theorem Ex_Z_R' : forall z : Z , (z <> 0)%Z <-> IZR z <> R0.
  Proof.
    unfold not in *.
    intros.
    split ; intros ; apply H ; apply IZR_0 ; auto.
  Qed.
  
  Axiom Rle_ge_eq : forall x y : R , x >= y -> y >= x -> x = y.

  (** The definition of R Number matched with Turing machine *)
  Parameter Bin_R : R -> nat -> nat -> Prop.
  Parameter TMR : nat -> R -> Prop.

  Axiom TMR_pro0 : forall (r : R) (n : nat) , TMR n r -> r >= R0.
  Axiom TMR_pro0' : forall (r : R) (n : nat) , TMR n r -> r <= R1.
  (** These two axioms above may be proved by other axioms. *)

  Axiom Bin_R_pro1 : forall (r : R) (n : nat) , Bin_R r n 1 \/ Bin_R r n 0.
  Axiom Bin_R_pro2 : forall (r : R) (n : nat) , Bin_R r n 1 <-> (~ Bin_R r n 0).
  Axiom Zero_Bin : forall (n : nat) , Bin_R R0 n 0.
  Axiom One_Bin : forall (n : nat) , Bin_R R1 n 1.
  Theorem Bin_R_pro2' : forall (r : R) (n : nat) , (~Bin_R r n 1) <-> (Bin_R r n 0).
  Proof.
    intros.
    split.
    - intros. apply NNPP. unfold not in *.
      intros. apply H. apply Bin_R_pro2. unfold not in *. apply H0.
    - unfold not in *. intros. rewrite Bin_R_pro2 in H0.
      apply H0. apply H.
  Qed.

  Axiom Bin_R_pro3  : forall (r1 r2 : R) , r1 = r2 <-> (forall (j : nat) , Bin_R r1 j 1 <-> Bin_R r2 j 1).
  Axiom Bin_R_pro3' : forall (r1 r2 : R) , r1 < r2 <-> 
                      exists (j : nat), (Bin_R r1 j 0) /\ (Bin_R r2 j 1) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (Bin_R r1 k 1 <-> Bin_R r2 k 1)).
  
  Theorem Bin_R_pro3'' : forall (r1 r2 : R) , r1 > r2 <-> 
                      exists (j : nat), (Bin_R r1 j 1) /\ (Bin_R r2 j 0) /\ 
                                      (forall (k : nat) , (k < j)%nat -> (Bin_R r1 k 1 <-> Bin_R r2 k 1)%nat).
  Proof.
    intros.
    pose proof (Bin_R_pro3' r2 r1).
    split.
    - intros.
      apply H in H0.
      inversion H0.
      exists x.
      destruct H1 as [H2 [H3 H4]].
      split ; auto.
      split ; auto.
      intros.
      rewrite (H4 _ H1). apply iff_refl.
    - intros.
      apply H.
      inversion H0.
      exists x.
      destruct H1 as [H2 [H3 H4]].
      split ; auto.
      split ; auto.
      intros.
      rewrite (H4 _ H1). apply iff_refl.
  Qed.

  Theorem Bin_R_pro3_not : forall (r1 r2 : R) , r1 <> r2 <-> exists (j : nat), (Bin_R r1 j 1 <-> Bin_R r2 j 0).
  Proof.
    intros.
    split.
    - intros.
      pose proof Bin_R_pro3 r1 r2.
      rewrite H0 in H.
      clear H0.
      apply not_all_ex_not in H.
      destruct H.
      exists x.
      unfold not in H.
      split.
      + intros. apply Bin_R_pro2'. unfold not. intros. apply H.
        split ; auto.
      + intros. apply Bin_R_pro2. unfold not. intros. apply H.
        split ; intros ; apply Bin_R_pro2 in H2 ; exfalso ; apply H2 ; auto.
    - intros.
      destruct H.
      unfold not in *.
      intros.
      rewrite (Bin_R_pro3 r1 r2) in H0.
      rewrite (H0 x) in H.
      rewrite (Bin_R_pro2 r2 x) in H.
      destruct H.
      pose proof classic (Bin_R r2 x 0).
      destruct H2.
      + apply H1 ; auto.
      + apply H2 ; auto.
  Qed.
  
  Axiom R_is_TMR : forall (n:nat) (r:R) , TMR n r <-> (forall (j : nat), TM n j -> Bin_R r j 1) /\ (forall (j:nat) , ~ TM n j -> Bin_R r j 0).
  Theorem TMR_proper0 : forall (n:nat) (r:R) , TMR n r -> forall (j : nat), (Bin_R r j 1 -> TM n j) /\ (Bin_R r j 0 -> ~TM n j).
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

  Theorem TMR_proper1 : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r j 1) -> (Bin_R r k 1)).
  Proof.
    intros.
    pose proof H.
    rewrite R_is_TMR in H.
    destruct H.
    apply H.
    apply Turing_proper1 with j ; auto.
    pose proof (TMR_proper0 _ _ H2 j).
    apply H4. 
    auto.
  Qed.

  Theorem TMR_proper1' : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r k 0) -> (Bin_R r j 0)).
  Proof.
    intros.
    pose proof H.
    rewrite R_is_TMR in H.
    destruct H.
    apply H3.
    unfold not. intros.
    apply H in H4.
    apply (TMR_proper1 n r H2 j k H0) in H4.
    apply Bin_R_pro2 in H4.
    apply H4 ; auto.
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
   
  Theorem P_OR_NP : (forall P : Prop, {P} + {~ P}) -> Halting.
  Proof. 
    unfold Halting.
    intros.
    pose proof X (exists j : nat , TM i j).
    destruct H ; auto.
    right.
    unfold not in *.
    intros.
    apply n.
    exists j ; auto.
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
      pose proof Zero_Bin.
      right. intros.
      apply (TMR_proper0 i X0 H j).
      apply Bin_R_pro2'.
      rewrite (e j).
      apply Bin_R_pro2' ; auto.
    - apply Bin_R_pro3_not in n.
      left.
      inversion n.
      exists x.
      apply (TMR_proper0 i X0 H x).
      apply Bin_R_pro2.
      unfold not in *.
      intros. 
      apply Bin_R_pro2' in H2.
      apply H2. apply H1.
      apply Zero_Bin.
  Qed.

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
      destruct r as [x [H1 [H2 H3]]].
      exists x.
      unfold not.
      intros.
      split ; auto.
    - right.
      apply Bin_R_pro3_not.
      apply Bin_R_pro3' in r.
      destruct r as [x [H1 [H2 H3]]].
      exists x.
      unfold not.
      intros.
      split ; intros ; exfalso.
      + apply Bin_R_pro2 in H. apply H ; auto.
      + apply Bin_R_pro2' in H. apply H ; auto.
  Qed.
  
  Theorem Two_dimensions2 : (forall r1 r2 : R, {r1 >= r2} + {r1 < r2}) -> Halting.
  Proof. 
    intros.
    apply Three_dimensions.
    intros.
    pose proof (X r1 r2).
    destruct H ; auto.
    pose proof (X r2 r1).
    destruct H ; auto.
    left. left.
    apply Rle_ge_eq ; auto.
  Qed.
  
  Theorem Exam_dimensions2 : (forall r : R , {r = R0} + {r <> R0}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    apply Two_dimensions.
    intros.
    pose proof X (r1 - r2).
    destruct H.
    - left. apply Rplus_0 ; auto.
    - right. unfold not in *.  intros. apply n. apply Rplus_0 ; auto.
  Qed.
  (** This theorem also proves the uncomputability of Rmax Rmin Rabs Rdist*)
  (** Rmax Rmin Rabs Rdist are actually computable. Defined in an incorrect way in std. -- Qinxiang *)

  Parameter RnZ : R -> nat -> Z. (** use the first n numbers of R to construct a member of Z *)
  Axiom RnZ_pro1 : forall (r : R) (n : nat) , (forall (j : nat) , (j > n)%nat -> (Bin_R (IZR (RnZ r n)) j 0)). 
  Axiom RnZ_pro2 : forall (r : R) (n : nat) , (forall (j : nat) , (j <= n)%nat -> (Bin_R r j 1 <-> Bin_R (IZR (RnZ r n))j 1)).

  Lemma Turing_eqb_1 : forall (n : nat) (r : R), TMR n r -> ((forall (j : nat) , (RnZ r j = 0)%Z) <-> (forall (j : nat), ~ TM n j)).
  Proof.
    intros.
    pose proof TMR_proper0 n r H.
    split ; intros.
    - pose proof H1 j.
      apply (IZR_0 (RnZ r j)) in H2.
      apply H0. 
      apply Bin_R_pro2'. unfold not in *.
      intros.
      apply (RnZ_pro2 r j j) in H3 ; auto.
      rewrite H2 in H3.
      pose proof Zero_Bin j.
      apply Bin_R_pro2' in H4.
      apply H4 ; auto.
    - apply Z_same_R. rewrite IZR_0'.
      apply Bin_R_pro3. intros.
      pose proof le_gt_dec j0 j.
      destruct H2. 
      + pose proof RnZ_pro2 r j j0 l.
        rewrite <- H2.
        split.
        * intros. apply H0 in H3.
          apply Bin_R_pro2. unfold not in *.
          intros. apply (H1 j0) ; auto.
        * intros. exfalso. apply Bin_R_pro2 in H3.
          apply H3. apply Zero_Bin.
      + pose proof RnZ_pro1 r j j0 g.
        split.
        * intros. exfalso. apply Bin_R_pro2 in H3. apply H3;auto.
        * intros. exfalso. apply Bin_R_pro2 in H3. apply H3. apply Zero_Bin.
  Qed.

  Lemma Turing_eqb_1' : forall (n : nat) (r : R), TMR n r -> ((exists (j : nat) , (RnZ r j <> 0)%Z) <-> (exists (j : nat), TM n j)).
  Proof.
    intros.
    pose proof TMR_proper0 n r H.
    split ; intros ; destruct H1.
    - apply Ex_Z_R' in H1.
      apply Bin_R_pro3_not in H1.
      destruct H1. exists x0.
      apply H0.
      pose proof le_gt_dec x0 x.
      destruct H2. 
      + pose proof RnZ_pro2 r x x0 l.
        apply H2. apply H1. apply Zero_Bin.
      + pose proof RnZ_pro1 r x x0 g.
        apply Bin_R_pro2' in H2.
        exfalso. apply H2. apply H1. apply Zero_Bin.
    - exists x.
      apply Ex_Z_R'. 
      apply Bin_R_pro3_not.
      exists x.
      assert (H' : (x <= x) %nat). { auto. }
      pose proof RnZ_pro2 r x x H'. clear H'.
      rewrite <- H2.
      split ; intros.
      + apply Zero_Bin.
      + apply (R_is_TMR n r) in H.
        apply H in H1 ; auto.
  Qed.
  
  Theorem Up_R : (forall (r : R) (z : Z) , IZR (z - 1) < r /\ r <= IZR z <-> (up r = z)%Z) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof R_ex_TMR i.
    remember (Get_TMR i) as X0.
    clear HeqX0.
    pose proof Z.eq_dec (up X0) 0%Z.
    pose proof (TMR_pro0 X0 i H0).
    destruct H1.
    - rewrite <- (H X0 0%Z) in e.
      simpl in *. destruct e.
      rewrite IZR_0' in H3.
      apply (Rle_ge X0 R0) in H2.
      pose proof conj H3 H2.
      apply (Req X0 R0) in H4.
      right.
      rewrite (Bin_R_pro3 X0 R0) in H4.
      intros.
      clear H3 H2 H1.
      apply (TMR_proper0 i X0 H0 j).
      apply Bin_R_pro2'. unfold not.
      intros. apply H4 in H1.
      apply Bin_R_pro2 in H1.
      apply H1. apply Zero_Bin.
    - left. destruct H2.
      + apply Bin_R_pro3' in H1.
        destruct H1. exists x.
        apply (TMR_proper0 i X0 H0 x).
        destruct H1 as [ ? [?  ? ]] ; auto.
      + apply Up_same in H1.
        exfalso. apply n.
        rewrite H1. apply Up_R0.
  Qed.
  (** This theorem also proves the uncomputability of Int_part frac_part *)
  

  (** (single point set -> R) -> (Rinv : {a0 : R | a0 <> R0} -> R) -> (Rinv' : R -> R) *)
  Parameter Rsinglefun : {X: R -> Prop | (forall x1 x2, X x1 -> X x2 ->
  x1 = x2) /\ (exists x, X x) /\ Proper (Reqb ==> iff) X} -> R.

  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
  
  Definition rinv (a : R) (H : a <> R0) : R.
    apply Rinv.
    exists a. apply H.
  Defined.

  Axiom rinv_eqb : forall (x y : R) (H : x <> R0) (H' : y <> R0) , rinv x H = rinv y H' <-> x = y.
 
  Definition Rinv' (a : R): R.
    apply Rsinglefun.
    exists (fun b => (exists H: a <> R0, (rinv a H) = b) \/
                   (a = R0 /\ b = R0)).
    split; [| split].
    - intros.
      destruct H. 
      + destruct H. rewrite <- H. symmetry.
        destruct H0.  
        * destruct H0. rewrite <- H0.
          apply rinv_eqb. auto.
        * exfalso. apply x. apply H0.
      + destruct H0.
        * destruct H0. exfalso. apply x. apply H.
        * destruct H. destruct H0. rewrite H1. auto. 
    - pose proof (classic (a = R0)).
      destruct H.
      + exists R0. right. split ; auto.
      + exists (rinv a H). left. exists H. auto.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Defined.
   
  Definition rpow (a : R) (H : a <> R0) : nat -> R.
    apply Rpow.
    exists a. apply H.
  Defined.

  Axiom rpow_eqb : forall (x y : R)(z : nat) (H : x <> R0) (H' : y <> R0) , rpow x H z = rpow y H' z <-> x = y.
 
  Definition Rpow' (a : R) (z : nat) : R.
    apply Rsinglefun.
    exists (fun b => (exists H: a <> R0, (rpow a H z) = b) \/
                   (a = R0 /\ b = R0)).
    split; [| split].
    - intros.
      destruct H. 
      + destruct H. rewrite <- H. symmetry.
        destruct H0.  
        * destruct H0. rewrite <- H0.
          apply rpow_eqb. auto.
        * exfalso. apply x. apply H0.
      + destruct H0.
        * destruct H0. exfalso. apply x. apply H.
        * destruct H. destruct H0. rewrite H1. auto. 
    - pose proof (classic (a = R0)).
      destruct H.
      + exists R0. right. split ; auto.
      + exists (rpow a H z). left. exists H. auto.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Defined.
 
  Definition CR (r : R) : Prop := 
      exists f : R -> nat -> nat, (forall (n: nat), (f r n = 1%nat \/ f r n = 0%nat) /\ Bin_R r n (f r n)).
  Definition CR' (r : R) := {f : R -> nat -> nat | (forall (n: nat), (f r n = 1%nat \/ f r n = 0%nat) /\ Bin_R r n (f r n)) }.

  Theorem CR_CR' : forall r : R , CR' r -> CR r.
  Proof.
    intros.
    unfold CR' in *.
    unfold CR in *.
    destruct X as [f ?].
    exists f. auto.
  Qed.
  
  Parameter TM'r : nat -> R.
  Axiom TM'r_pro0 : forall (n m: nat), Bin_R (TM'r n) m 1 <-> TM m n.
  Theorem TM'r_pro0' : forall (n m : nat), Bin_R (TM'r n) m 0 <-> ~ TM m n.
  Proof.
    intros.
    pose proof TM'r_pro0 n m.
    unfold not in *.
    split ; intros. 
    - apply Bin_R_pro2 in H0 ; auto.
      apply H. auto.
    - apply Bin_R_pro2'. unfold not. intros.
      apply H0. apply H. auto.
  Qed.

  Theorem TM'r_pro1 : forall (n m : nat) , Bin_R (TM'r n) m 1 -> (forall (r : nat) , (r >= n)%nat -> Bin_R (TM'r r) m 1).
  Proof.
    intros.
    apply TM'r_pro0 in H.
    apply TM'r_pro0.
    pose proof Turing_proper1 m n r.
    apply H1 ; auto.
  Qed.
  
  Theorem TM'r_pro1' : forall (n m : nat) , Bin_R (TM'r n) m 0 -> (forall (r : nat) , (r <= n)%nat -> Bin_R (TM'r r) m 0).
  Proof.
    intros.
    apply TM'r_pro0' in H.
    apply TM'r_pro0'.
    pose proof Turing_proper2 m n r.
    apply H1 ; auto.
  Qed.

  Parameter limitTM'r : R.
  Axiom limitTM'r_pro : forall (n : nat) , Bin_R limitTM'r n 1 <-> exists j : nat , TM n j.
  Theorem limitTM'r_pro' : forall (n : nat) , Bin_R limitTM'r n 0 <-> forall j : nat ,~ TM n j. 
  Proof.
    intros.
    pose proof limitTM'r_pro n.
    unfold not in *.
    split ; intros.
    - apply Bin_R_pro2 in H0 ; auto. apply H. exists j. auto.
    - apply Bin_R_pro2'. unfold not . intros.
      apply H in H1.
      destruct H1.
      apply (H0 x) ; auto. 
  Qed.

  Theorem limitTM'r_pro1 : (forall (n : nat) , {Bin_R limitTM'r n 0} + {Bin_R limitTM'r n 1}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof H i.
    destruct H0.
    - rewrite (limitTM'r_pro' i) in b. auto.
    - rewrite (limitTM'r_pro i) in b. auto.
  Qed.

  Axiom TM'r_is_computable' : forall n : nat , CR' (TM'r n).
  Theorem TM'r_is_computable : forall n : nat , CR (TM'r n).
  Proof.
    intros.
    apply CR_CR'. apply TM'r_is_computable'.
  Qed.

  Parameter Un_cv : (nat -> R) -> R -> Prop.
  Axiom limit_of_TM'r : Un_cv TM'r limitTM'r.
 (** the limitation of a list of Real Number *)

  Theorem lim_CN_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> CR l1) -> Halting_easy'.
  Proof. 
    intros.
    pose proof H TM'r limitTM'r limit_of_TM'r TM'r_is_computable.
    clear H.
    unfold CR in *.
    unfold Halting_easy'.
    inversion H0.
    intros.
    pose proof H i.
    clear H.
    destruct H1 as [[ ? | ?] ?].
    - rewrite H in H1.
      rewrite (limitTM'r_pro i) in H1.
      assert (H' : {exists j : nat, TM i j} + {forall j : nat, ~ TM i j}) by auto.
      exists H'. auto.
    - rewrite H in H1.
      rewrite (limitTM'r_pro' i) in H1.
      assert (H' : {exists j : nat, TM i j} + {forall j : nat, ~ TM i j}) by auto.
      exists H'. auto.
  Qed.
  
  Theorem lim_CN_NCN' : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> CR l1) -> Halting_easy.
  Proof. 
    intros.
    pose proof H TM'r limitTM'r limit_of_TM'r TM'r_is_computable.
    clear H.
    unfold CR in *.
    unfold Halting_easy.
    destruct H0 as [f ?].
    unfold Halting.
    Print ex.
    refine (@ex_intro _ _ _ I).
    intros.
    pose proof H i.
    clear H.
    destruct H0 as [? ?].
    destruct (f limitTM'r i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct H. 
      + apply eq_add_S in H. discriminate H.
      + discriminate H.
  Qed.
  
  Theorem lim_CN'_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR' (Un n)) -> CR' l1) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof X TM'r limitTM'r limit_of_TM'r TM'r_is_computable'.
    clear X.
    unfold CR' in *.
    destruct X0 as [f ].
    destruct (a i).
    clear a.
    destruct (f limitTM'r i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct H. 
      + apply eq_add_S in H. discriminate H.
      + discriminate H.
  Qed.
  
End Vir_R.


(** Module Uncomputable_function <: Vir_R.
  
End Uncomputable_function. *)


