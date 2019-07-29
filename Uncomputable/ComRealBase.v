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
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Export Field.
From Coq Require Export Omega.
From CReal Require Export Uncomputable.TMSet.
Import ListNotations.
Import TM_0_0.
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
  Parameter Rabs : R -> R.
  Parameter up : R -> Z.
  Parameter IZR : Z -> R.
  Parameter QTR : Q -> R.
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
  
  Parameter QTR_0 : forall q : Q , QTR q = R0 <-> (q = 0)%Q.
  Theorem QTR_0' : QTR 0 = R0.
  Proof.
    apply QTR_0 ; auto.
  Qed.
  Parameter Q_same_R : forall q1 q2 : Q , (q1 = q2)%Z <-> QTR q1 = QTR q2.
  Theorem Q_same_R' : forall q1 q2 : Q , (q1 <> q2)%Z <-> QTR q1 <> QTR q2.
  Proof.
    unfold not in *.
    intros. 
    split ; intros ; apply H ; apply Q_same_R ; auto.
  Qed.
  Theorem Ex_Q_R' : forall q : Q , (q <> 0)%Q <-> QTR q <> R0.
  Proof.
    unfold not in *.
    intros.
    split ; intros ; apply H ; apply QTR_0 ; auto.
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
  
  Axiom R_is_TMR : forall (n:nat) (r:R) , TMR n r <-> (forall (j : nat), Bin_R r j (TM n j)).
  Theorem TMR_proper0 : forall (n:nat) (r:R) , TMR n r -> forall (j : nat), (Bin_R r j 1 -> TM n j = 1%nat) /\ (Bin_R r j 0 -> TM n j = 0%nat).
  Proof.
    intros.
    rewrite R_is_TMR in H.
    destruct (Turing_proper0 n j) ; split ; auto ; intros.
    - pose proof H j.
      rewrite H0 in H2.
      rewrite Bin_R_pro2 in H1.
      exfalso. apply H1 ; auto.
    - pose proof H j.
      rewrite H0 in H2.
      rewrite Bin_R_pro2 in H2.
      exfalso. apply H2 ; auto.
  Qed.

  Theorem TMR_proper1 : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r j 1) -> (Bin_R r k 1)).
  Proof.
    intros.
    pose proof H.
    rewrite R_is_TMR in H.
    pose proof H k.
    assert (H' : TM n j = 1%nat).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n k = 1%nat).
    { apply Turing_proper1 with j ; auto. }
    rewrite H'' in H3.
    auto.
  Qed.

  Theorem TMR_proper1' : forall (n : nat) (r : R), TMR n r -> (forall (j k : nat), (j <= k)%nat -> (Bin_R r k 0) -> (Bin_R r j 0)).
  Proof.
    intros.
    pose proof H.
    rewrite R_is_TMR in H.
    pose proof H j.
     assert (H' : TM n k = 0%nat).
    { apply (TMR_proper0 n r H2) ; auto. }
    assert (H'' : TM n j = 0%nat).
    { apply Turing_proper2 with k ; auto. }
    rewrite H'' in H3.
    auto.
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
    pose proof X (exists j : nat , TM i j = 1%nat).
    destruct H ; auto.
    right.
    intros.
    destruct (Turing_proper0 i j) ; auto.
    exfalso. apply n. exists j. auto.
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
      exists f : nat -> nat, (forall (n: nat), (f n = 1%nat \/ f n = 0%nat) /\ Bin_R r n (f n)).
  Definition CR1 (r : R) := {f : nat -> nat | (forall (n: nat), (f n = 1%nat \/ f n = 0%nat) /\ Bin_R r n (f n)) }.
  Definition limit (f : nat -> Q) (r : R) : Prop :=
    forall eps : Q , (eps > 0)%Q -> exists N : nat , forall n : nat , (n >= N)%nat -> Rabs(QTR (f n) - r) < QTR eps.
  (** exists a sequence of rational number limits to r *)
  Definition CR2 (r : R) := exists f : nat -> Q, limit f r.
  (** exists a Cauthy sequence of rational number limits to r *)
  Definition CR3 (r : R) :=
      {f : nat -> Q & {N : Q -> nat | limit f r /\ (forall eps : Q , (eps > 0)%Q -> forall (n m : nat) , (n >= N eps)%nat /\ (n >= 1) %nat -> (m >= n)%nat -> (Qabs(f n - f m) < eps)%Q)} }.
 
  Theorem CR1_CR : forall r : R , CR1 r -> CR r.
  Proof.
    intros.
    unfold CR1 in *.
    unfold CR in *.
    destruct H as [f ?].
    exists f. auto.
  Qed.
  Theorem CR3_CR2 : forall r : R , CR3 r -> CR2 r.
  Proof.
    unfold CR3 in *.
    unfold CR2 in *.
    intros.
    destruct H as [? [? ?]].
    exists x. destruct a. auto.
  Qed.

  Fixpoint sum_f (f : nat -> nat) (n : nat) : Q :=
    match n with
      | 0%nat => Z_of_nat (f 0%nat) # 1%positive
      | S n' => (sum_f f n' + (Z_of_nat (f n) # Pos.of_nat (2 ^ n)))%Q
    end.
 
  Axiom sum_f_limit_r : forall (f : nat -> nat) (r : R) , limit (sum_f f) r <-> (forall n : nat , Bin_R r n (f n)).
  
  Axiom sum_f_limit_eps : forall (f : nat -> nat)(n m : nat) , (n <= m) % nat -> (Qabs(sum_f f n - sum_f f m) < 1%Z # Pos.of_nat (2^n))%Q.

  Theorem CR_CR2 : forall r : R , CR r -> CR2 r.
  Proof.
    unfold CR.
    unfold CR2.
    intros.
    destruct H.
    exists (sum_f x).
    rewrite sum_f_limit_r.
    apply H.
  Qed.

  Lemma Mult_pow2 : forall n : nat,(2 ^ (S n) = 2 ^ n * 2)%nat.
  Proof.
    intros.
    replace (S n) with ((n + 1)%nat).
    - apply Nat.pow_add_r.
    - apply Nat.add_1_r.
  Qed.
  
  Lemma Max_powSn_1 : forall n : nat , ( n >= 1 -> 2 ^ n > 1)%nat.
  Proof.
    intros.
    induction n.
    - inversion H.
    - assert (H' : forall p : nat , (2 ^ p > 0) %nat).
      { intros. induction p.
        + simpl. apply Nat.lt_0_1.
        + rewrite Mult_pow2.
          apply Nat.mul_pos_pos ; auto.
      }
      simpl. rewrite <- plus_n_O.
      apply Nat.lt_le_trans with (m := (1 + 2 ^ n) % nat).
      simpl. apply lt_n_S. apply (H' n). 
      apply plus_le_compat_r. 
      pose proof H' n.
      apply H0.
  Qed.
  
  Lemma nat_le_four : forall (n m q p : nat) , (n <= m)%nat -> (p <= q)%nat -> (n + p <= m + q)%nat.
  Proof.
    intros.
    apply Nat.le_trans with (m := (n + q)%nat).
    - apply plus_le_compat_l. auto.
    - apply plus_le_compat_r. auto.
  Qed.
  
  Lemma nat_lt_four : forall (n m q p : nat) , (n < m)%nat -> (p < q)%nat -> (n + p < m + q)%nat.
  Proof.
    intros.
    apply Nat.lt_trans with (m := (n + q)%nat).
    - apply plus_lt_compat_l. auto.
    - apply plus_lt_compat_r. auto.
  Qed.

  Lemma ge_pow_ge : forall n: nat , (2 ^ n > n)%nat.
  Proof.
    intros.
    apply Nat.pow_gt_lin_r.
    auto.
  Qed.
  
  Lemma Z_le_lt_trans : forall z1 z2 z3 :Z , (z1 <= z2 -> z2 < z3 -> z1 < z3)%Z.
  Proof.
    intros.
    apply Zle_compare in H.
    destruct ((z1 ?= z2) % Z) eqn : En.
    - apply Z.compare_eq in En. rewrite En. auto.
    - apply Zcompare_Lt_trans with z2 ; auto.
    - inversion H.
  Qed.
  
  Lemma eps_lemma : forall eps : Q , (eps > 0)%Q -> (1 # Pos.of_nat (2 ^ S (Pos.to_nat (Qden eps) / Z.to_nat (Qnum eps))) <
 eps)%Q.
  Proof.
  Admitted.
  
  Theorem CR1_CR3 : forall r : R , CR1 r -> CR3 r.
  Proof.
    unfold CR1.
    unfold CR3.
    intros.
    destruct H.
    exists (sum_f x).
    exists (fun eps => (2 ^ S (Pos.to_nat(Qden eps) / Z.to_nat (Qnum eps)))%nat).
    split.
    - rewrite sum_f_limit_r. apply a.
    - 
      intros.
      apply Qlt_trans with (y := (1%Z # Pos.of_nat(2 ^ S (Pos.to_nat(Qden eps) / Z.to_nat (Qnum eps)))%nat)).
      + apply Qlt_trans with (y := (1%Z # Pos.of_nat (2^n))%Q).
        * apply sum_f_limit_eps ; auto.
        * unfold Qlt. simpl.
          apply Pos2Z.pos_lt_pos.
          apply Pos2Nat.inj_lt.
          repeat rewrite Nat2Pos.id_max.
          replace (max 1 (2 ^ n))%nat with (2 ^ n)%nat.
          destruct H.
          destruct H0.
          pose proof ge_pow_ge n.
          apply le_lt_trans with (m := n) ; auto.
          apply Nat.max_lub ; auto.
          symmetry.
          apply max_r.
          apply Nat.lt_le_incl.
          apply Max_powSn_1. apply H0.
      + apply eps_lemma. auto.
  Qed.
  
  Parameter TM'r : nat -> R.
  Axiom TM'r_pro : forall (n m: nat), Bin_R (TM'r n) m (TM m n).

  Theorem TM'r_pro0 : forall (n m : nat), Bin_R (TM'r n) m 1 <-> TM m n = 1%nat.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Bin_R_pro2 in H0 ; auto.
      destruct (Turing_proper0 m n) ; auto.
      rewrite H1 in H. exfalso. apply H0 ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r_pro0' : forall (n m : nat), Bin_R (TM'r n) m 0 <-> TM m n = 0%nat.
  Proof.
    intros.
    pose proof TM'r_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Bin_R_pro2' in H0 ; auto.
      destruct (Turing_proper0 m n) ; auto.
      rewrite H1 in H. exfalso. apply H0 ; auto.
    - rewrite H0 in H; auto.
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
  Axiom limitTM'r_pro : forall (n : nat) , Bin_R limitTM'r n 1 <-> exists j : nat , TM n j = 1%nat.
  Theorem limitTM'r_pro' : forall (n : nat) , Bin_R limitTM'r n 0 <-> forall j : nat , TM n j = 0%nat. 
  Proof.
    intros.
    pose proof limitTM'r_pro n.
    unfold not in *.
    split ; intros.
    - destruct (Turing_proper0 n j) ; auto.
      apply Bin_R_pro2 in H0 ; try inversion H0. 
      apply H. exists j ; auto. 
    - apply Bin_R_pro2'. unfold not . intros.
      apply H in H1.
      destruct H1.
      rewrite (H0 x) in H1.
      discriminate H1.
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

  Theorem TM'r_is_computable1 : forall n : nat , CR1 (TM'r n).
  Proof.
    intros.
    unfold CR1.
    exists (fun n0 => TM n0 n).
    intros.
    split.
    - destruct (Turing_proper0 n0 n) ; auto.
    - apply TM'r_pro.
  Qed.
  
  Theorem TM'r_is_computable : forall n : nat , CR (TM'r n).
  Proof.
    intros.
    apply CR1_CR. apply TM'r_is_computable1.
  Qed.
  
  Theorem TM'r_is_computable3 : forall n : nat , CR3 (TM'r n).
  Proof.
    intros.
    apply CR1_CR3. apply TM'r_is_computable1.
  Qed.

  Theorem TM'r_is_computable2 : forall n : nat , CR2 (TM'r n).
  Proof.
    intros.
    apply CR3_CR2. apply TM'r_is_computable3.
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
      assert (H' : {exists j : nat, TM i j = 1%nat} + {forall j : nat, TM i j = 0%nat}) by auto.
      exists H'. auto.
    - rewrite H in H1.
      rewrite (limitTM'r_pro' i) in H1.
      assert (H' : {exists j : nat, TM i j = 1%nat} + {forall j : nat, TM i j = 0%nat}) by auto.
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
    refine (@ex_intro _ _ _ I).
    intros.
    pose proof H i.
    clear H.
    destruct H0 as [? ?].
    destruct (f i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct H. 
      + apply eq_add_S in H. discriminate H.
      + discriminate H.
  Qed.
  
  Theorem lim_CN1_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR1 (Un n)) -> CR1 l1) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof X TM'r limitTM'r limit_of_TM'r TM'r_is_computable1.
    clear X.
    unfold CR1 in *.
    destruct H as [f ].
    destruct (a i).
    clear a.
    destruct (f i) as [ | [ | ]].
    - right. apply limitTM'r_pro' ; auto.
    - left. apply limitTM'r_pro ; auto.
    - exfalso. 
      destruct H. 
      + apply eq_add_S in H. discriminate H.
      + discriminate H.
  Qed.
  
  Parameter Dec_R : R -> nat -> nat -> Prop.
  Parameter TM'r' : nat -> R.
  Axiom TM'r'_pro : forall (n m: nat), Dec_R (TM'r' n) m (TM m n).
  Axiom Dec_TM'r'_pro1 : forall (n m: nat), Dec_R (TM'r' n) m 1 <-> ~ Dec_R (TM'r' n) m 0.
  Axiom Dec_TM'r'_pro1' : forall (n m: nat), Dec_R (TM'r' n) m 0 <-> ~ Dec_R (TM'r' n) m 1.
  Theorem TM'r'_pro0 : forall (n m : nat), Dec_R (TM'r' n) m 1 <-> TM m n = 1%nat.
  Proof.
    intros.
    pose proof TM'r'_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Dec_TM'r'_pro1 in H0 ; auto.
      destruct (Turing_proper0 m n) ; auto.
      rewrite H1 in H. exfalso. apply H0 ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r'_pro0' : forall (n m : nat), Dec_R (TM'r' n) m 0 <-> TM m n = 0%nat.
  Proof.
    intros.
    pose proof TM'r'_pro n m.
    unfold not in *.
    split ; intros. 
    - apply Dec_TM'r'_pro1' in H0 ; auto.
      destruct (Turing_proper0 m n) ; auto.
      rewrite H1 in H. exfalso. apply H0 ; auto.
    - rewrite H0 in H; auto.
  Qed.

  Theorem TM'r'_pro1 : forall (n m : nat) , Dec_R (TM'r' n) m 1 -> (forall (r : nat) , (r >= n)%nat -> Dec_R (TM'r' r) m 1).
  Proof.
    intros.
    apply TM'r'_pro0 in H.
    apply TM'r'_pro0.
    pose proof Turing_proper1 m n r.
    apply H1 ; auto.
  Qed.
  
  Theorem TM'r'_pro1' : forall (n m : nat) , Dec_R (TM'r' n) m 0 -> (forall (r : nat) , (r <= n)%nat -> Dec_R (TM'r' r) m 0).
  Proof.
    intros.
    apply TM'r'_pro0' in H.
    apply TM'r'_pro0'.
    pose proof Turing_proper2 m n r.
    apply H1 ; auto.
  Qed.

  Parameter limitTM'r' : R.
  Axiom limit_of_TM'r' : Un_cv TM'r' limitTM'r'.
  Axiom Dec_Q : forall (q : Q) (n:nat) , {Dec_R (QTR q) n 0} + {~Dec_R (QTR q) n 0}.
  Axiom limit_TM'r'_pro_pre : forall (f : nat -> Q) (n n0 m : nat), limit f limitTM'r' -> 
      (Qabs (f n0 - f m) < 1 # Pos.of_nat (10 ^ n))%Q -> (Dec_R (QTR(f n0)) n 0 <-> Dec_R limitTM'r' n 0).
  Axiom Dec_limitTM'r'_pro1 : forall (m: nat), Dec_R limitTM'r' m 1 <-> ~ Dec_R limitTM'r' m 0.
  Axiom Dec_limitTM'r'_pro1' : forall (m: nat), Dec_R limitTM'r' m 0 <-> ~ Dec_R limitTM'r' m 1.
  Axiom limitTM'r'_pro : forall (n : nat) , Dec_R limitTM'r' n 1 <-> exists j : nat , TM n j = 1%nat.
  Theorem limitTM'r'_pro' : forall (n : nat) , Dec_R limitTM'r' n 0 <-> forall j : nat , TM n j = 0%nat. 
  Proof.
    intros.
    pose proof limitTM'r'_pro n.
    unfold not in *.
    split ; intros.
    - destruct (Turing_proper0 n j) ; auto.
      apply Dec_limitTM'r'_pro1 in H0 ; try inversion H0. 
      apply H. exists j ; auto. 
    - apply Dec_limitTM'r'_pro1'. unfold not . intros.
      apply H in H1.
      destruct H1.
      rewrite (H0 x) in H1.
      discriminate H1.
  Qed.

  Theorem limitTM'r'_pro1 : (forall (n : nat) , {Dec_R limitTM'r' n 0} + {Dec_R limitTM'r' n 1}) -> Halting.
  Proof.
    unfold Halting.
    intros.
    pose proof H i.
    destruct H0.
    - rewrite (limitTM'r'_pro' i) in d. auto.
    - rewrite (limitTM'r'_pro i) in d. auto.
  Qed.

  Fixpoint sum_f' (f : nat -> nat) (n : nat) : Q :=
    match n with
      | 0%nat => Z_of_nat (f 0%nat) # 1%positive
      | S n' => (sum_f' f n' + (Z_of_nat (f n) # Pos.of_nat (10 ^ n)))%Q
    end.
 
  Axiom sum_f'_limit_r : forall (f : nat -> nat) (r : R) , limit (sum_f' f) r <-> (forall n : nat , Dec_R r n (f n)).
  
  Axiom sum_f'_limit_eps : forall (f : nat -> nat)(n m : nat) , (n <= m) % nat -> (Qabs(sum_f' f n - sum_f' f m) < 1%Z # Pos.of_nat (10^n))%Q.

  Lemma pow2_ge_pow10 : forall n : nat , (10 ^ n >= 2 ^ n)%nat.
  Proof.
    intros.
    induction n ; auto.
    replace (S n) with ((n + 1)%nat).
    - rewrite Nat.pow_add_r. rewrite Nat.pow_add_r.
      apply Nat.mul_le_mono ; auto.
      simpl. apply le_n_S. apply le_n_S. apply le_0_n.
    - apply Nat.add_1_r.
  Qed.

  Theorem TM'r'_is_computable3 : forall n : nat , CR3 (TM'r' n).
  Proof.
    intros.
    unfold CR3.
    exists (sum_f' (fun m => TM m n)).
    exists (fun eps => S (Pos.to_nat(Qden eps) / Z.to_nat (Qnum eps))).
    split.
    - rewrite sum_f'_limit_r.
      apply TM'r'_pro.
    - intros.
      rewrite sum_f'_limit_eps ; auto.
      apply Qle_lt_trans with (y := (1%Z # Pos.of_nat(2 ^ S (Pos.to_nat(Qden eps) / Z.to_nat (Qnum eps)))%nat)).
      + apply Qle_trans with (y := (1%Z # Pos.of_nat (2^n0))%Q).
        * unfold Qle. simpl.
          apply Pos2Z.pos_le_pos.
          apply Pos2Nat.inj_le.
          repeat rewrite Nat2Pos.id_max.
          destruct H0.
          pose proof Max_powSn_1 n0 H2.
          apply Nat.lt_le_incl in H3.
          pose proof max_r 1 (2 ^ n0) H3.
          pose proof le_trans 1 (2 ^ n0) (10^n0) H3 (pow2_ge_pow10 n0).
          pose proof max_r 1 (10 ^ n0) H5.
          rewrite H4,H6. apply pow2_ge_pow10.
        * unfold Qle. simpl.
          apply Pos2Z.pos_le_pos.
          apply Pos2Nat.inj_le.
          repeat rewrite Nat2Pos.id_max.
          destruct H0.
          pose proof Max_powSn_1 n0 H2.
          apply Nat.lt_le_incl in H3 as H4.
          pose proof max_r 1 (2 ^ n0) H4.
          rewrite H5.
          destruct H.
          pose proof ge_pow_ge n0.
          apply Nat.max_lub ; auto.
          replace ((2 ^ (Pos.to_nat (Qden eps) / Z.to_nat (Qnum eps)) +
 (2 ^ (Pos.to_nat (Qden eps) / Z.to_nat (Qnum eps)) + 0))%nat) 
          with ((2 ^ S (Pos.to_nat (Qden eps) / Z.to_nat (Qnum eps)))%nat) by reflexivity.
          apply Nat.pow_le_mono_r ; auto.
      + apply eps_lemma. auto.
  Qed.
  
  Theorem lim_CN3_NCN : (forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR3 (Un n)) -> CR3 l1) -> Halting.
  Proof.
    intros.
    apply limitTM'r'_pro1.
    intros.
    pose proof X TM'r' limitTM'r' limit_of_TM'r' TM'r'_is_computable3.
    clear X.
    unfold CR3 in *.
    destruct H as [f [N [? ?]]].
    assert (H' : (0 < 1 # Pos.of_nat (10 ^ n))%Q).
    {
      unfold Qlt. simpl. apply Z.lt_0_1.
    }
    pose proof H0 (1 # Pos.of_nat (10 ^ n))%Q H'.
    clear H' H0.
    remember (N (1 # Pos.of_nat (10 ^ n))) as n1.
    remember (S n1) as n0. remember (S n0) as m.
    pose proof H1 n0 m.
    clear H1.
    assert (H' : (n0 >= n1 /\ n0 >= 1)%nat).
    {
      split ; rewrite Heqn0.
      - apply le_S. apply le_n.
      - apply le_n_S. apply Nat.le_0_l.
    }
    assert (H'' : (m >= n0) % nat).
    {
      rewrite Heqm. apply le_S. apply le_n.
    }
    pose proof H0 H' H''.
    clear H0.
    pose proof limit_TM'r'_pro_pre _ _ _ _ H H1.
    destruct (Dec_Q (f n0) n).
    - rewrite H0 in d. auto.
    - rewrite H0 in n2.
      rewrite <- Dec_limitTM'r'_pro1 in n2. auto.
  Qed.
  
End Vir_R.


(** Module Uncomputable_function <: Vir_R.
  
End Uncomputable_function. *)


