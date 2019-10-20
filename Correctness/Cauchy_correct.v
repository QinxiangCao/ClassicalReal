Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Field.
From Coq Require Import Omega.
From Coq Require Import Psatz.
From CReal Require Import Cauchy.RBase.
From CReal Require Import Cauchy.RArith.
From CReal Require Import Cauchy.ROrder.
From CReal Require Import Uncomputable.Countable.
From CReal Require Import Uncomputable.ComRealBase.
From Coq Require Import PArith.BinPosDef.

Module CauchyR : VIR_R.
  Definition R := Real.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Definition R0 := Rzero.
  Definition R1 := Rone.
  Definition Rplus := Rplus.
  Definition Rmult := Rmult.
  Definition Ropp := Ropp.
  Parameter Rinv : R -> R.
  Definition Rlt := Rlt.
  Definition Req := Real_equiv.
  Infix "==" := Req : R_scope.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  
  Definition Rle (r1 r2:R) : Prop := Rlt r1 r2 \/ r1 ==r2.
  
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 == r2.
  
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  
  Definition Rdiv (r1 r2 :R) : R := r1 * Rinv r2.
  
  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Notation "0" := R0 : R_scope.
  Notation "1" := R1 : R_scope.
  Notation "2" := (1+1) : R_scope.
  
  Definition Req_refl := Real_def_refl.
  
  Definition Req_sym := Real_def_symm.

  Definition Req_trans := Real_def_trans.
  
  Definition R_Setoid := Real_equiv_holds.
  
  Definition Rplus_comp := Rplus_comp.
 
  Definition Ropp_comp := Ropp_comp.
  
  Definition Rmult_comp := Rmult_comp.
  
  Axiom Rinv_comp : Proper (Req==>Req) Rinv.
  Existing Instance Rinv_comp .
  
  Instance Rle_comp : Proper (Req==>Req==>iff) Rle.
  Proof.
    split.
    - intros.
      destruct H1.
      + left. rewrite <- H , <- H0. auto.
      + right. rewrite <- H , <- H0. auto.
    - intros.
      destruct H1.
      + left. rewrite H, H0. auto.
      + right. rewrite H ,H0. auto. 
  Qed.
  
  Definition Rlt_comp := Rlt_comp.
  
  Instance Rminus_comp : Proper (Req==>Req==>Req) Rminus.
  Proof. hnf ; red ; intros. unfold Rminus. rewrite H , H0. reflexivity. Qed.
  
  Instance Rdiv_comp : Proper (Req==>Req==>Req) Rdiv.
  Proof. hnf ; red ; intros. unfold Rdiv. rewrite H , H0. reflexivity. Qed.
  
  Instance Rgt_comp : Proper (Req==>Req==>iff) Rgt.
  Proof. hnf ; red ; intros. unfold Rgt. rewrite H , H0. reflexivity. Qed.
  
  Instance Rge_comp : Proper (Req==>Req==>iff) Rge.
  Proof. hnf ; red ; intros. unfold Rge. rewrite H , H0. reflexivity. Qed.
  
  (* Complementary definition of Real Equivalence. *)
  Fixpoint pow (r:R) (n:nat) : R :=
    match n with
      | O => 1
      | S n => Rmult r (pow r n)
    end.
    
  
  Instance Rpow_comp : Proper (Req ==> eq ==> Req) pow.
  Proof. 
    hnf ; red; intros. subst.
    induction y0.
    - reflexivity.
    - simpl. rewrite IHy0. rewrite H. reflexivity.
  Qed.
  
  (* Definition copied from Rpow_def.v *)
  
  Fixpoint IPR_2 (p:positive) : R :=
    match p with
    | xH => R1 + R1
    | xO p => (R1 + R1) * IPR_2 p
    | xI p => (R1 + R1) * (R1 + IPR_2 p)
    end.

  Definition IPR (p:positive) : R :=
    match p with
    | xH => R1
    | xO p => IPR_2 p
    | xI p => R1 + IPR_2 p
    end.
  Arguments IPR p%positive : simpl never.

  (**********)
  Definition IZR (z:Z) : R :=
    match z with
    | Z0 => R0
    | Zpos n => IPR n
    | Zneg n => - IPR n
    end.
  Arguments IZR z%Z : simpl never.
  
  (* Definitions copied from Rdefinitions.v *)
  
  Fixpoint INR (n:nat) : R :=
    match n with
    | O => 0
    | S O => 1
    | S n => INR n + 1
    end.
  Arguments INR n%nat.
  
  (* Definition copied from Raxioms.v *)
  
  Definition IQR(q : Q) : R :=
    match q with
    | p # q => IZR p / IPR q
    end.
  Arguments IQR q%Q.
  
  Definition Rplus_comm := Rplus_comm.
  
  Definition Rplus_assoc := Rplus_assoc.
  
  Definition Rplus_opp_r := Rplus_opp_r.
  
  Definition Rplus_0_l := Rplus_0_l.
  
  Definition Rmult_comm := Rmult_comm.
  
  Definition Rmult_assoc := Rmult_assoc.
  
  Theorem Rinv_l : forall r:R, ~ r == 0 -> Rinv r * r == 1.
  Proof.
  Admitted.
  
  Definition Rmult_1_l := Rmult_1_l.
  
  Lemma R1_neq_R0 : ~ 1 == 0.
  Proof.
    intro. hnf in H.
    specialize (H (1 # 2)).
    assert (0 < 1 # 2)%Q. { lra. }
    specialize (H H0).
    destruct H. 
    assert (S x > x)%nat. { omega. }
    specialize (H (S x) H1 1%Q 0%Q).
    simpl in H.
    assert (~ (1 < 1 # 2))%Q. {lra. }
    apply H2. apply H ; lra.
  Qed.
  
  Theorem Rmult_plus_distr_l : 
    forall r1 r2 r3 : R, r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
  Proof.
    intros.
    rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    rewrite ! (Rmult_comm r1).
    reflexivity.
  Qed.
  
  Theorem total_order_T : forall r1 r2 : R, r1 < r2 \/ r1 == r2 \/ r2 < r1.
  Proof.
    intros.
    destruct (classic (r1 < r2)) ; auto.
    apply Rnot_lt in H.
    auto.
  Qed.
  
  Theorem Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Proof.
    intros. intro.
    apply (Rlt_irrefl r1).
    apply Rlt_trans with r2 ; auto.
  Qed.
  
  Definition Rlt_trans := Rlt_trans.
  
  Theorem Rplus_lt_compat_l : 
    forall r r1 r2 : R, r1 < r2 -> (r + r1)%R < (r + r2)%R.
  Proof.
    intros.
    rewrite ! (Rplus_comm r).
    apply Rlt_plus_r. auto.
  Qed.
  
  Theorem Rmult_lt_compat_l : 
     forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  Proof.
    intros.
    rewrite !(Rmult_comm r).
    apply Rlt_mult_r with (C := r) ; auto.
    apply Rpositive_gt_0. auto.
  Qed.
  
  Axiom archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.

  Definition upper_bound (X : nat -> R -> Prop) (U : R) : Prop := forall (n : nat)(q : R) , X n q -> q <= U.
  Definition Sup (X : nat -> R -> Prop) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.

  Axiom upper_bound_exists_Sup : forall (X : nat -> R -> Prop) , is_function eq Req X -> (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).
End CauchyR.
