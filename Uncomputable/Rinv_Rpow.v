(** (single point set -> R) -> (Rinv : {a0 : R | a0 <> R0} -> R) -> (Rinv' : R -> R) *)
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
From CReal Require Import INQ_libs.
From CReal Require Import QArith_base_ext.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
Module Type Vir_R.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Req : R -> R -> Prop.
  Infix "==" := Req : R_scope.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv' : {a0 : R | ~ a0 == R0} -> R.
  Parameter Rlt : R -> R -> Prop.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  Infix "-" := Rminus : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Parameter Rpow' : {a0 : R | ~ a0 == R0} -> nat -> R. 
  
  Parameter Req_refl : forall x : R ,  x == x.
  
  Parameter Req_sym : forall x y : R , x == y -> y == x.

  Parameter Req_trans : forall x y z : R , x == y -> y == z -> x == z.
  
  Instance R_Setoid : Equivalence Req.
  Proof. 
    split; red.
    - apply Req_refl.
    - apply Req_sym.
    - apply Req_trans.
  Qed.
  
  Axiom Rmult_comp : Proper (Req==>Req==>Req) Rmult.
  Existing Instance Rmult_comp .
  
  Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
  Parameter Rsinglefun : {X: R -> Prop | P_singlefun X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).

  Definition If_fun (P : Prop) (x y : R) := (fun z => (P /\ x == z) \/ (~ P /\ y == z)).
  
  Theorem If_fun_single : forall (P : Prop)(x y : R), P_singlefun (If_fun P x y).
  Proof.
    intros. 
    repeat split ; intros.
    - destruct H , H0 , H , H0.
      + rewrite <- H1. auto.
      + exfalso. auto.
      + exfalso. auto.
      + rewrite <- H1. auto.
    - destruct (classic P).
      + exists x. hnf. left. split ; auto. reflexivity.
      + exists y. hnf. right. split ; auto. reflexivity.
    - hnf in *. rewrite H in H0. auto. 
    - hnf in *. rewrite H . auto.
  Qed.
  
  Instance If_fun_comp : Proper (eq(A:=Prop) ==> Req ==> Req ==> Req ==> iff) If_fun.
  Proof.
    hnf ; red ; intros ; hnf ; red ; intros.
    split ; intros ; hnf in * ; rewrite H , H0 , H1 , H2 in *; auto.
  Qed.
  
  Definition Rif (P : Prop)(x y  : R) : R.
    apply Rsinglefun. 
    exists (If_fun P x y).
    apply If_fun_single.
  Defined.
  
  Instance Rif_comp : Proper (eq(A:=Prop) ==> Req ==> Req ==> Req) Rif.
  Proof.
    hnf ; red ; intros ; hnf ; intros.
    unfold Rif.
    pose proof If_fun_single x x0 x1.
    pose proof If_fun_single y y0 y1.
    assert (If_fun x x0 x1 = If_fun y y0 y1).
    { rewrite H. apply functional_extensionality_dep.
      intros. apply propositional_extensionality.
      rewrite H0 , H1. reflexivity.
    }
    subst.
    pose proof Rsinglefun_correct (If_fun y x0 x1) H2.
    pose proof Rsinglefun_correct (If_fun y y0 y1) H3.
    assert (H3 = If_fun_single y y0 y1). { apply proof_irrelevance. }
    assert (H2 = If_fun_single y x0 x1). { apply proof_irrelevance. }
    rewrite H6 , H7 in *. clear H6 H7.
    destruct H , H5 , H , H5.
    - rewrite <- H7. rewrite <- H6. auto.
    - exfalso. auto.
    - exfalso. auto.
    - rewrite <- H7. rewrite <- H6. auto.
  Qed.
  
  Theorem Rif_left : forall (P:Prop) (x y:R), P -> Rif P x y == x.
  Proof.
    intros. unfold Rif. 
    pose proof If_fun_single P x y.
    pose proof Rsinglefun_correct (If_fun P x y) H0.
    assert (H0 = If_fun_single P x y).
    { apply proof_irrelevance. }
    subst.
    destruct H1 , H0.
    - rewrite <- H1. reflexivity.
    - exfalso. auto.
  Qed.
  
  Theorem Rif_right : forall (P:Prop) (x y:R), ~ P -> Rif P x y == y.
  Proof.
    intros. unfold Rif. 
    pose proof If_fun_single P x y.
    pose proof Rsinglefun_correct (If_fun P x y) H0.
    assert (H0 = If_fun_single P x y).
    { apply proof_irrelevance. }
    subst.
    destruct H1 , H0.
    - exfalso. auto.
    - rewrite <- H1. reflexivity.
  Qed. 

  Definition rinv' (a : R) (H : ~ (a == R0)) : R.
    apply Rinv'.
    exists a. apply H.
  Defined.
  
  Parameter Rinv'_pro1 : forall (r1 r2 : R)(H1 : ~ r1 == R0) (H2 : ~r2 == R0), r1 == r2 -> rinv' r1 H1 == rinv' r2 H2.
  
  Parameter Rinv'_pro2 : forall (r : R)(H : ~ r == R0), rinv' r H * r == R1.

  Theorem Lemma_Rinv : forall a : R , P_singlefun (fun b : R => (exists H : ~ a == R0, rinv' a H == b) \/ a == R0 /\ b == R0).
  Proof.
    intros.
    split; [| split].
    - intros.
      destruct H. 
      + destruct H. rewrite <- H. symmetry. destruct H0.  
        * destruct H0. rewrite <- H0.
          assert (x = x0). { apply proof_irrelevance. }
          subst x ; auto. reflexivity.
        * exfalso. apply x. apply H0.
      + destruct H0.
        * destruct H0. exfalso. apply x. apply H.
        * destruct H. destruct H0. rewrite H1. rewrite H2. reflexivity. 
    - pose proof (classic (a == R0)).
      destruct H.
      + exists R0. right. split ; auto. reflexivity.
      + exists (rinv' a H). left. exists H. auto. reflexivity.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto. symmetry. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Qed.
  
  Definition Rinv (a : R): R.
    apply Rsinglefun.
    exists (fun b => (exists H: ~ (a == R0), (rinv' a H) == b) \/
                     (a == R0 /\ b == R0)).
    apply Lemma_Rinv.
  Defined.

  Theorem Rinv_1 : forall r : R , r == R0 -> Rinv r == R0.
  Proof.
    intros.
    unfold Rinv.
    pose proof (Lemma_Rinv r).
    pose proof (Rsinglefun_correct (fun b : R => 
      (exists H0 : ~ r == R0, rinv' r H0 == b) \/ r == R0 /\ b == R0) H0).
    assert (H0 = (Lemma_Rinv r)).
    { apply proof_irrelevance. }
    subst.
    destruct H1,H0.
    - exfalso. auto.
    - rewrite H1. reflexivity. 
  Qed.
  
  Theorem Rinv_Rinv' : forall r : R , ~ r == R0 -> exists H: ~ r == R0, Rinv r == (rinv' r H).
  Proof.
    intros.
    unfold Rinv.
    pose proof (Lemma_Rinv r).
    pose proof (Rsinglefun_correct (fun b : R => 
      (exists H0 : ~ r == R0, rinv' r H0 == b) \/ r == R0 /\ b == R0) H0).
    assert (H0 = (Lemma_Rinv r)).
    { apply proof_irrelevance. }
    subst.
    destruct H1,H0.
    - exists x. rewrite H0. reflexivity.
    - exfalso. auto.
  Qed.
  
  Theorem Rinv_correct1 : forall r1 r2 : R , r1 == r2 -> Rinv r1 == Rinv r2.
  Proof.
    intros.
    destruct (classic (r1 == R0)).
    - rewrite H0 in H.
      symmetry in H.
      apply Rinv_1 in H.
      apply Rinv_1 in H0.
      rewrite H , H0. reflexivity.
    - destruct (classic (r2 == R0)).
      + exfalso. apply H0. rewrite H. auto.
      + apply Rinv_Rinv' in H0.
        apply Rinv_Rinv' in H1.
        destruct H0,H1.
        rewrite H0 , H1.
        apply Rinv'_pro1;  auto.
  Qed.
  
  Theorem Rinv_correct2 : forall r : R , ~ r == R0 -> Rinv r * r == R1.
  Proof.
    intros.
    apply Rinv_Rinv' in H.
    destruct H.
    rewrite H.
    apply Rinv'_pro2.
  Qed.
  
  Definition rpow' (a : R) (H : ~ a == R0) : nat -> R.
    apply Rpow'.
    exists a. apply H.
  Defined.

  Parameter Rpow'_pro : forall (r1 r2 : R)(H1 : ~ r1 == R0) (H2 : ~r2 == R0)(z1 z2 : nat), 
    r1 == r2 -> z1 = z2 -> rpow' r1 H1 z1 == rpow' r2 H2 z2.

  Theorem Lemma_Rpow : forall (a:R) (z : nat), P_singlefun (fun b : R => (exists H : ~ a == R0, rpow' a H z == b) \/ a == R0 /\ b == R0).
  Proof.
    intros.
    split; [| split].
    - intros.
      destruct H. 
      + destruct H. rewrite <- H. symmetry. destruct H0.  
        * destruct H0. rewrite <- H0.
          assert (x = x0). { apply proof_irrelevance. }
          subst; auto. reflexivity.
        * exfalso. apply x. apply H0.
      + destruct H0.
        * destruct H0. exfalso. apply x. apply H.
        * destruct H. destruct H0. rewrite H1. symmetry. auto. 
    - pose proof (classic (a == R0)).
      destruct H.
      + exists R0. right. split ; auto. reflexivity.
      + exists (rpow' a H z). left. exists H. auto. reflexivity.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto. symmetry. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Qed.
  
  Definition Rpow (a : R) (z : nat) : R.
    apply Rsinglefun.
    exists (fun b => (exists H: ~ a == R0, (rpow' a H z) == b) \/
                    (a == R0 /\ b == R0)).
    apply Lemma_Rpow.
  Defined.
  
  Theorem Rpow_1 : forall (r : R)(z:nat) , r == R0 -> Rpow r z == R0.
  Proof.
    intros.
    unfold Rpow.
    pose proof (Lemma_Rpow r z).
    pose proof (Rsinglefun_correct (fun b : R => 
      (exists H1 : ~ r == R0, rpow' r H1 z == b) \/ r == R0 /\ b == R0) H0).
    assert (H0 = (Lemma_Rpow r z)).
    { apply proof_irrelevance. }
    subst.
    destruct H1,H0.
    - exfalso. auto.
    - rewrite H1. reflexivity. 
  Qed.
  
  Theorem Rpow_Rpow' : forall (r : R)(z:nat) , ~ r == R0 -> exists H: ~ r == R0, Rpow r z == (rpow' r H z).
  Proof.
    intros.
    unfold Rpow.
    pose proof (Lemma_Rpow r z).
    pose proof (Rsinglefun_correct (fun b : R => 
      (exists H1 : ~ r == R0, rpow' r H1 z == b) \/ r == R0 /\ b == R0) H0).
    assert (H0 = (Lemma_Rpow r z)).
    { apply proof_irrelevance. }
    subst.
    destruct H1,H0.
    - exists x. rewrite H0. reflexivity.
    - exfalso. auto.
  Qed.
  
  Theorem Rpow_correct : forall (r1 r2 : R)(z1 z2 : nat) , r1 == r2 -> z1 = z2 -> Rpow r1 z1 == Rpow r2 z2.
  Proof.
    intros. subst.
    destruct (classic (r1 == R0)).
    - rewrite H0 in H.
      symmetry in H.
      apply (Rpow_1 _ z2) in H.
      apply (Rpow_1 _ z2) in H0.
      rewrite H , H0. reflexivity.
    - destruct (classic (r2 == R0)).
      + exfalso. apply H0. rewrite H. auto.
      + apply (Rpow_Rpow' _ z2) in H0.
        apply (Rpow_Rpow' _ z2) in H1.
        destruct H0,H1.
        rewrite H0 , H1.
        apply Rpow'_pro;  auto.
  Qed.

End Vir_R.