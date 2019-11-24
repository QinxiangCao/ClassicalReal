Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Export ZArith_base.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Classes.Equivalence.
From Coq Require Import setoid_ring.Ring_theory.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import setoid_ring.Ring.
From Coq Require Import setoid_ring.Field.
From Coq Require Import omega.Omega.
From Coq Require Import micromega.Psatz.
From Coq Require Import Logic.ProofIrrelevance.
Import ListNotations.
From CReal Require Import Countable.
From CReal Require Import QArith_base_ext.

Module Type R_SINGLE_SIMPLE.
  Parameter Inline R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter Inline Req : R -> R -> Prop.
  
  Axiom R_Setoid : Equivalence Req.
  Existing Instance R_Setoid .

  Infix "==" := Req : R_scope.
  
  Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
  Parameter Inline Rsinglefun : {X: R -> Prop | P_singlefun X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
 
End R_SINGLE_SIMPLE.

Module RSignleLemmas (RSS : R_SINGLE_SIMPLE).
  Import RSS.
  Local Open Scope R_scope.
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
    assert (If_fun P x y x). {
      hnf; left.
      split; auto.
      reflexivity.
    }
    pose proof If_fun_single P x y.
    pose proof Rsinglefun_correct (If_fun P x y) (If_fun_single P x y).
    pose proof proj1 H1.
    apply H3; auto.
  Qed.
  
  Theorem Rif_right : forall (P:Prop) (x y:R), ~ P -> Rif P x y == y.
  Proof.
    intros. unfold Rif.
    assert (If_fun P x y y). {
      hnf; right.
      split; auto.
      reflexivity.
    }
    pose proof If_fun_single P x y.
    pose proof Rsinglefun_correct (If_fun P x y) (If_fun_single P x y).
    pose proof proj1 H1.
    apply H3; auto.
  Qed.
  
  Definition If_fun_rich (P : Prop) (x : P -> R) (y : ~ P -> R) := 
    (fun z => (exists H : P , x H == z) \/ (exists H : ~ P , y H == z)).
  
  Theorem If_fun_single_rich : forall (P : Prop) x y ,
    Proper ((fun _ _ => True) ==> Req) x ->
    Proper ((fun _ _ => True) ==> Req) y ->
    P_singlefun (If_fun_rich P x y).
  Proof.
    intros P x y Px Py.
    repeat split ; intros.
    - destruct H , H0 , H , H0.
      + pose proof Px x0 x3 I. rewrite <- H, H1, H0. reflexivity.
      + exfalso. auto.
      + exfalso. auto.
      + pose proof Py x0 x3 I. rewrite <- H, H1, H0. reflexivity.
    - destruct (classic P).
      + exists (x H). hnf. left.
        exists H. reflexivity.
      + exists (y H). hnf. right.
        exists H. reflexivity.
    - hnf in *. destruct H0 , H0 ; rewrite H in H0.
      + left. exists x1. auto.
      + right. exists x1. auto. 
    - hnf in *. destruct H0 , H0 ; rewrite <- H in H0.
      + left. exists x1. auto.
      + right. exists x1. auto.
  Qed. 
 
  Definition Rif_rich (P : Prop)(x : P -> R)(y : ~ P -> R)
                      {_: Proper ((fun _ _ => True) ==> Req) x}
                      {_: Proper ((fun _ _ => True) ==> Req) y}: R.
    apply Rsinglefun. 
    exists (If_fun_rich P x y).
    apply If_fun_single_rich; auto.
  Defined.

  Theorem Rif_rich_left : forall (P:Prop) x y
    {Px: Proper ((fun _ _ => True) ==> Req) x}
    {Py: Proper ((fun _ _ => True) ==> Req) y},
    P -> exists H : P,Rif_rich P x y == x H.
  Proof.
    intros. unfold Rif_rich. 
    assert (If_fun_rich P x y (x H)). {
      hnf; left.
      eexists; reflexivity.
    }
    pose proof If_fun_single_rich P x y _ _.
    pose proof Rsinglefun_correct (If_fun_rich P x y) (If_fun_single_rich P x y _ _).
    pose proof proj1 H1.
    exists H.
    apply H3; auto.
  Qed.
  
  Theorem Rif_rich_right : forall (P:Prop) x y
    {Px: Proper ((fun _ _ => True) ==> Req) x}
    {Py: Proper ((fun _ _ => True) ==> Req) y},
    ~ P -> exists H : ~ P,Rif_rich P x y == y H.
  Proof.
    intros. unfold Rif_rich. 
    assert (If_fun_rich P x y (y H)). {
      hnf; right.
      eexists; reflexivity.
    }
    pose proof If_fun_single_rich P x y _ _.
    pose proof Rsinglefun_correct (If_fun_rich P x y) (If_fun_single_rich P x y _ _).
    pose proof proj1 H1.
    exists H.
    apply H3; auto.
  Qed.
  
End RSignleLemmas.

Module Type RINV_PARTIAL (RSS : R_SINGLE_SIMPLE).
  Module RL := RSignleLemmas (RSS).
  Import RL RSS.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rmult : R -> R -> R.
  Infix "*" := Rmult : R_scope.
  Axiom Rmult_comp : Proper (Req==>Req==>Req) Rmult.
  Existing Instance Rmult_comp .
  Parameter Rinv': forall (a : R) (H : ~ (a == R0)), R.
  Parameter Rinv'_comp : forall (r1 r2 : R)(H1 : ~ r1 == R0) (H2 : ~r2 == R0), r1 == r2 -> Rinv' r1 H1 == Rinv' r2 H2.
  Parameter Rinv'_l : forall (r : R)(H : ~ r == R0), Rinv' r H * r == R1.
End RINV_PARTIAL.


Module Rinv_Partial_To_Total (RSS : R_SINGLE_SIMPLE) (RP : RINV_PARTIAL RSS).
  Module RSL := RSignleLemmas (RSS).
  Import RP RSS RSL.
  Local Open Scope R_scope.
  Local Instance RinvL' (a: R):
    Proper ((fun _ _ : a == R0 => True) ==> Req) (fun _ : a == R0 => R0).
  Proof. hnf; intros. reflexivity. Qed.

  Local Instance RinvR' (a: R):
    Proper ((fun _ _ : ~ a == R0 => True) ==> Req) (fun H : ~ a == R0 => Rinv' a H).
  Proof. hnf; intros. apply Rinv'_comp. reflexivity. Qed.

  Program Definition Rinv (a : R): R :=
    Rif_rich (a == R0) (fun _ => R0) (fun H => Rinv' a H).

  Theorem Rinv_1 : forall r : R , r == R0 -> Rinv r == R0.
  Proof.
    intros.
    unfold Rinv.
    pose proof (Rif_rich_left (r==R0) (fun _ : r == R0 => R0) (fun H0 : ~ r == R0 => Rinv' r H0) H).
    destruct H0.
    auto.
  Qed.
  
  Theorem Rinv_Rinv' : forall r : R , ~ r == R0 -> exists H: ~ r == R0, Rinv r == (Rinv' r H).
  Proof.
    intros.
    unfold Rinv.
    pose proof (Rif_rich_right (r==R0) (fun _ : r == R0 => R0) (fun H0 : ~ r == R0 => Rinv' r H0)) H.
    destruct H0.
    auto.
    exists x. auto.
  Qed.
  
  Theorem Rinv_comp : Proper (Req ==> Req) Rinv.
  Proof.
    hnf. intros.
    intros.
    destruct (classic (x == R0)).
    - rewrite H0 in H.
      symmetry in H.
      apply Rinv_1 in H.
      apply Rinv_1 in H0.
      rewrite H , H0. reflexivity.
    - destruct (classic (y == R0)).
      + exfalso. apply H0. rewrite H. auto.
      + apply Rinv_Rinv' in H0.
        apply Rinv_Rinv' in H1.
        destruct H0,H1.
        rewrite H0 , H1.
        apply Rinv'_comp;  auto.
  Qed.
  
  Theorem Rinv_l : forall r : R , ~ r == R0 -> Rinv r * r == R1.
  Proof.
    intros.
    apply Rinv_Rinv' in H.
    destruct H.
    rewrite H.
    apply Rinv'_l.
  Qed.
End Rinv_Partial_To_Total.
