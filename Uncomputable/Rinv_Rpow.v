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
  Parameter Rinv : {a0 : R | ~ a0 == R0} -> R.
  Parameter Rlt : R -> R -> Prop.
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
  Parameter Rpow : {a0 : R | ~ a0 == R0} -> nat -> R. 
  
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
  
  Parameter Rsinglefun : {X: R -> Prop | (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).

  Definition rinv (a : R) (H : ~ (a == R0)) : R.
    apply Rinv.
    exists a. apply H.
  Defined.

  Definition Rinv' (a : R): R.
    apply Rsinglefun.
    exists (fun b => (exists H: ~ (a == R0), (rinv a H) == b) \/
                     (a == R0 /\ b == R0)).
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
      + exists (rinv a H). left. exists H. auto. reflexivity.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto. symmetry. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Defined.

  Definition rpow (a : R) (H : ~ a == R0) : nat -> R.
    apply Rpow.
    exists a. apply H.
  Defined.

  Definition Rpow' (a : R) (z : nat) : R.
    apply Rsinglefun.
    exists (fun b => (exists H: ~ a == R0, (rpow a H z) == b) \/
                    (a == R0 /\ b == R0)).
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
      + exists (rpow a H z). left. exists H. auto. reflexivity.
    - split ; intros ; destruct H0.
      + destruct H0. left. exists x0. rewrite H0. auto.
      + right. split; try ( apply H0 ).
        rewrite <- H. apply H0.
      + destruct H0. left. exists x0. rewrite H0. auto. symmetry. auto.
      + right. split ; try ( apply H0).
        rewrite H. apply H0.
  Defined.
  
End Vir_R.