(* Uncomputablity in the definition of R function *)
(* For convenience's sake, we focus on real numbers in [0,1] *) 
(* All definitions are copied from Coq standard library Rdefinitions.v Rpow_def.v Raxioms.v*)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Classes.Equivalence.
From Coq Require Export ZArith.ZArith_base.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import setoid_ring.Ring_theory.
From Coq Require Import setoid_ring.Ring.
From Coq Require Import setoid_ring.Field.
From Coq Require Import omega.Omega.
From Coq Require Import micromega.Psatz.
Import ListNotations.
From CReal Require Import Countable.
From CReal Require Import QArith_base_ext.
From CReal Require Import Uncomputable.SingleLemmas.

Module Type VIR_R.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv : R -> R.
  Parameter Rlt : R -> R -> Prop.
  Parameter Req : R -> R -> Prop.
  
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
  
  Definition Rdiv (r1 r2 :R) : R := r1 * / r2.
  
  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
  Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
  Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
  Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.
  Notation "0" := R0 : R_scope.
  Notation "1" := R1 : R_scope.
  Notation "2" := (1+1) : R_scope.
  
  (* Definitions copied from Rdefinitions.v *)
  (* Delete the definition of up *)
  
  Parameter Req_refl : forall x : R ,  x == x.
  
  Parameter Req_sym : forall x y : R , x == y -> y == x.

  Parameter Req_trans : forall x y z : R , x == y -> y == z -> x == z.

  Hint Immediate Req_sym : real.
  Hint Resolve Req_refl Req_trans : real.

  Instance R_Setoid : Equivalence Req.
  Proof. split; red; eauto with real. Qed.
  
  Axiom Rplus_comp : Proper (Req==>Req==>Req) Rplus.
  Existing Instance Rplus_comp .
  
  Axiom Ropp_comp : Proper (Req==>Req) Ropp.
  Existing Instance Ropp_comp .
  
  Axiom Rmult_comp : Proper (Req==>Req==>Req) Rmult.
  Existing Instance Rmult_comp .
  
  Axiom Rinv_comp : Proper (Req==>Req) Rinv.
  Existing Instance Rinv_comp .
  
  Axiom Rle_comp : Proper (Req==>Req==>iff) Rle.
  Existing Instance Rle_comp .
  
  Axiom Rlt_comp : Proper (Req==>Req==>iff) Rlt.
  Existing Instance Rlt_comp .
  
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
    hnf ; red; intros. rewrite H0. clear H0.
    induction y0.
    - simpl. reflexivity.
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
 
  (* Complementary definition of Injection from Q to R. *)
  
  (* Definition of Vir_R *)
  
  Axiom Rplus_comm : forall r1 r2:R, r1 + r2 == r2 + r1.
  Hint Resolve Rplus_comm: real.
  Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 == r1 + (r2 + r3).
  Hint Resolve Rplus_assoc: real.
  Axiom Rplus_opp_r : forall r:R, r + - r == 0.
  Hint Resolve Rplus_opp_r: real.
  Axiom Rplus_0_l : forall r:R, 0 + r == r.
  Hint Resolve Rplus_0_l: real.
  Axiom Rmult_comm : forall r1 r2:R, r1 * r2 == r2 * r1.
  Hint Resolve Rmult_comm: real.
  Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 == r1 * (r2 * r3).
  Hint Resolve Rmult_assoc: real.
  Axiom Rinv_l : forall r:R, ~ r == 0 -> / r * r == 1.
  Hint Resolve Rinv_l: real.
  Axiom Rmult_1_l : forall r:R, 1 * r == r.
  Hint Resolve Rmult_1_l: real.
  Axiom
    Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) == r1 * r2 + r1 * r3.
  Hint Resolve Rmult_plus_distr_l: real.

  Axiom total_order_T : forall r1 r2:R, r1 < r2 \/ r1 == r2 \/ r1 > r2.
  Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Axiom R1_gt_R0 : 0 < 1.
  Hint Resolve R1_gt_R0: real.
  
  Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
  Axiom
    Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: real.
  (* Axioms copied from Raxioms.v *)
  (* Change { | } -> exists , sumbool to or *)
  (* Change eq -> Req *)
  
  (* Axioms of Vir_R *)
End VIR_R.

Module Type VIR_R_COMPLETE (VirR : VIR_R).
  Import VirR.
  Local Open Scope R_scope.
  Axiom archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.

  Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

  Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.

  Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

  Axiom
  completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> exists m:R , is_lub E m .
 
  (* Completeness axioms copied from Raxioms.v *)
  (* Change { | } -> exists , sumbool to or *)
End VIR_R_COMPLETE.

Module Type VIR_R_SINGLETON (VirR : VIR_R).
  Import VirR.
  Local Open Scope R_scope.
  Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
  Parameter Rsinglefun : {X: R -> Prop | P_singlefun X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
End VIR_R_SINGLETON.

Module VirRSingletonLemmas (VirR: VIR_R) (VirRSingleton: VIR_R_SINGLETON VirR).
  Import VirR.
  Import VirRSingleton.
  Local Open Scope R_scope.

  Module RSS <: R_SINGLE_SIMPLE.
    Definition R := VirR.R.
    Definition Req := VirR.Req.
    Definition R_Setoid := VirR.R_Setoid.
    Definition P_singlefun := VirRSingleton.P_singlefun.
    Definition Rsinglefun := VirRSingleton.Rsinglefun.
    Definition Rsinglefun_correct  := VirRSingleton.Rsinglefun_correct.
  End RSS.

  Module RL := RSignleLemmas RSS.
  
  Definition Rif: Prop -> R -> R -> R := RL.Rif. 
  
  Instance Rif_comp : Proper (eq(A:=Prop) ==> Req ==> Req ==> Req) Rif :=
    RL.Rif_comp.
  
  Definition Rif_left : forall (P:Prop) (x y:R), P -> Rif P x y == x :=
    RL.Rif_left.
  
  Definition Rif_right : forall (P:Prop) (x y:R), ~ P -> Rif P x y == y :=
    RL.Rif_right.
  
  Definition Rif_rich: forall (P : Prop), (P -> R) -> (~ P -> R) -> R :=
    RL.Rif_rich.

  Definition Rif_rich_left:
    forall (P:Prop) x y, P -> exists H : P,Rif_rich P x y == x H
  := RL.Rif_rich_left.
  
  Definition Rif_rich_right:
    forall (P:Prop) x y, ~ P -> exists H : ~ P,Rif_rich P x y == y H
  := RL.Rif_rich_right.
End VirRSingletonLemmas.

Module Type VIR_R_ALL.

Include VIR_R.
Include VIR_R_SINGLETON.
Include VIR_R_COMPLETE.

End VIR_R_ALL.
