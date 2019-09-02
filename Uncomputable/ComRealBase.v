(** Uncomputablity in the definition of R function **)
(** For convenience's sake, we focus on Vir_real numbers in [0,1] **) 
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
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Classes.RelationClasses.
Require Import Ring.
From Coq Require Import Field.
From Coq Require Import Omega.
From Coq Require Import Psatz.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.
From CReal Require Import Countable.
From CReal Require Import QArith_base_ext.

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
  Parameter Rabs : R -> R.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
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
  Definition Reqb (x y : R) : Prop := x = y.
  
  Notation "0" := R0 : R_scope.
  Notation "1" := R1 : R_scope.
  Notation "2" := (1+1) : R_scope.
  Notation "-1" := (- 1%R) : R_scope.
  
  Fixpoint pow (r:R) (n:nat) : R :=
    match n with
      | O => 1
      | S n => Rmult r (pow r n)
    end.
    
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
  
  Fixpoint INR (n:nat) : R :=
    match n with
    | O => 0
    | S O => 1
    | S n => INR n + 1
    end.
  Arguments INR n%nat.
  
  Definition IQR(q : Q) : R :=
    match q with
    | p # q => IZR p / IPR q
    end.
  Arguments IQR q%Q.
  (** Definition of Vir_R *)
  Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
  Hint Resolve Rplus_comm: Vir_real.
  Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
  Hint Resolve Rplus_assoc: Vir_real.
  Axiom Rplus_opp_r : forall r:R, r + - r = 0.
  Hint Resolve Rplus_opp_r: Vir_real.
  Axiom Rplus_0_l : forall r:R, 0 + r = r.
  Hint Resolve Rplus_0_l: Vir_real.
  Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
  Hint Resolve Rmult_comm: Vir_real.
  Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
  Hint Resolve Rmult_assoc: Vir_real.
  Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
  Hint Resolve Rinv_l: Vir_real.
  Axiom Rmult_1_l : forall r:R, 1 * r = r.
  Hint Resolve Rmult_1_l: Vir_real.
  Axiom R1_neq_R0 : 1 <> 0.
  Hint Resolve R1_neq_R0: Vir_real.

  Axiom
    Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
  Hint Resolve Rmult_plus_distr_l: Vir_real.

  Axiom total_order_T : forall r1 r2:R, r1 < r2 \/ r1 = r2 \/ r1 > r2.
  Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
  Axiom
    Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: Vir_real.
  
  Parameter Rabs_tri : forall a b c : R , Rabs(a - b) < c <-> a < b + c /\ a > b - c.
  Parameter Rabs_comm : forall a b : R , Rabs (a - b) = Rabs (b - a).
  
  Axiom archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.

  Definition upper_bound (X : nat -> R -> Prop) (U : R) : Prop := forall (n : nat)(q : R) , X n q -> q <= U.
  Definition Sup (X : nat -> R -> Prop) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.

  Axiom upper_bound_exists_Sup : forall (X : nat -> R -> Prop) , is_function X -> (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).
 
  Axiom Rabs_pos : forall r1 : R , (r1 >= R0) -> Rabs r1 = r1.
  Axiom Rabs_neg : forall r1 : R , (r1 <= R0) -> Rabs r1 = - r1.
  Axiom Rlt_mid : forall r r1 : R , r < r1 -> exists eps : Q , (eps > 0)%Q /\ r + IQR eps < r1 - IQR eps.
  Hint Resolve Rabs_pos Rabs_neg Rlt_mid: Vir_real.
  (** Axioms of Vir_R *)

End VIR_R.

Module Type VIR_R_EXTRA (VirR: VIR_R).
  Import VirR.
  Parameter Rsinglefun : {X: R -> Prop | (forall x1 x2, X x1 -> X x2 -> x1 = x2)
         /\ (exists x, X x) /\ Proper (Reqb ==> iff) X} -> R.
  Axiom Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
End VIR_R_EXTRA.
