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
  (** Add Real_equiv and Proper.   -- Qinxiang *)
End Vir_Real.


Parameter TM : nat -> nat -> Prop.
Definition Halting : Type := forall (i j : nat), {TM i j} + {~(TM i j)}.
Axiom Turing_proper1 : forall (i j k: nat), (j <= k)%nat -> TM i j -> TM i k.
Axiom Turing_proper2 : forall (i j k: nat), (k <= j)%nat -> ~ (TM i j) -> ~ (TM i k).
(** 2 can be proved from 1.     -- Qinxiang *)

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

Module Uncomputable_function.
  Parameter Rinv : {a0 : R | ~(a0 = 0)%R} -> R.
  Parameter Rpow : {a0 : R | ~(a0 = 0)%R} -> nat -> R. 
  Parameter CR : R -> Prop.
  Theorem Three_dimensions : (forall r1 r2 : R, ({r1 = r2} + {r1 <> r2})%R) -> Halting.
  Proof. Admitted.
  (** This theorem also proves the uncomputability of Rmax Rmin Rabs Rdist*)
  (** Rmax Rmin Rabs Rdist are actually computable. Defined in an incorrect way in std. -- Qinxiang *)
  (** Derive other two_dimensions and three dimensions from it. -- Qinxiang *)
  Theorem Rinv_def : (forall (Rinv' : R -> R)(r: R) (H : r <> 0%R) ,Rinv' r = Rinv (exist _ r H) ) -> Halting.
  Proof. Admitted.
  Theorem Rpow_def : (forall (Rpow' : R -> nat -> R)(r: R)(H : r <> 0%R) ,Rpow' r 0%nat = Rpow (exist _ r H) 0%nat ) -> Halting.
  Proof. Admitted.
  (** This theorem also proves the problem in the definition of powRZ *)
  Theorem Up_R : (forall (r : R)(z : Z), up r = z) -> Halting.
  Proof. Admitted.
  (** This theorem also proves the uncomputability of Int_part frac_part *)
  Theorem lim_CN_NCN :forall (Un:nat -> R) (l1:R), Un_cv Un l1 -> (forall n : nat ,CR (Un n)) -> ~ CR l1.
  Proof. Admitted.
  
End Uncomputable_function.


