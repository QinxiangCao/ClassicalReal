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

Parameter TM : nat -> nat -> Prop.
Parameter CR : 
Definition Halting : Type := forall (i j : nat), {TM i j} + {~(TM i j)}.


Module Uncomputable_function.
  Theorem Three_dimensions : (forall r1 r2 : R, ({r1 = r2} + {r1 <> r2})%R) -> Halting.
  Proof.
    unfold Halting.
    intros.
    unfold not in *.
  Admitted.
  Theorem Rinv_def : (forall r r1 : R , Rinv r = r1) -> Halting.
  Proof.
  Admitted.
  (*Theorem lim_CN_NCN :*) 
End Uncomputable_function.


