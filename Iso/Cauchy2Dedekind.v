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
From CReal Require Import Dedekind.RBase.
From CReal Require Import Dedekind.ROrder.
From CReal Require Import Dedekind.RArith.
From CReal Require Import Cauchy.RBase.
From CReal Require Import Cauchy.RArith.
From CReal Require Import Cauchy.ROrder.
From Coq Require Import PArith.BinPosDef.
Import Pos.

Module C := Cauchy.RBase.
Module C2 := Cauchy.ROrder.
Module C3 := Cauchy.RArith.
Module D1 := Dedekind.RBase.
Module D2 := Dedekind.ROrder.
Module D3 := Dedekind.RArith.

Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)).
Proof.
Admitted.

Definition C2D (A:C.Real):D1.Real :=
match A with
|Real_intro CSeq H =>
Real_cons (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)) (Dedekind_CSeq CSeq H) end.

Theorem C2D_properity1:forall (x y:C.Real),
  (D3.Rplus (C2D x)(C2D y)==C2D (x+y)).
Proof.
Admitted.

Theorem C2D_properity2:forall (x y:C.Real),
  (D3.Rmult(C2D x)(C2D y))==C2D (C3.Rmult x y).
Proof.
Admitted.

Theorem C2D_properity3:forall (x y:C.Real),
(x==y)%R->  ((C2D x)==(C2D y)).
Proof.
Admitted.


