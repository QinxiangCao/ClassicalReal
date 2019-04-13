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
Require Import CReal.Cauchy.RBase.
Require Import CReal.Cauchy.ROrder.
From Coq Require Import PArith.BinPosDef.
Import Pos.
Module C1:=Cauchy.RBase.
Module C2:=Cauchy.ROrder.
Module D1 := Dedekind.RBase.
Module D2 := Dedekind.ROrder.
Module D3 := Dedekind.RArith.
Bind Scope CReal_Scope with Cauchy.RBase.Real.
Delimit Scope CReal_Scope with C.

Bind Scope DReal_Scope with Dedekind.RBase.Real.
Delimit Scope DReal_Scope with D.
Local Open Scope DReal_Scope.

Notation "a == b" :=(D2.Req a b):DReal_Scope.
Notation "a + b" :=(D3.Rplus a b):DReal_Scope.
Notation "a * b" :=(D3.Rmult a b):DReal_Scope.
Notation "a == b" :=(C1.Real_equiv a b):CReal_Scope.
Notation "a + b" :=(C1.Rplus a b):CReal_Scope.
Notation "a * b" :=(C1.Rmult a b):CReal_Scope.

Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)).
Proof.
Admitted.

Definition C2D (A:C1.Real):D1.Real :=
match A with
|Real_intro CSeq H =>
Real_cons (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)) (Dedekind_CSeq CSeq H) end.

Theorem C2D_properity1:forall (x y:C1.Real),
  ( (C2D x)+(C2D y)==C2D (x+y))%D.
Proof.
Admitted.

Theorem C2D_properity2:forall (x y:C1.Real),
  ((C2D x)*(C2D y)==C2D ( x *y))%D.
Proof.
Admitted.

Theorem C2D_properity3:forall (x y:C1.Real),
(x==y)%C->  ((C2D x)==(C2D y)).
Proof.
Admitted.


