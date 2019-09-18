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

Theorem Cauchy_Dcut :forall (DCut:Q->Prop),
Dedekind DCut->Cauchy (fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).
Proof.
Admitted.

Definition D2C (B:D1.Real):C.Real :=
match B with
|Real_cons DCut H =>
Real_intro (fun n q=>exists N:Z,DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q)
(Cauchy_Dcut DCut H) end.

Theorem C2D_properity1:forall (x y:D1.Real),
 C.Real_equiv(C3.Rplus (D2C x)(D2C y))(D2C (D3.Rplus x y)).
Proof.
Admitted.

Theorem C2D_properity2:forall (x y:D1.Real),
 C.Real_equiv (C3.Rmult(D2C x)(D2C y))(D2C (D3.Rmult x y)).
Proof.
Admitted.

Theorem C2D_properity3:forall (x y:D1.Real),
(x==y)->  (C.Real_equiv (D2C x)(D2C y)).
Proof.
Admitted.

