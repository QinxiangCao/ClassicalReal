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
Local Open Scope CReal_Scope.

Bind Scope DReal_Scope with Dedekind.RBase.Real.
Delimit Scope DReal_Scope with D.


Notation "a == b" :=(D2.Req a b):DReal_Scope.
Notation "a + b" :=(D3.Rplus a b):DReal_Scope.
Notation "a * b" :=(D3.Rmult a b):DReal_Scope.
Notation "a == b" :=(C1.Real_equiv a b):CReal_Scope.
Notation "a + b" :=(C1.Rplus a b):CReal_Scope.
Notation "a * b" :=(C1.Rmult a b):CReal_Scope.
Lemma Dcut_P: forall (n:positive)(Dcut:Q->Prop),Dedekind Dcut ->
exists (m:Z),Dcut (m#n)/\~Dcut (m+1#n).
Proof.
  intros. assert(exists (t:Z),Dcut (t#n)).
  { destruct H. destruct Dedekind_properties1. Search Z Q. destruct H.
  destruct Inject_lemmas.le_inject_Z with x.
  exists (Zpos(n)*x0)%Z. assert(Z.pos n * x0 # n<=x).
Admitted.
Definition CSeq_pre (DCut: Q -> Prop): nat -> Q -> Prop :=
(fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).

Theorem Cauchy_Dcut :forall (DCut:Q->Prop),
Dedekind DCut->Cauchy (CSeq_pre DCut). (*(fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).
*)
Proof.
  intros.
  split.
- intros. unfold CSeq_pre. 
  assert(exists (N:Z), DCut (N # 2 ^ of_nat n) /\
  ~ DCut (N + 1 # 2 ^ of_nat n)). apply Dcut_P. apply H.
  destruct H0.
  exists( x # 2 ^ of_nat n). exists x.
  split. apply H0. split. apply H0. reflexivity.
- intros. unfold CSeq_pre in *. destruct H0. destruct H1.
  assert(x=x0)%Z.
  { assert(x<=x0+1)%Z.

Definition D2C (B:D1.Real):C1.Real :=
match B with
|Real_cons DCut H =>
Real_intro (fun n q=>exists N:Z,DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q)
(Cauchy_Dcut DCut H) end.

Theorem C2D_properity1:forall (x y:D1.Real),
  ((D2C x)+(D2C y))==(D2C ( x+ y)).
Proof.
Admitted.

Theorem C2D_properity2:forall (x y:D1.Real),
 (D2C x)*(D2C y)==(D2C (x * y)).
Proof.
Admitted.

Theorem C2D_properity3:forall (x y:D1.Real),
(x==y)%D->  ((D2C x)==(D2C y)).
Proof.
Admitted.

