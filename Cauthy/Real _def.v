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
Import ListNotations.

Module Definition_Cauthy.

Definition Cauthy_Sequence (A:nat->Q):Prop:=
forall (x:Q),x>0->(exists(N:nat),forall(m n:nat)
,(m>N)%nat/\(n>N)%nat->Qabs(A m-A n)<x).

Inductive Real:Type :=
|Real_intro(x:nat->Q)(H:Cauthy_Sequence x).

Definition Req(x1 x2:Real):Prop:=
match x1,x2 with
|Real_intro Seq1 H1,Real_intro Seq2 H2
  =>forall (epsilon:Q) ,epsilon>0->
  (exists (N:nat),forall (n:nat),(n>N)%nat->
  Qabs (Seq1 n -Seq2 n)<epsilon) end.
Notation "a == b" := (Req a b).
Definition Rlt(x1 x2:Real):Prop:=
match x1,x2 with
|Real_intro Seq1 H1,Real_intro Seq2 H2
  =>forall (epsilon:Q) ,epsilon>0->
  (exists (N:nat),forall (n:nat),(n>N)%nat->
  Seq1 n<Seq2 n )end.
Notation "a < b" := (Rlt a b).
Definition Rle(x1 x2 :Real):Prop:=
Req x1 x2/\Rlt x1 x2.
Notation "a <= b" :=(Rle a b).

Definition Seq_plus(Seq1 Seq2:nat->Q) :nat->Q:=
fun (n:nat)=>Seq1 n+Seq2 n.

Theorem Seq_plus_property:forall Seq1 Seq2,
Cauthy_Sequence Seq1->Cauthy_Sequence Seq2
->Cauthy_Sequence (Seq_plus Seq1 Seq2).
Admitted.

Definition Rplus (x1 x2:Real) :Real
match x1,x2 with
|Real_intro Seq1 H1,Real_intro Seq2 H2 =>
  Real_intro  (Seq_plus Seq1 Seq2)
(Seq_plus_property Seq1 Seq2 H1 H2) end. 

Theorem Rle_refl: forall x : Real, x <= x.
Admitted.
Theorem Reqb_refl: forall x : Real, x == x.
Admitted.
Theorem Rlt_le_weak: forall x y : Real, x < y -> x <= y.
Admitted.
Theorem Rle_trans: forall x y z : Real, x <= y -> y <= z -> x <= z.
Admitted.
Theorem Rlt_trans: forall x y z : Real, x < y -> y < z -> x < z.
Admitted.
Theorem Rle_not_lt: forall x y : Real, x <= y -> ~ y < x.
Admitted.
Theorem Rlt_not_le: forall x y : Real, x < y -> ~ y <= x.
Admitted.
Theorem Rle_antisym: forall x y : Real, x <= y -> y <= x -> x == y.
Admitted.
Theorem Rle_lt_trans: forall x y z : Real, x <= y -> y < z -> x < z.
Admitted.
Theorem Rlt_le_trans: forall x y z : Real, x < y -> y <= z -> x < z.
Admitted.
Theorem not_exists_not_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) <-> (forall x, P x).
Admitted.
Theorem not_exists_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, P x) <-> (forall x, ~ P x).
Admitted.
Theorem Rnot_le_lt: forall x y : Real, ~ x <= y -> y < x.
Admitted.
Theorem Rnot_lt_le: forall x y : Real, ~ x < y -> y <= x.
Admitted.

