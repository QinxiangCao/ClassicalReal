From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import QArith.Qround.
From Coq Require Import Logic.Classical.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Export Field.
From CReal Require Import QArith_ext.QArith_base_ext.

Class Cauchy (CSeq : nat -> Q -> Prop) : Prop := {
  Cauchy_exists : forall (n:nat), exists (q:Q), (CSeq n q);
  Cauchy_unique : forall (n:nat) (q1 q2:Q),
      CSeq n q1 -> CSeq n q2 -> q1 == q2;
  Cauchy_proper: forall (p q: Q) n, p==q -> (CSeq n p -> CSeq n q);
  Cauchy_def : forall (eps:Q), eps > 0 -> (exists (n:nat),
     forall (m1 m2:nat), (m1 > n)%nat -> (m2 > n)%nat
     -> forall (q1 q2:Q), CSeq m1 q1 -> CSeq m2 q2 ->
          Qabs (q1 - q2) < eps);
}.

Arguments Cauchy_exists (CSeq) (Cauchy) : clear implicits.
Arguments Cauchy_unique (CSeq) (Cauchy) : clear implicits.
Arguments Cauchy_def (CSeq) (Cauchy) : clear implicits. 

Instance Cauchy_proper_iff: forall A n, Cauchy A -> Proper (Qeq ==> iff) (A n).
Proof.
  intros.
  hnf.
  intros.
  split.
  + apply Cauchy_proper. auto.
  + apply Cauchy_proper. symmetry. auto.
Qed.

Inductive Real : Type :=
| Real_intro (CSeq : nat -> Q -> Prop) (H: Cauchy CSeq).

Definition Real_equiv (x1 x2 : Real) : Prop :=
  match x1, x2 with
  | Real_intro CSeq1 H1,
    Real_intro CSeq2 H2 =>
      forall (eps:Q), eps>0 -> (exists (n:nat),
      forall (m:nat), (m > n)%nat -> 
        forall (q1 q2:Q), CSeq1 m q1 -> CSeq2 m q2 ->
          Qabs (q1 - q2) < eps)
  end.


Theorem Real_def_refl: reflexive Real Real_equiv.
Proof. unfold reflexive. intros. unfold Real_equiv.
  destruct x as [x H1]. intros.
  exists O. intros. apply (Cauchy_unique _ H1 m q1 q2 H2) in H3.
  assert (H': q1 - q2 == 0). { rewrite H3. ring. }
  rewrite H'. apply H.
Qed.

Theorem Real_def_symm: symmetric Real Real_equiv.
Proof. unfold symmetric. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy].
  intros. apply H in H0. destruct H0. exists x0. intros.
  rewrite Qabs_Qminus. apply (H0 m).
  apply H1. apply H3. apply H2. 
Qed.

Theorem Real_def_trans: transitive Real Real_equiv.
Proof. unfold transitive. intros. unfold Real_equiv in *.
  destruct x as [x Hx], y as [y Hy], z as [z Hz]. intros.
  assert (Heps: eps == eps *(1#2) + eps *(1#2)) by ring.
  destruct (H _ (eps_divide_2_positive eps H1)) as [n1 Hab].
  destruct (H0 _ (eps_divide_2_positive eps H1)) as [n2 Hbc].
  clear H. clear H0.
  assert (H: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct H.

- exists n2. intros m H0 q1 q3. assert (H': (m > n1)%nat). { omega. }
  intros Hxq Hzq. destruct (Cauchy_exists _ Hy m) as [q2 Hyq].
  apply (Hab _ H' q1 q2) in Hxq.
  apply (Hbc _ H0 q2 q3) in Hyq.
  apply Qlt_le_weak in Hyq.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ Hxq Hyq).
  apply Hzq. apply Hyq.


- exists n1. apply not_le in H. intros m H0 q1 q3. assert (H': (m > n2)%nat). { omega. }
  intros Hxq Hzq. destruct (Cauchy_exists _ Hy m) as [q2 Hyq].
  apply (Hab _ H0 q1 q2) in Hxq.
  apply (Hbc _ H' q2 q3) in Hyq.
  apply Qlt_le_weak in Hyq.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend q1 q2 q3)).
  rewrite Heps. apply (Qplus_lt_le_compat _ _ _ _ Hxq Hyq).
  apply Hzq. apply Hyq.
Qed.


Instance Real_equiv_holds: Equivalence Real_equiv.
Proof. split.
- apply Real_def_refl.
- apply Real_def_symm.
- apply Real_def_trans.
Qed.

Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_scope with R.

Theorem Real_has_Q: forall (x1:Q) , Cauchy (fun (n:nat) => (fun x => x == x1)).
Proof. intros. split.
  - intros. exists x1. reflexivity.
  - intros. rewrite H. rewrite H0. reflexivity.
  - intros. intros. rewrite <- H0. symmetry. apply H.
  - intros. exists O. intros. rewrite H2,H3. unfold Qminus.
    rewrite Qplus_opp_r. apply H.
Qed.

Definition inject_Q (q:Q):Real:=
 Real_intro (fun (n:nat) => (fun x => x == q)) (Real_has_Q q).

Lemma Qnot_0_abs_pos: forall (q:Q), ~(q==0) -> Qabs q > 0.
Admitted.


