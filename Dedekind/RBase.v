(** * Real: Simple real number definition *)

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
From Coq Require Import Classes.Morphisms.
Import ListNotations.

(** In this part, we use Dedekind Cut to constructing real numbers.*)

(** First, we shoule know what is Dedekind Cut.
    According to Rudin's "principles_of_mathematical_analysis",
    a Cut is any set A which is a subset of Q with the following three properties,
      i. A is not empty, and A != Q
      ii. If p is in A, q is in Q, and q < p  =>  q is in A
      iii. If p is in A, => exists r in A, p < r.
    And we call the cuts as the members of R.
    We use the letters p,q,r to denote rational numbers and A,B,C to denote the cuts.
*)

Record Dedekind ( A : Q-> Prop) : Prop := {
  Dedekind_properties1 : (exists (x : Q) , A x) /\ (exists (x : Q) , ~ A x) ;
  Dedekind_properties2 : forall (p q : Q) , A p /\ (Qle q p) -> A q ;
  Dedekind_properties3 : forall (p : Q) , A p -> (exists r, A r /\ (Qlt p r)) ;
  Dedekind_properties4 : forall (p q : Q), p == q -> A p -> A q ;
}.

Inductive Real : Type :=
  | Real_cons (A : Q -> Prop) (H : Dedekind A)
.

Delimit Scope R_scope with R.

Local Open Scope R_scope.
(** Then we will add some properties to ensure R become a field.*)

(** First , we find some members to denote zero and one.*)

Theorem Dedekind_Q : forall x1 : Q , Dedekind (fun x=> x < x1).
Proof.
  split.
  - split.
    exists (x1 - 1).
    + intros. unfold Qlt.
      simpl.
      rewrite -> Zmult_plus_distr_l.
      replace (Z.pos (Qden x1 * 1) % positive) with (QDen x1 * 1)%Z by reflexivity.
      repeat rewrite -> Zmult_1_r.
      rewrite <- Z.add_0_r.
      apply Zplus_lt_compat_l.
      reflexivity.
    + exists x1. apply Qlt_irrefl.
  - intros.
    inversion H.
    apply Qle_lt_trans with (y := q).
    + apply Qle_lteq. right. reflexivity.
    + apply Qle_lt_trans with (y := p).
      * apply H1.
      * apply H0.
  - intros.
    exists ((p + x1) * / (2 # 1) ).
    split.
    + apply Qlt_shift_div_r. 
      reflexivity.
      assert(H' : x1 * (2 # 1) == x1 + x1).
      {
        unfold Qmult.
        unfold Qplus.
        simpl. rewrite <- Zmult_plus_distr_l.
        rewrite Zmult_comm.
        rewrite <- Z.add_diag.
        unfold Qeq.
        simpl. rewrite -> Pos.mul_1_r.
        rewrite Pos2Z.inj_mul.
        rewrite Zmult_assoc. reflexivity.
      }
      rewrite H'.
      apply Qplus_lt_le_compat.
      * apply H.
      * apply Qle_refl.
    + apply Qlt_shift_div_l. 
      reflexivity.
      assert(H' : p * (2 # 1) == p + p).
      {
        unfold Qmult.
        unfold Qplus.
        simpl. rewrite <- Zmult_plus_distr_l.
        rewrite Zmult_comm.
        rewrite <- Z.add_diag.
        unfold Qeq.
        simpl. rewrite -> Pos.mul_1_r.
        rewrite Pos2Z.inj_mul.
        rewrite Zmult_assoc. reflexivity.
      }
      rewrite H'.
      apply Qplus_lt_r. apply H.
  - intros. 
    apply Qle_lt_trans with p.
    + apply Qle_lteq. right.
      symmetry. apply H.
    + apply H0. 
Qed.

Definition Rzero : Real := Real_cons (fun x => x < 0) (Dedekind_Q 0).

Definition Rone : Real := Real_cons (fun x => x < 1) (Dedekind_Q 1).

Lemma Dedekind_le : forall A x x1, Dedekind A -> (~ A x) -> A x1 -> x > x1.
Proof.
  intros.
  apply Qnot_le_lt.
  unfold not.
  intros. 
  apply H0. 
  apply (Dedekind_properties2 _ H) with x1.
  split.
  - apply H1.
  - apply H2.
Qed.

(* Fri 2019.3.15 12:44 Wu Xiwei , Hu Zhixuan *)

