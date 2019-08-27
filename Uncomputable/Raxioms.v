(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*********************************************************)
(**    Axiomatisation of the classical reals             *)
(*********************************************************)

Require Export ZArith_base.
From CReal Require Export Countable.
From CReal Require Export INQ_libs.
From CReal Require Export Rdefinitions.
Require Export Field.
Local Open Scope R_scope.

(*********************************************************)
(** *            Field axioms                            *)
(*********************************************************)

(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

(**********)
Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Hint Resolve Rplus_comm: real.

(**********)
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Hint Resolve Rplus_assoc: real.

(**********)
Axiom Rplus_opp_r : forall r:R, r + - r = 0.
Hint Resolve Rplus_opp_r: real.

(**********)
Axiom Rplus_0_l : forall r:R, 0 + r = r.
Hint Resolve Rplus_0_l: real.

(***********************************************************)
(** **    Multiplication                                   *)
(***********************************************************)

(**********)
Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Hint Resolve Rmult_comm: real.

(**********)
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Hint Resolve Rmult_assoc: real.

(**********)
Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Hint Resolve Rinv_l: real.

(**********)
Axiom Rmult_1_l : forall r:R, 1 * r = r.
Hint Resolve Rmult_1_l: real.

(**********)
Axiom R1_neq_R0 : 1 <> 0.
Hint Resolve R1_neq_R0: real.

(*********************************************************)
(** **   Distributivity                                  *)
(*********************************************************)

(**********)
Axiom
  Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Rmult_plus_distr_l: real.

(*********************************************************)
(** *    Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(** **   Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T : forall r1 r2:R, r1 < r2 \/ r1 = r2 \/ r1 > r2.

(*********************************************************)
(** **   Lower                                           *)
(*********************************************************)

(**********)
Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.

(**********)
Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.

(**********)
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.

(**********)
Axiom
  Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: real.

(**********************************************************)
(** *    Injection from N to R                            *)
(**********************************************************)

(**********)
Fixpoint INR (n:nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.
Arguments INR n%nat.

(**********************************************************)
(** *    [R] Archimedean                                  *)
(**********************************************************)

Definition archimedean : nat -> R -> Prop .
  intros n r.
  apply (IQR (INQ n) <= r /\ r < IQR (INQ (n + 1))).
Defined.

Axiom archimedean_exists : forall r : R , exists x : nat , archimedean x r.

Definition upper_bound (X : nat -> R -> Prop) (U : R) : Prop := forall (n : nat)(q : R) , X n q -> q <= U.
Definition Sup (X : nat -> R -> Prop) (sup : R) : Prop := (forall r : R , upper_bound X r -> r >= sup) /\ upper_bound X sup.

Axiom upper_bound_exists_Sup : forall (X : nat -> R -> Prop) , is_function X -> (exists r : R , upper_bound X r) ->
                                          (exists sup : R , Sup X sup).

Lemma RT: ring_theory R0 R1 Rplus Rmult Rminus Ropp (eq (A := R)).
  constructor.
 intro; apply Rplus_0_l.
 exact Rplus_comm.
 symmetry ; apply Rplus_assoc.
 intro; apply Rmult_1_l.
 exact Rmult_comm.
 symmetry ; apply Rmult_assoc.
 intros m n p.
   rewrite Rmult_comm.
   rewrite (Rmult_comm n p).
   rewrite (Rmult_comm m p).
   apply Rmult_plus_distr_l.
 reflexivity.
 exact Rplus_opp_r.
Qed.

Lemma RF : field_theory 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv (eq(A:=R)).
  constructor.
 exact RT.
 exact R1_neq_R0.
 reflexivity.
 exact Rinv_l.
Qed.

Add Ring ABS: RT (abstract).
Add Field ABS' : RF (abstract).
