Require Import Nnat.
Require Import ArithRing.
Require Export Ring Field.
From CReal Require Import ComRealBase.

(* All theorems and proofs copied from RealField.v *)

Module VirR_Field (R : VIR_R).

Import R.
Local Open Scope R_scope.
  
Theorem R1_neq_R0 : ~ 1 == 0.
Proof.
  intro.
  pose proof R1_gt_R0.
  rewrite H in *.
  apply (Rlt_asym 0 0) ; auto.
Qed.
Hint Resolve R1_neq_R0 : real.
  
Lemma RTheory : ring_theory 0 1 Rplus Rmult Rminus Ropp Req.
Proof.
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

Lemma Rfield : field_theory 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv Req.
Proof.
constructor.
 exact RTheory.
 exact R1_neq_R0.
 reflexivity.
 exact Rinv_l.
Qed.

Lemma Rlt_n_Sn : forall x, x < x + 1.
Proof.
  intros.
  rewrite <- Rplus_0_l at 1.
  rewrite Rplus_comm.
  apply Rplus_lt_compat_l.
  apply R1_gt_R0.
Qed.

Lemma Rlt_0_2 : 0 < 2.
Proof.
apply Rlt_trans with (0 + 1).
 apply Rlt_n_Sn.
 rewrite Rplus_comm.
   apply Rplus_lt_compat_l.
    assert (1 == 0 + 1).
    { symmetry. apply Rplus_0_l. }
    rewrite H. 
  apply Rlt_n_Sn.
Qed.

Lemma Rdef_pow_add : forall (x:R) (n m:nat), pow x  (n + m) == pow x n * pow x m.
Proof.
  intros x n; elim n; simpl; auto with real.
  intros n0 H' m; rewrite H'; auto with real.
Qed.

Lemma R_power_theory : power_theory 1%R Rmult Req N.to_nat pow.
Proof.
 constructor. destruct n. reflexivity.
 simpl. induction p.
 - rewrite Pos2Nat.inj_xI. simpl. rewrite plus_0_r, Rdef_pow_add, IHp. reflexivity.
 - rewrite Pos2Nat.inj_xO. simpl. now rewrite plus_0_r, Rdef_pow_add, IHp.
 - simpl. rewrite Rmult_comm;apply Rmult_1_l.
Qed.

Ltac Rpow_tac t :=
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N.of_nat t)
  end.

Ltac IZR_tac t :=
  match t with
  | R0 => constr:(0%Z)
  | R1 => constr:(1%Z)
  | IZR ?u =>
    match isZcst u with
    | true => u
    | _ => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Add Ring ABS: RTheory (abstract).
Add Field ABS' : Rfield 
   ( constants [IZR_tac], power_tac R_power_theory [Rpow_tac]).
   
End VirR_Field.
