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
From Coq Require Import Field.
From Coq Require Import Omega.
From Coq Require Import Psatz.
From CReal Require Import Dedekind.RBase.
From CReal Require Import Dedekind.ROrder.
From CReal Require Import Dedekind.RArith.
From CReal Require Import Uncomputable.Countable.
From CReal Require Import Uncomputable.ComRealBase.
From CReal Require Import Uncomputable.SingleLemmas.
From Coq Require Import PArith.BinPosDef.

Module DedekindR <: VIR_R.
  Definition R := Real.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Definition R0 := Rzero.
  Definition R1 := Rone.
  Definition Rplus := Rplus.
  Definition Rmult := Rmult.
  Definition Ropp := Ropp.
  Module Vex <: R_SINGLE_SIMPLE.
    Definition R := R.
    Delimit Scope R_scope with R.
    Bind Scope R_scope with R.
    Local Open Scope R_scope.
    Definition Req := Req.
    Definition R_Setoid := R_Setoid.
    Infix "==" := Req : R_scope.
    Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
    Definition Rsinglefun : {X: R -> Prop | P_singlefun X} -> R.
      intros.
      apply Rsinglefun.
      destruct X. exists x.
      destruct p. destruct H0.
      auto.
    Defined.
    Theorem Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
    Proof.
      intros.
      unfold Rsinglefun.
      apply Rsinglefun_correct.
    Qed.
  End Vex.
  Module Vex_Lemmas := RSignleLemmas (Vex).
  Module Rinv_partial <: RINV_PARTIAL Vex.
    Module RS := Vex. 
    Module RL := Vex_Lemmas.
    Import RS RL.
    Local Open Scope R_scope.
    Definition R0 := Rzero.
    Definition R1 := Rone.
    Definition Rmult := Rmult.
    Infix "*" := Rmult : R_scope.
    Definition Rmult_comp := R_mult_comp.
    Definition Rinv' (a : R) (H : ~ (a == R0)) : R := Rinv a H.
    Definition Rinv'_comp : forall (r1 r2 : R)(H1 : ~ r1 == R0) (H2 : ~r2 == R0), r1 == r2 -> Rinv' r1 H1 == Rinv' r2 H2 := Rinv_eq.
    Theorem Rinv'_l : forall (r : R)(H : ~ r == R0), Rinv' r H * r == R1.
    Proof.
      intros.
      rewrite Rmult_comm.
      apply Rmult_inv.
    Qed.
  End Rinv_partial.
  
  Module RPTT := Rinv_Partial_To_Total Vex Rinv_partial.
  
  Export RPTT Rinv_partial Vex_Lemmas Vex.
  Definition Rinv := Rinv.
  Definition Rlt := Rlt.
  Definition Req := Req.
  Infix "==" := Req : R_scope.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.
  Infix "<" := Rlt : R_scope.
  
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  
  Definition Rle (r1 r2:R) : Prop := Rlt r1 r2 \/ r1 ==r2.
  
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 == r2.
  
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  
  Definition Rdiv (r1 r2 :R) : R := r1 * / r2.
  
  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Notation "0" := R0 : R_scope.
  Notation "1" := R1 : R_scope.
  Notation "2" := (1+1) : R_scope.
  Definition Req_refl := Req_refl.
  
  Lemma Req_sym : forall x y : R , x == y -> y == x.
  Proof.
    split.
    + destruct H. apply H0.
    + destruct H. apply H. 
  Qed.

  Lemma Req_trans : forall x y z : R , x == y -> y == z -> x == z.
  Proof.
    split.
    + destruct H, H0. apply (Rle_trans x y z).
      * apply H.
      * apply H0.
    + destruct H, H0. apply (Rle_trans z y x).
      * apply H2.
      * apply H1.
  Qed.
  
  Instance R_Setoid : Equivalence Req.
  Proof. split; red. apply Req_refl. apply Req_sym. apply Req_trans. Qed.
  
  Definition Rplus_comp := Rplus_comp.
 
  Definition Ropp_comp := Ropp_comp.
  
  Definition Rmult_comp := R_mult_comp.
  
  Instance Rinv_comp : Proper (Req==>Req) Rinv.
  Proof.
    apply Rinv_comp.
  Qed.
  
  Instance Rle_comp : Proper (Req==>Req==>iff) Rle.
  Proof.
    split.
    - intros.
      destruct H1.
      + left. rewrite <- H , <- H0. auto.
      + right. rewrite <- H , <- H0. auto.
    - intros.
      destruct H1.
      + left. rewrite H, H0. auto.
      + right. rewrite H ,H0. auto. 
  Qed.
  
  Definition Rlt_comp := Rlt_comp.
  
  Instance Rminus_comp : Proper (Req==>Req==>Req) Rminus.
  Proof. hnf ; red ; intros. unfold Rminus. rewrite H , H0. reflexivity. Qed.
  
  Instance Rdiv_comp : Proper (Req==>Req==>Req) Rdiv.
  Proof. hnf ; red ; intros. unfold Rdiv. rewrite H , H0. reflexivity. Qed.
  
  Instance Rgt_comp : Proper (Req==>Req==>iff) Rgt.
  Proof. hnf ; red ; intros. unfold Rgt. rewrite H , H0. reflexivity. Qed.
  
  Instance Rge_comp : Proper (Req==>Req==>iff) Rge.
  Proof. hnf ; red ; intros. unfold Rge. rewrite H , H0. reflexivity. Qed.
  
  (* Complementary definition of Real Equivalence. *)
  Fixpoint pow (r:R) (n:nat) : R :=
    match n with
      | O => 1
      | S n => Rmult r (pow r n)
    end.
    
  
  Instance Rpow_comp : Proper (Req ==> eq ==> Req) pow.
  Proof. 
    hnf ; red; intros. rewrite H0. clear H0.
    induction y0.
    - simpl. reflexivity.
    - simpl. rewrite IHy0. rewrite H. reflexivity.
  Qed.
  
  (* Definition copied from Rpow_def.v *)
  
  Fixpoint IPR_2 (p:positive) : R :=
    match p with
    | xH => R1 + R1
    | xO p => (R1 + R1) * IPR_2 p
    | xI p => (R1 + R1) * (R1 + IPR_2 p)
    end.

  Definition IPR (p:positive) : R :=
    match p with
    | xH => R1
    | xO p => IPR_2 p
    | xI p => R1 + IPR_2 p
    end.
  Arguments IPR p%positive : simpl never.

  (**********)
  Definition IZR (z:Z) : R :=
    match z with
    | Z0 => R0
    | Zpos n => IPR n
    | Zneg n => - IPR n
    end.
  Arguments IZR z%Z : simpl never.
  
  (* Definitions copied from Rdefinitions.v *)
  
  Fixpoint INR (n:nat) : R :=
    match n with
    | O => 0
    | S O => 1
    | S n => INR n + 1
    end.
  Arguments INR n%nat.
  
  (* Definition copied from Raxioms.v *)
  
  Definition IQR(q : Q) : R :=
    match q with
    | p # q => IZR p / IPR q
    end.
  Arguments IQR q%Q.
  
  Definition Rplus_comm := Rplus_comm.
  
  Definition Rplus_assoc := Rplus_assoc.
  
  Definition Rplus_opp_r := Rplus_opp.
  
  Definition Rplus_0_l := Rplus_0_l.
  
  Definition Rmult_comm := Rmult_comm.
  
  Definition Rmult_assoc := Rmult_assoc.
  
  Theorem Rinv_l : forall r:R, ~ r == 0 -> / r * r == 1.
  Proof.
    apply Rinv_l.
  Qed.
  Hint Resolve Rinv_l: real.
  
  Definition Rmult_1_l := Rmult_1_l.
  
  Lemma R1_neq_R0 : ~ 1 == 0.
  Proof.
    intro. destruct H.
    hnf in H.
    apply (Qlt_irrefl 0).
    apply H. reflexivity.
  Qed.
  
  Definition Rmult_plus_distr_l := Rmult_distr_l.

  Definition total_order_T := R_three_dis.
  
  Theorem Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Proof.
    intros.
    apply Rle_not_lt.
    apply Rlt_le_weak.
    auto.
  Qed.
  
  Definition Rlt_trans := Rlt_trans.
  
  Theorem Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
  Proof.
    intros.
    rewrite Rplus_comm.
    rewrite (Rplus_comm r r2).
    rewrite Rplus_lt_l.
    auto.
  Qed.
  
  Theorem Rmult_lt_compat_l : 
     forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  Proof.
    intros.
    assert (~ r == 0).
    { intro. rewrite H1 in H.
      destruct H.
      destruct H2 ,H2.
      auto.
    } 
    apply Rmult_lt_compat_r with (z := / r).
    - apply Rmult_lt_compat_r with (z := r) ; auto.
      rewrite Rinv_l ; auto.
      rewrite Rmult_0_l. split.
      + intros. lra.
      + exists 0%Q. split ; lra.
    - repeat (rewrite Rmult_comm ; rewrite <- Rmult_assoc ; rewrite Rinv_l; auto;
      rewrite Rmult_1_l). auto.
  Qed.
  
  Axiom archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.
  
  (** We have proved a similar version in Dedekind.RArith named Zarchimedean*)

  Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

  Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.

  Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

  Lemma Rle_equiv : forall r1 r2 : R , r1 <= r2 <-> ROrder.Rle r1 r2.
  Proof.
    intros.
    split ; intros.
    - destruct H.
      + apply Rlt_le_weak. auto.
      + rewrite H. apply Rle_refl.
    - apply Rle_lt_eq in H.
      hnf. destruct H.
      + right. rewrite H. reflexivity.
      + auto.
  Qed.
  
  Theorem completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> exists m:R , is_lub E m .
  Proof.
    intros.
    pose proof R_complete.
    set (fun x => exists r , E r /\ x < r).
    assert (Rdedekind P).
    { subst P.
      split.
      - split .
        + destruct H0. exists (x - 1). exists x.
          split ; auto.
          unfold Rminus.
          rewrite <- (Rplus_0_r x) at 2.
          apply Rplus_lt_compat_l.
          rewrite Rzero_opp.
          apply Ropp_lt_compat.
          split ; intros.
          * lra.
          * exists 0%Q. lra.
        + destruct H. exists (x + 1).
          intro. 
          destruct H2 , H2.
          specialize (H _ H2).
          rewrite Rle_equiv in H.
          pose proof (Rlt_le_trans (x+1) x0 x H3 H).
          assert (x < x + 1).
          { rewrite <- Rplus_0_r at 1.
            apply Rplus_lt_compat_l.
            split.
            - intros. lra.
            - exists 0%Q. lra.
          }
          apply (Rlt_not_refl x).
          apply Rlt_trans with (x + 1) ; auto.
      - intros.
        repeat destruct H2. exists x.
        split ; auto.
        apply Rle_lt_trans with p ; auto.
      - intros.
        repeat destruct H2.
        exists ((p + x) / 2).
        assert (2 > 0).
        { split.
          - intros. exists x0 , 0%Q. lra.
          - exists 0%Q. split ; try (lra).
            exists 0%Q , 0%Q. lra.
        }
        assert (~ 2 == 0).
        { intro. apply (Rlt_not_refl 0). rewrite <- H5 at 2. auto. }
        split.
        + exists x.
          split ; auto.
          apply (Rmult_lt_compat_r _ _ 2) ; auto.
          unfold Rdiv.
          rewrite Rmult_assoc.
          rewrite Rinv_l ; auto.
          rewrite Rmult_plus_distr_l.
          rewrite !Rmult_1_r. 
          rewrite Rplus_lt_l. auto.
        + apply (Rmult_lt_compat_r _ _ 2) ; auto.
          unfold Rdiv.
          rewrite Rmult_assoc.
          rewrite Rinv_l ; auto.
          rewrite Rmult_plus_distr_l.
          rewrite !Rmult_1_r. 
          apply Rplus_lt_compat_l. auto.
      - intros. repeat destruct H3. exists x.
        rewrite H2 in *.
        split ; auto. 
    }
    specialize (H1 P H2).
    destruct H1.
    exists x.
    split.
    - hnf. intros. destruct H1.
      subst P.
      simpl in *.
      pose proof (not_ex_all_not _ _ H1 x0).
      simpl in *.
      apply not_and_or in H5.
      destruct H5.
      + exfalso. auto.
      + destruct (total_order_T x x0).
        * exfalso. auto. 
        * destruct H6.
          ** right. rewrite H6. reflexivity.
          ** left. auto.
    - subst P. simpl in *. intros.
      rewrite Rle_equiv. apply H1.
      intro.
      repeat destruct H4.
      specialize (H3 _ H4).
      apply (Rlt_not_refl b).
      apply Rlt_le_trans with x0 ; auto.
      rewrite <- Rle_equiv. auto.
  Qed.
  
End DedekindR.

Module DedekindAll: VIR_R_ALL.

Include DedekindR.
Module DedekindRSingle : VIR_R_SINGLETON DedekindR := DedekindR.Vex.
Include DedekindRSingle.

End DedekindAll.
