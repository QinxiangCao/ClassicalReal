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
  
    (** related lemmas for reasoning archimed:begin*)
(** Proved at Uncomputable.ComRealBaseLemma1*)
Axiom plus_IZR : forall n m:Z, IZR (n + m) == IZR n + IZR m.
  Lemma opp_opp_r:forall r:R, - - r == r.
Proof. intros. destruct r. hnf.  split. hnf.  
  intros x0. apply Cut_opp_opp;auto. hnf. intros x0. apply Cut_opp_opp;auto.
Qed.
  Lemma opp_IZR : forall n:Z, IZR (- n) == - IZR n.
Proof.
  intros [|z|z]; unfold IZR; simpl; auto.
  - hnf. split;hnf;intros. 
    + unfold Cut_opp. exists (-x)%Q. split;lra.
    + destruct H,H. lra. 
  - reflexivity.
  - remember (IPR z). symmetry. apply opp_opp_r.
Qed.
  (** above copied from ComRealBaseLemma1*)
  Lemma Q_to_R_plus:forall a b, Q_to_R(a + b) == Q_to_R a + Q_to_R b.
Proof. intros. hnf. split.
  - hnf.  unfold Cut_plus_Cut. intros. exists ((x+a-b)%Q * (1 # 2))%Q.
    exists ((x-a+b)%Q * (1 # 2))%Q. split. lra. split. lra. 
    rewrite Qmult_comm. rewrite (Qmult_comm (x - a + b) (1 # 2)).
    rewrite<-(Qmult_plus_distr_r (1#2) (x+a-b) (x-a+b)).
    apply Qmult_inj_l with (2#1). lra.
    assert(forall a b:Q, (a - b)%Q == (a + (-b))%Q)%Q. { reflexivity. }
    rewrite->H0. rewrite (H0 x a). rewrite<-Qplus_assoc.
    rewrite<-(Qplus_assoc x (-a) b). rewrite (Qplus_assoc (-b) x). 
    rewrite (Qplus_comm (-b) x). rewrite<-(Qplus_assoc x a).
    rewrite<-(Qplus_assoc x (-b)). rewrite (Qplus_assoc a x (- b + (- a + b))).
    rewrite (Qplus_comm a x). rewrite<-(Qplus_assoc x a). rewrite Qplus_assoc.
    rewrite (Qplus_comm (-a)). rewrite (Qplus_assoc (-b)). rewrite (Qplus_comm (-b)). lra.
  - hnf. unfold Cut_plus_Cut. intros. destruct H,H,H,H0. lra.
Qed.
  Example IZR_QR1:IZR (-1) == Q_to_R (inject_Z (-1)).
Proof.  assert((-1)=-(1))%Z. { reflexivity. }
  rewrite H.  rewrite (inject_Z_opp 1). unfold IZR. simpl. unfold Q_to_R.
  hnf.  split. 
  - unfold Cut_opp. hnf. intros. destruct H0, H0. 
  apply Qnot_lt_le in H1. assert(1< - x)%Q. { lra. }
  assert(inject_Z 1 = 1)%Q. { reflexivity. } rewrite H3. lra.
  - unfold Cut_opp. hnf. intros. exists (-(x+1))%Q. split.
    + assert(inject_Z 1==1)%Q. { reflexivity. } rewrite H1 in H0. lra.
    + lra. 
Qed.
  Lemma IZR_Q:forall z:Z, IZR z == Q_to_R (inject_Z z).
Proof. split;generalize dependent z.
  - apply Zind.
    + (** Zero*)simpl. intros. unfold inject_Z;auto.
    + (** positive*)intros. assert(IZR (Z.succ x)== IZR x + 1).
      apply plus_IZR. rewrite H0. unfold Z.succ. rewrite inject_Z_plus.
      rewrite Q_to_R_plus. assert(1==Q_to_R (inject_Z 1)). { reflexivity. }
      rewrite<-H1. apply Rplus_le_l. auto. 
    + (** negtive*)intros. unfold Z.pred. rewrite inject_Z_plus.
      rewrite Q_to_R_plus. rewrite plus_IZR. 
      rewrite IZR_QR1. apply Rplus_le_l. auto. 
  - apply Zind.
    + (** Zero*)simpl. intros. apply H.
    + intros. unfold Z.succ. rewrite plus_IZR. rewrite inject_Z_plus.
      rewrite Q_to_R_plus. assert(Q_to_R (inject_Z 1) == IZR 1). { reflexivity. }
      rewrite H0. apply Rplus_le_l. auto.
    + intros. unfold Z.pred. rewrite inject_Z_plus. rewrite plus_IZR.
      rewrite IZR_QR1. rewrite Q_to_R_plus. apply Rplus_le_l. auto.
Qed.
  Lemma opp_simpl_lt:forall x r, IZR x < r -> IZR (x + 1) - r < 1.
Proof. intros.  rewrite plus_IZR. assert(IZR 1 == 1). { reflexivity. }
    rewrite H0. apply (Rplus_lt_compat_l (1-r)) in H. 
    rewrite (Rplus_comm (1-r)) in H. rewrite (Rplus_comm (1-r) r) in H.
    assert(1 - r == 1 + (-r)). { reflexivity. } rewrite H1 in H.
    rewrite<-Rplus_assoc in H.  rewrite<-Rplus_assoc in H. 
    rewrite (Rplus_comm r 1) in H. rewrite (Rplus_assoc 1 r) in H.
    rewrite Rplus_opp_r in H. rewrite (Rplus_comm 1 Rzero) in H.
    rewrite Rplus_0_l in H. apply H.
Qed.
  Lemma opp_simpl_le:forall x r, IZR x <= r -> IZR (x + 1) - r <= 1.
Proof. intros. destruct H.
  - hnf. left. rewrite plus_IZR. assert(IZR 1 == 1). { reflexivity. }
    rewrite H0. apply (Rplus_lt_compat_l (1-r)) in H. 
    rewrite (Rplus_comm (1-r)) in H. rewrite (Rplus_comm (1-r) r) in H.
    assert(1 - r == 1 + (-r)). { reflexivity. } rewrite H1 in H.
    rewrite<-Rplus_assoc in H.  rewrite<-Rplus_assoc in H. 
    rewrite (Rplus_comm r 1) in H. rewrite (Rplus_assoc 1 r) in H.
    rewrite Rplus_opp_r in H. rewrite (Rplus_comm 1 Rzero) in H.
    rewrite Rplus_0_l in H. apply H.
  - hnf. right.  rewrite plus_IZR.  assert(IZR 1 == 1). { reflexivity. }
    rewrite H,H0. assert(r + 1 - r == r + 1 + (-r)). { reflexivity. }
    rewrite H1. rewrite Rplus_assoc. rewrite (Rplus_comm 1 (-r)).
    rewrite<-Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l. reflexivity.
Qed.
  Lemma excluded_middle:forall P, P\/~P.
Proof. intros. pose proof classic P. apply H.
Qed.
  Lemma not_conj_imply:forall P Q:Prop,~(P/\~Q) -> (P ->Q).
Proof. intros. pose proof classic Q. destruct H1;auto.
  destruct H. split;auto.
Qed.
  Lemma not_conj_disj:forall P Q, ~(P /\ ~Q) -> ~P \/Q.
Proof.
  intros. apply imply_to_or. intros. pose proof classic Q.
  destruct H1;auto. destruct H. split;auto. 
Qed. 
  Lemma archimed' : forall r:R, exists z : Z , IZR z >= r /\ IZR z - r < 1.
Proof. (** pose proof : add lemmas to the context*)
  intros. pose proof mylemma1. remember r. destruct r.
  assert(exists m, A (inject_Z m)/\ ~(A (inject_Z (m+1)))).
  { apply exists_dist. intros H1. 
    assert(~ (forall m : Z, A (inject_Z m) -> A (inject_Z (m + 1)))).
    apply H;auto. destruct H2. intros m. apply not_conj_imply. apply H1. } clear H.
  (** above we found a Z*)
  destruct H1. exists (x+1)%Z. split.
  - pose proof (excluded_middle (forall x1:Q, x1<(inject_Z (x+1)) -> A x1)%Q).
    destruct H1. hnf. right. rewrite IZR_Q. rewrite Heqr0. hnf. split.
    + hnf. intros. apply H1;auto.
    + hnf. intros. destruct H. eapply Dedekind_le;eauto.
    + hnf. left. rewrite IZR_Q,Heqr0. hnf. split.
      * intros. destruct H. eapply Dedekind_le;eauto.
      * apply exists_dist. intros H2. destruct H1. intros x1.
        apply not_conj_imply. apply H2.
  - apply opp_simpl_lt. rewrite IZR_Q. hnf. (* left(** lt R0*). *)
    rewrite Heqr0. hnf. split.
    + (** A->B*)intros. apply (Dedekind_properties2 _ H0 (inject_Z x)).
      destruct H. split;auto. apply Qlt_le_weak. apply H1.
    + (** B x->~A x*)exists (inject_Z x). destruct H. split;auto.
      apply Qle_not_lt. apply Qle_refl.
Qed.
  (** related lemmas for reasoning archimed:end*)
  Theorem archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.
Proof. intros r. pose proof (archimed' (-r)). destruct H,H.
  exists (1 + -x)%Z. split. 
  - rewrite plus_IZR. unfold Rgt. rewrite opp_IZR. 
    apply (Rplus_lt_compat_l (-IZR x)) in H0. rewrite Rplus_comm.
    assert(IZR x - - r == IZR x + - - r). { reflexivity. }
    rewrite H1 in H0. rewrite<-Rplus_assoc in H0. 
    rewrite (Rplus_comm (-IZR x))in H0. rewrite Rplus_opp_r in H0.
    rewrite Rplus_0_l in H0. rewrite opp_opp_r in H0. apply H0.
  - rewrite plus_IZR. unfold Rge in H. hnf. destruct H.
    + left. unfold Rgt in H. apply (Rplus_lt_compat_l (1+ -(IZR x))) in H.
      rewrite (Rplus_assoc _ _ (IZR x)) in H. rewrite (Rplus_comm 1 (-IZR x + IZR x)) in H.
      rewrite (Rplus_comm (-IZR x))in H. rewrite Rplus_opp_r in H. rewrite Rplus_0_l in H.
      rewrite opp_IZR. apply H.
    + right. rewrite opp_IZR,H,opp_opp_r. assert(IZR 1+r-r==IZR 1+r+-r). { reflexivity. }
      rewrite H1, Rplus_assoc, Rplus_opp_r. rewrite Rplus_comm. rewrite Rplus_0_l. reflexivity.
Qed.
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
  
  Lemma R1_gt_R0 : 1 > 0. Admitted.

End DedekindR.

Module DedekindAll: VIR_R_ALL.

Include DedekindR.
Module DedekindRSingle : VIR_R_SINGLETON DedekindR := DedekindR.Vex.
Include DedekindRSingle.

End DedekindAll.
