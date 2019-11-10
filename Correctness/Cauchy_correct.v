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
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Field.
From Coq Require Import Omega.
From Coq Require Import Psatz.
From CReal Require Import Cauchy.RBase.
From CReal Require Import Cauchy.RArith.
From CReal Require Import Cauchy.RSign.
From CReal Require Import Cauchy.ROrder.
From CReal Require Import Cauchy.RAbs.
From CReal Require Import Cauchy.RFunc.
From CReal Require Import Cauchy.RComplete.
From CReal Require Import Uncomputable.Countable.
From CReal Require Import Uncomputable.ComRealBase.
From CReal Require Import Uncomputable.ComRealField.
From CReal Require Import Uncomputable.ComRealBaseLemma1.
From CReal Require Import Uncomputable.SingleLemmas.
From Coq Require Import PArith.BinPosDef.

Module CauchyR <: VIR_R.
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
    Definition R := Real.
    Delimit Scope R_scope with R.
    Bind Scope R_scope with R.
    Local Open Scope R_scope.
    Definition Req := Real_equiv.
    Definition R_Setoid := Real_equiv_holds.
    Infix "==" := Req : R_scope.
    Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
    Definition Rsinglefun : {X: R -> Prop | P_singlefun X} -> R.
      intros.
      apply RSingleFun.
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
    Definition Rmult_comp := Rmult_comp.
    Definition rinv' := Rinv.
    Definition Rinv' (a : R) (H : ~ (a == R0)) : R.
      apply rinv'.
      exists a. apply H.
    Defined.
    Theorem Rinv'_comp : forall (r1 r2 : R)(H1 : ~ r1 == R0) (H2 : ~r2 == R0), r1 == r2 -> Rinv' r1 H1 == Rinv' r2 H2.
    Proof.
      intros.
      pose proof Rinv_equiv (exist _ r1 H1) (exist _ r2 H2).
      specialize (H0 H).
      apply H0.
    Qed.
    Theorem Rinv'_l : forall (r : R)(H : ~ r == R0), Rinv' r H * r == R1.
    Proof.
      intros.
      rewrite Rmult_comm.
      apply Rmult_inv_r'.
    Qed.
  End Rinv_partial.
  
  Module RPTT := Rinv_Partial_To_Total Vex (Rinv_partial).
  
  Export RPTT Rinv_partial Vex_Lemmas Vex.
  Definition Rinv := Rinv.
  Definition Rlt := Rlt.
  Definition Req := Real_equiv.
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
  
  Definition Rdiv (r1 r2 :R) : R := r1 * Rinv r2.
  
  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.
  Notation "0" := R0 : R_scope.
  Notation "1" := R1 : R_scope.
  Notation "2" := (1+1) : R_scope.
  
  Definition Req_refl := Real_def_refl.
  
  Definition Req_sym := Real_def_symm.

  Definition Req_trans := Real_def_trans.
  
  Definition R_Setoid := Real_equiv_holds.
  
  Definition Rplus_comp := Rplus_comp.
 
  Definition Ropp_comp := Ropp_comp.
  
  Definition Rmult_comp := Rmult_comp.
  
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
    
  Notation "x ^ y" := (pow x y) : R_scope.
  
  Instance Rpow_comp : Proper (Req ==> eq ==> Req) pow.
  Proof. 
    hnf ; red; intros. subst.
    induction y0.
    - reflexivity.
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
  
  Definition Rplus_opp_r := Rplus_opp_r.
  
  Definition Rplus_0_l := Rplus_0_l.
  
  Definition Rmult_comm := Rmult_comm.
  
  Definition Rmult_assoc := Rmult_assoc.
  
  Theorem Rinv_l : forall r:R, ~ r == 0 -> Rinv r * r == 1.
  Proof.
    apply Rinv_l.
  Qed.
  
  Definition Rmult_1_l := Rmult_1_l.
  
  Theorem R1_gt_R0 : 0 < 1.
  Proof.
    rewrite <- Rpositive_gt_0.
      hnf.
      exists 1%Q.
      split ; try (lra).
      exists O.
      intros.
      simpl in H0.
      lra.
  Qed.

  Theorem Rmult_plus_distr_l : 
    forall r1 r2 r3 : R, r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
  Proof.
    intros.
    rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    rewrite ! (Rmult_comm r1).
    reflexivity.
  Qed.
  
  Theorem total_order_T : forall r1 r2 : R, r1 < r2 \/ r1 == r2 \/ r2 < r1.
  Proof.
    intros.
    destruct (classic (r1 < r2)) ; auto.
    apply Rnot_lt in H.
    auto.
  Qed.
  
  Theorem Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Proof.
    intros. intro.
    apply (Rlt_irrefl r1).
    apply Rlt_trans with r2 ; auto.
  Qed.
  
  Definition Rlt_trans := Rlt_trans.
  
  Theorem Rplus_lt_compat_l : 
    forall r r1 r2 : R, r1 < r2 -> (r + r1)%R < (r + r2)%R.
  Proof.
    intros.
    rewrite ! (Rplus_comm r).
    apply Rlt_plus_r. auto.
  Qed.
  
  Theorem Rmult_lt_compat_l : 
     forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  Proof.
    intros.
    rewrite !(Rmult_comm r).
    apply Rlt_mult_r with (C := r) ; auto.
    apply Rpositive_gt_0. auto.
  Qed.
  
End CauchyR.

Module CauchyR_complete : VIR_R_COMPLETE CauchyR.
  Module RF := VirR_Field(CauchyR).
  Module RLemma1 := VirRLemma1 CauchyR.
  Export CauchyR RF RLemma1.
  Local Open Scope R_scope. (*
  Module Vex <: VIR_R_SINGLETON VirR.
    Definition R := VirR.R.
    Delimit Scope R_scope with R.
    Bind Scope R_scope with R.
    Local Open Scope R_scope.
    Definition Req := Req.
    Definition R_Setoid := R_Setoid.
    Infix "==" := Req : R_scope.
    Definition P_singlefun (X : R -> Prop) := (forall x1 x2, X x1 -> X x2 -> x1 == x2)
         /\ (exists x, X x) /\ Proper (Req ==> iff) X.
    Definition Rsinglefun := Rsinglefun.
    
    Definition Rsinglefun_correct := Rsinglefun_correct.
  End Vex.
  *)
  Module Vex_Lemmas := RSignleLemmas CauchyR.Vex.
  
  Export CauchyR.Vex Vex_Lemmas.
  
  Lemma not_conj_disj:forall P Q, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros. pose proof classic P. destruct H0. 
  - right. intros Hq. destruct H. split;auto.
  - left. auto.
Qed.
  Lemma imply_iff:forall P Q:Prop, (P->Q) <-> (~P \/ Q).
Proof. intros P Q. split.
  - intros. pose proof classic P. destruct H0.
    + right.  auto.
    + left. intros Hp. auto. 
  - intros. destruct H;auto. destruct H;auto.
Qed.
  Lemma exists_dist :
  forall (X:Type) (P : X -> Prop),
    (exists x, P x) <-> ~ (forall x, ~ P x).
Proof. intros. split. 
  - intros. destruct H. intros Hcontra. apply (Hcontra x);auto.
  - intros. pose proof classic (exists x : X, P x). destruct H0.
    + apply H0. 
    + destruct H. intros x Hx. destruct H0. exists x. apply Hx.
Qed.
  Lemma not_forall_exists{X:Type}:forall (P Q:X->Prop),
    (~(forall x,P x -> Q x)) -> exists x, P x /\ ~Q x.
Proof. intros. pose proof classic (exists x : X, P x /\ ~Q x).
  destruct H0;auto. destruct H. intros. pose proof classic (Q x).
  destruct H1;auto. destruct H0;auto. exists x;split;auto.
Qed. 
  Theorem IZR_Q:forall z:Z, IZR z == inject_Q (inject_Z z).
Proof. apply Zind.
  - reflexivity.
  - intros. unfold Z.succ. rewrite plus_IZR.  rewrite inject_Z_plus. 
    rewrite inject_Q_plus. assert(IZR 1 == inject_Q (inject_Z 1)).
    { hnf. intros. exists O. intros. rewrite H2,H3. unfold Qminus.
    rewrite Qplus_opp_r. apply H0. } rewrite H,H0. reflexivity.
  - intros. unfold Z.pred. rewrite plus_IZR, inject_Z_plus, inject_Q_plus.
    assert(IZR (-1) == inject_Q (inject_Z (-1))). {
    hnf. unfold Cauchy_opp. intros. exists O. intros. assert(-1 = -(1))%Z. reflexivity.
    rewrite H4,(inject_Z_opp 1) in H3. clear H4. assert(-q2==1)%Q.
    { rewrite H3. rewrite Qopp_opp. reflexivity. }
    apply (H2 (-q2)%Q)in H4. rewrite Qopp_opp in H4. rewrite H4. unfold Qminus.
    rewrite Qplus_opp_r. apply H0. } rewrite H, H0. reflexivity.
Qed.
  Theorem R_Archimedian':forall A B:R, 
    Rpositive A -> Rpositive B -> exists z:Z, inject_Q (inject_Z z) * A > B.
Proof. pose proof R_Archimedian. intros. pose proof classic (A<B).
  destruct H2. 
  - (** lt*) apply (H A B) in H0.  destruct H0. exists (Z.of_nat x). apply H0. auto.
  - apply Rnot_lt in H2. destruct H2.
    + (** eq*) exists 2%Z. rewrite H2. unfold Rgt. rewrite<-Rmult_1_l at 1.
      rewrite Rmult_comm. rewrite (Rmult_comm _ B). apply Rlt_mult_l. apply H1.
      hnf. exists 1%Q. split. lra. unfold RArith.Rminus.  unfold RArith.Ropp. 
      unfold RArith.Rplus.  unfold inject_Q. unfold Rone. unfold Cauchy_opp. 
      exists O. unfold CauchySeqPlus. intros.  rewrite (H4 2 (-1))%Q;try lra.
      reflexivity. intros. lra.
    + (** gt*) exists 1%Z. assert(inject_Q (inject_Z 1) == 1). reflexivity.
      rewrite H3. rewrite Rmult_1_l. apply H2.
Qed.
  Theorem R_Archimedian'':forall A:R, Rpositive A -> 
    exists z:Z, inject_Q (inject_Z z) > A.
Proof. pose proof (R_Archimedian' 1). intros. assert(Rpositive 1).
  { unfold Rpositive. unfold Rone. exists 1%Q. split. lra. exists O.
    intros. rewrite H2. lra. } 
  apply (H A) in H1;auto. destruct H1. exists x. rewrite<-Rmult_1_l.
  rewrite Rmult_comm. apply H1. 
Qed.
  Lemma czlemma1:forall a b:R,Rpositive a -> Rpositive b  
    -> (forall n, inject_Q (inject_Z n)*a>b -> inject_Q (inject_Z (n-1))*a>b)
    -> exists x1,forall m, inject_Q (inject_Z(x1 + m))* a>b.
Proof. intros a b Ha Hb H. assert(Rpositive a) by auto.
  apply (R_Archimedian' a b) in H0;auto. destruct H0. 
  exists x. apply Zind. - (** m=0*) rewrite Zplus_0_r. apply H0.
  - (** m+1*)intros. unfold Z.succ. rewrite Zplus_assoc. rewrite inject_Z_plus.
  rewrite inject_Q_plus. remember (inject_Q (inject_Z (x + x0))).
  assert(r*a + a>r*a). { unfold Rgt. rewrite<-Rplus_0_r at 1. 
  apply Rplus_lt_compat_l. apply Rpositive_gt_0 in Ha. apply Ha. }
  rewrite Rmult_comm.  rewrite Rmult_plus_distr_l. rewrite Rmult_comm. 
  rewrite Rmult_1_r. apply Rlt_trans with (r*a);auto.  
  - (** m-1*)intros. apply H in H1. unfold Z.pred. rewrite Zplus_assoc. apply H1.
Qed.
  Lemma czlemma2:forall a b:R,Rpositive a -> Rpositive b  
    -> (forall n, inject_Q (inject_Z n)*a>b -> inject_Q (inject_Z (n-1))*a>b)
    -> forall m, inject_Q (inject_Z m)* a>b.
Proof. intros. 
  assert(exists x1, forall m, inject_Q (inject_Z (x1 + m)) * a > b).
  { apply czlemma1;auto. } 
  destruct H2. assert(inject_Q (inject_Z (x + (-x +m))) * a > b).
  apply H2. rewrite Zplus_assoc in H3. rewrite Zplus_opp_r in H3. 
  rewrite Zplus_0_l in H3. apply H3.
Qed.
  Lemma czlemma3:forall a b:R,Rpositive a -> Rpositive b  
    -> ~(forall n, inject_Q (inject_Z n)*a>b -> inject_Q (inject_Z (n-1))*a>b).
Proof. intros. intros H1. assert(forall m, inject_Q (inject_Z m)* a>b).
  { apply czlemma2;auto. } assert(0*a>b). { 
    replace Rzero with (inject_Q (inject_Z 0)) by reflexivity. apply H2. }
  rewrite Rmult_0_l in H3. apply Rpositive_gt_0 in H0. apply Rlt_asym in H0.
  destruct H0. auto.
Qed.
  (** czlemma_le just like czlemma except changing lt to le*)
  Lemma czlemma1_le:forall a b:R,Rpositive a -> Rpositive b  
    -> (forall n, inject_Q (inject_Z n)*a>=b -> inject_Q (inject_Z (n-1))*a>=b)
    -> exists x1,forall m, inject_Q (inject_Z(x1 + m))* a>=b.
Proof. intros a b Ha Hb H. assert(Rpositive a) by auto.
  apply (R_Archimedian' a b) in H0;auto. destruct H0. 
  exists x. apply Zind. - (** m=0*) rewrite Zplus_0_r. 
  unfold Rge. left. apply H0.
  - (** m+1*)intros. unfold Z.succ. rewrite Zplus_assoc. rewrite inject_Z_plus.
  rewrite inject_Q_plus. remember (inject_Q (inject_Z (x + x0))).
  assert(r*a + a>r*a). { unfold Rgt. rewrite<-Rplus_0_r at 1. 
  apply Rplus_lt_compat_l. apply Rpositive_gt_0 in Ha. apply Ha. }
  rewrite Rmult_comm.  rewrite Rmult_plus_distr_l. rewrite Rmult_comm. 
  rewrite Rmult_1_r. destruct H1. 
    + unfold Rge. left. apply Rlt_trans with (r*a);auto.
    + rewrite H1. unfold Rge. left. unfold Rgt. rewrite<-Rplus_0_r at 1. 
      apply Rplus_lt_compat_l. apply Rpositive_gt_0 in Ha. apply Ha.
  - (** m-1*)intros. apply H in H1. unfold Z.pred. rewrite Zplus_assoc. apply H1.
Qed.
  Lemma czlemma2_le:forall a b:R,Rpositive a -> Rpositive b  
    -> (forall n, inject_Q (inject_Z n)*a>=b -> inject_Q (inject_Z (n-1))*a>=b)
    -> forall m, inject_Q (inject_Z m)* a>=b.
Proof. intros. 
  assert(exists x1, forall m, inject_Q (inject_Z (x1 + m)) * a >= b).
  { apply czlemma1_le;auto. } 
  destruct H2. assert(inject_Q (inject_Z (x + (-x +m))) * a >= b).
  apply H2. rewrite Zplus_assoc in H3. rewrite Zplus_opp_r in H3. 
  rewrite Zplus_0_l in H3. apply H3.
Qed.
  Lemma czlemma3_le:forall a b:R,Rpositive a -> Rpositive b  
    -> ~(forall n, inject_Q (inject_Z n)*a>=b -> inject_Q (inject_Z (n-1))*a>=b).
Proof. intros. intros H1. assert(forall m, inject_Q (inject_Z m)* a>=b).
  { apply czlemma2_le;auto. } assert(0*a>=b). { 
    replace Rzero with (inject_Q (inject_Z 0)) by reflexivity. apply H2. }
  rewrite Rmult_0_l in H3. apply Rpositive_gt_0 in H0.
  apply Rge_not_lt in H3. auto.
Qed.
  Lemma IZR_change:forall x r, IZR x - r > 1 -> IZR (x-1) > r.
Proof. intros. apply (Rplus_lt_compat_l (r-1)) in H. unfold Rminus in H.
   (** left H*)rewrite Rplus_assoc in H. rewrite (Rplus_comm _ 1) in H.
   rewrite Rplus_opp_r in H. rewrite Rplus_0_r in H. 
  (** right H*) rewrite Rplus_assoc in H. rewrite<-(Rplus_assoc (-1%R)) in H.
   rewrite (Rplus_comm (-1%R)) in H. rewrite<-(opp_IZR 1) in H.
   rewrite<-plus_IZR in H. rewrite Rplus_comm in H. assert(-r + r==0).
   { rewrite Rplus_comm. rewrite Rplus_opp_r. reflexivity. }
    rewrite Rplus_assoc in H. rewrite H0 in H. rewrite Rplus_0_r in H.
    apply H.
Qed.
  Example pos1:Rpositive 1.
Proof. unfold Rpositive. unfold Rone. exists 1%Q. split. lra.
  exists O. intros. rewrite H0. lra.
Qed. 
  Lemma Rnot_ge_lt:forall a b, ~(a>=b) -> a<b.
Proof. intros. pose proof classic (a<b). destruct H0;auto.
  destruct H. apply Rnot_lt_le in H0. hnf. destruct H0.
  - left;auto. -  right. symmetry; auto.
Qed.
  (** lemmas for proving archimed: end*)
  Theorem archimed : forall r:R, exists z : Z , IZR z > r /\ IZR z - r <= 1.
Proof. pose proof czlemma3. intros r. pose proof (Real_sgn_case r).
  destruct H0 as [H0|[H0|H0]].
  - (** positive*) apply exists_dist. intros Hcontra.
    assert(forall x, (~(IZR x > r) \/ ~(IZR x - r <= 1))).
    { intros. apply not_conj_disj. apply Hcontra. } 
    assert(forall x, IZR x>r -> IZR (x-1) > r).
    { intros x. apply imply_iff. destruct (H1 x). 
      + left;auto. 
      + right. apply IZR_change. apply Rnot_le_lt. apply H2. }
    apply (H 1 r);auto using pos1. intros n. repeat rewrite<-IZR_Q.
    repeat rewrite Rmult_1_r. apply H2.
  - (** zero*)exists (1)%Z. unfold IZR. unfold IPR. rewrite H0. split.
    + unfold Rgt. hnf. exists (1)%Q. split. lra. exists O. intros. 
      hnf in H2. unfold Cauchy_opp in H2. rewrite (H2 1 0)%Q;try lra.
      intros. rewrite H3. lra.
    + assert(1%R-0==1)%R. { unfold RArith.Rminus.
      rewrite<-Rzero_opp_zero.  rewrite Rplus_0_r. reflexivity. } rewrite H1.
      hnf. right;reflexivity.
  - (** negative*) clear H. pose proof czlemma3_le. apply Rnegative_Ropp in H0.
    apply (H 1 (-r)) in H0;auto using pos1. clear H. apply not_forall_exists in H0.
    destruct H0. exists (1+ -x)%Z. destruct H. split.
    + apply Rnot_ge_lt in H0. rewrite<-IZR_Q in H0. rewrite Rmult_1_r in H0.
      assert(x-1 = x + -1)%Z by reflexivity. rewrite H1 in H0. clear H1.
      rewrite plus_IZR in H0. apply (Rplus_lt_compat_l (r + IZR 1 + -IZR x)) in H0.
      (** left*)rewrite<-Rplus_assoc in H0. rewrite (Rplus_assoc (r + IZR 1)) in H0.
      rewrite (Rplus_comm (-IZR x)) in H0. rewrite Rplus_opp_r in H0. 
      rewrite Rplus_0_r in H0. assert(-1 = - 1%Z)%Z by reflexivity.
      rewrite H1 in H0. rewrite opp_IZR in H0. rewrite Rplus_assoc in H0.
      rewrite Rplus_opp_r in H0. rewrite Rplus_0_r in H0. 
      (** right*) rewrite (Rplus_comm _ (-r)) in H0. 
      repeat rewrite<-(Rplus_assoc (-r) _ _) in H0. rewrite (Rplus_comm (-r)) in H0.
      rewrite Rplus_opp_r in H0. rewrite Rplus_0_l in H0. rewrite<-opp_IZR in H0.
      rewrite plus_IZR. apply H0.
    + destruct H. 
      * hnf. left. apply (Rplus_lt_compat_l (IZR (1 + - x))) in H. 
        rewrite Rmult_1_r in H. rewrite<-IZR_Q in H. rewrite plus_IZR in H at 2.
        rewrite (Rplus_assoc _ _ (IZR x)) in H. rewrite (Rplus_comm _ (IZR x)) in H.
        rewrite opp_IZR in H. rewrite Rplus_opp_r in H. rewrite Rplus_0_r in H.
        apply H.
      * unfold Rminus. rewrite<-H. rewrite<-IZR_Q. rewrite Rmult_1_r.
        rewrite plus_IZR. rewrite Rplus_assoc. rewrite (Rplus_comm _ (IZR x)).
        rewrite opp_IZR. rewrite Rplus_opp_r. rewrite Rplus_0_r. 
        hnf. right. reflexivity. 
Qed.

  (** We have proved another version in Cauchy.RAbs named R_Archimedian *)
  Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

  Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.

  Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

  Fixpoint Nested_interval (E : R -> Prop) (x y : R) (n : nat) : R * R.
    destruct n eqn : En.
    - apply (x , y).
    - set (Nested_interval E x y n0).
      set (fst p).
      set (snd p).
      apply ((Rif (is_upper_bound E ((r + r0)/2)) ((r + r0) / 2) r),(Rif (is_upper_bound  E ((r + r0)/2)) r0 ((r + r0) / 2) )).
  Defined.
  
  Definition Left_Nested_interval (E : R -> Prop) (x y : R) (n : nat) : R :=
     fst (Nested_interval E x y n).
  
  Definition Right_Nested_interval (E : R -> Prop) (x y : R)(n : nat) : R :=
     snd (Nested_interval E x y n).
     
  Lemma Rle_div2 : forall x y : R , x <= y -> x <= (x + y) / 2.
  Proof.
    intros.
    unfold Rdiv.
    apply Rle_mult_compat_r with 2.
    - rewrite Rpositive_gt_0. apply Rlt_0_2.
    - rewrite Rmult_assoc. rewrite Rinv_l.
      + rewrite Rmult_plus_distr_l.
        rewrite !Rmult_1_r.
        apply Rle_plus_l.
        auto.
      + intro.
        apply (Rlt_irrefl 0).
        rewrite <- H0 at 2.
        apply Rlt_0_2.
  Qed.
  
  Lemma Rge_div2 : forall x y : R , x <= y -> (x + y) / 2 <= y.
  Proof.
    intros.
    unfold Rdiv.
    apply Rle_mult_compat_r with 2.
    - rewrite Rpositive_gt_0. apply Rlt_0_2.
    - rewrite Rmult_assoc. rewrite Rinv_l.
      + rewrite Rmult_plus_distr_l.
        rewrite !Rmult_1_r.
        apply Rle_plus_r.
        auto.
      + intro.
        apply (Rlt_irrefl 0).
        rewrite <- H0 at 2.
        apply Rlt_0_2.
  Qed.
  
  Lemma up_Nested_interval : forall E x y n , x <= y -> fst (Nested_interval E x y n) <= snd (Nested_interval E x y n).
  Proof.
    intros.
    induction n.
    - simpl. auto.
    - remember (Nested_interval E x y n) as p.
      remember (fst p) as r.
      remember (snd p) as r0.
      assert (((Rif (is_upper_bound  E ((r + r0)/2)) ((r + r0) / 2) r),(Rif (is_upper_bound  E ((r + r0)/2)) r0 ((r + r0) / 2) )) = Nested_interval E x y (S n)).
      { simpl. subst. reflexivity. }
      rewrite <- H0.
      destruct (classic (is_upper_bound E ((r + r0) / 2))). 
      * assert (Rif (is_upper_bound E ((r + r0) / 2)) ((r + r0) / 2) r == (r + r0) / 2).
        { apply Rif_left. auto. }
        assert (Rif (is_upper_bound E ((r + r0) / 2)) r0 ((r + r0) / 2) == r0).
        { apply Rif_left. auto. }
        simpl. rewrite H2.
        rewrite H3. apply Rge_div2. auto.
      * assert (Rif (is_upper_bound E ((r + r0) / 2)) ((r + r0) / 2) r == r).
        { apply Rif_right. auto. }
        assert (Rif (is_upper_bound E ((r + r0) / 2)) r0 ((r + r0) / 2) == (r + r0) / 2).
        { apply Rif_right. auto. }
        simpl. rewrite H2.
        rewrite H3. apply Rle_div2. auto. 
  Qed.

  Lemma sub_Nested_interval : forall E x y n , x <= y -> snd (Nested_interval E x y n) - fst(Nested_interval E x y n) <= (y - x) / (2 ^ n).
  Proof.
    intros.
    induction n.
    - simpl. right. unfold Rdiv. rewrite <- Rmult_1_r at 2.
      rewrite Rmult_assoc. rewrite (Rmult_comm 1). rewrite Rinv_l.
      + rewrite Rmult_1_r. reflexivity.
      + apply R1_neq_R0.
    - rewrite <- Nat.add_1_r.
      rewrite Rdef_pow_add.
      unfold Rdiv.
      assert (forall n : nat , ~ 2 ^ n == 0).
      { intros.
        intro.
        apply (Rlt_irrefl 0).
        rewrite <- H0 at 2.
        induction n0.
        - simpl. auto with real.
        - rewrite <- Nat.add_1_r in *.
          rewrite Rdef_pow_add in *.
          apply Rmult_lt_0_compat.
          + apply IHn0.
            apply Rmult_integral in H0.
            destruct H0 ; auto.
            exfalso. apply (Rlt_irrefl 0).
            rewrite <- H0 at 2. 
            admit.
          + admit.
      }
      rewrite Rinv_mult_distr ; auto.
      
  Admitted.
  
  Lemma Left_upper_Nested_interval : forall E x y n1 n2 , x <= y -> 
      (n1 <= n2)%nat -> (Left_Nested_interval E x y n1) <= (Left_Nested_interval E x y n2).
  Proof.
    intros.
    induction H0.
    - right. reflexivity.
    - apply Rle_trans with (Left_Nested_interval E x y m) ; auto.
      clear IHle.
      unfold Left_Nested_interval.
      remember (Nested_interval E x y m) as p.
      remember (fst p) as r.
      remember (snd p) as r0.
      assert (((Rif (is_upper_bound E ((r + r0)/2)) ((r + r0) / 2) r),(Rif (is_upper_bound E ((r + r0)/2)) r0 ((r + r0) / 2) )) = Nested_interval E x y (S m)).
      { simpl. subst. reflexivity. }
      rewrite <- H1.
      destruct (classic (is_upper_bound E ((r + r0) / 2))). 
        * assert (Rif (is_upper_bound E ((r + r0) / 2)) ((r + r0) / 2) r == (r + r0) / 2).
          { apply Rif_left. auto. }
          simpl.
          rewrite H3. apply Rle_div2. subst. apply up_Nested_interval. auto.
        * assert (Rif (is_upper_bound E ((r + r0) / 2)) ((r + r0) / 2) r == r).
          { apply Rif_right. auto. }
          simpl.
          rewrite H3. apply Rle_refl.
  Qed.
  
  Lemma Right_lower_Nested_interval : forall E x y n1 n2, x <= y -> 
      (n1 <= n2)%nat -> Right_Nested_interval E x y n2 <= Right_Nested_interval E x y n1.
  Proof.
    intros.
    induction H0.
    - right. reflexivity.
    - apply Rle_trans with (Right_Nested_interval E x y m) ; auto.
      clear IHle.
      unfold Right_Nested_interval.
      remember (Nested_interval E x y m) as p.
      remember (fst p) as r.
      remember (snd p) as r0.
      assert (((Rif (is_upper_bound E ((r + r0)/2)) ((r + r0) / 2) r),(Rif (is_upper_bound E ((r + r0)/2)) r0 ((r + r0) / 2) )) = Nested_interval E x y (S m)).
      { simpl. subst. reflexivity. }
      rewrite <- H1.
      destruct (classic (is_upper_bound E ((r + r0) / 2))). 
        * assert (Rif (is_upper_bound E ((r + r0) / 2)) r0 ((r + r0) / 2) == r0).
          { apply Rif_left. auto. }
          simpl.
          rewrite H3. apply Rle_refl. 
        * assert (Rif (is_upper_bound E ((r + r0) / 2)) r0 ((r + r0) / 2) == ((r + r0) / 2)).
          { apply Rif_right. auto. }
          simpl.
          rewrite H3. apply Rge_div2. subst. apply up_Nested_interval. auto.
  Qed.

  Theorem completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> exists m:R , is_lub E m .
  Proof.
    pose proof CC_sufficiency.
    intros.
    destruct H0 , H1.
    set (Left_Nested_interval E x0 x).
    set (Right_Nested_interval E x0 x).
    assert (R_seq (fun n r1 => r n == r1)).
    { split.
      - intros. exists (r n). reflexivity.
      - intros. rewrite <- H2 , <- H3. reflexivity.
      - intros. hnf. intros.
        rewrite H2. reflexivity.
    }
    set (Rseq_intro _ H2).
    assert (R_seq (fun n r1 => r0 n == r1)).
    { split.
      - intros. exists (r0 n). reflexivity.
      - intros. rewrite <- H4 , <- H3. reflexivity.
      - intros. hnf. intros.
        rewrite H3. reflexivity.
    }
    set (Rseq_intro _ H3).
    assert (Cauchy_of_R r1).
    { hnf. intros.
       admit. }
    assert (Cauchy_of_R r2).
    { admit. }
    apply H in H4.
    apply H in H5.
    destruct H4 , H5.
    assert (x1 == x2).
    { hnf. admit. }
    exists x1.
    split.
    + admit.
    + intros. admit.
  Admitted.
  (** We have proved another version in Cauchy.RComplete named CC_sufficiency*)
End CauchyR_complete.

Module CauchyAll: VIR_R_ALL.

Include CauchyR.
Module CauchyRSingle : VIR_R_SINGLETON CauchyR := CauchyR.Vex.
Include CauchyRSingle.

End CauchyAll.
