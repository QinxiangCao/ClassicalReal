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
From CReal Require Import QArith_ext.Inject_lemmas.
From CReal.Cauchy Require Import RBase.
From CReal.Cauchy Require Import RArith.
From CReal.Cauchy Require Import RSign.
From CReal.Cauchy Require Import ROrder.
From CReal.Cauchy Require Import RAbs.
From CReal.Cauchy Require Import RFloor.
From CReal.Cauchy Require Import RFunc.

(* Helping Lemmas *)

Lemma  inject_Q_minus : forall q1 q2, 
(inject_Q (q1 - q2) == inject_Q q1 - inject_Q q2)%R.
Proof. intros. unfold Rminus. unfold Qminus.
  rewrite inject_Q_plus. rewrite inject_Q_opp. reflexivity.
Qed.


(* Definition of R_seq*)
Class R_seq (RS: nat -> Real -> Prop) : Prop := {
  Rseq_exists : forall (n:nat), exists A1, RS n A1;
  Rseq_unique : forall (n:nat)  A1 A2,
      RS n A1 -> RS n A2 -> (A1 == A2)%R;
  Rseq_proper: forall n, Proper (Real_equiv ==> iff) (RS n);
}.


Inductive Real_seq : Type :=
| Rseq_intro (RS : nat -> Real -> Prop) (H: R_seq RS).
Lemma eps_divide_4_positive: forall (eps:Q), 0 < eps -> eps * (1 # 4) > 0.
Proof. intros. unfold Qmult. unfold Qlt. simpl.
    rewrite <- Zmult_assoc. simpl. apply H.
Qed.

Theorem take_max_N_0604: forall N1 N2 N3 (P Q R:nat->Prop), 
 (forall n, (n>=N1)%nat -> P n) ->
 (forall m,(m>=N2)%nat -> Q m) ->
 (forall m,(m>=N3)%nat -> R m) ->
  exists N, ((forall n, (n>=N)%nat -> P n )/\ 
              (forall n, (n>=N)%nat -> Q n )/\
            (forall n, (n>=N)%nat -> R n)).
Proof. intros.
  exists (max (max N1 N2) N3).
  remember (max (max N1 N2) N3) as N.
  assert (E3: (N>=N3)%nat). { rewrite HeqN. apply Nat.le_max_r. }
  assert (E0: (N>=(max N1 N2))%nat). { rewrite HeqN. apply Nat.le_max_l. }
  pose proof (Nat.max_lub_r _ _ _ E0) as E2.
  pose proof (Nat.max_lub_l _ _ _ E0) as E1.
  split.
  - intros. apply H. omega.
  - split.
  + intros. apply H0. omega.
  + intros. apply H1. omega.
Qed.

Theorem Real_density_of_Q:
forall A B, (B<A)%R -> exists q, ((B<inject_Q q) /\ (inject_Q q< A))%R.
Proof.
intros. hnf in H. destruct A as [A HA], B as [B HB].
destruct H as [dlt [Hdlt [N1 HN1]]].
destruct (Cauchy_Q_limit (Real_intro A HA) _ (eps_divide_4_positive _ Hdlt)) as [N2 HN2].
destruct (Cauchy_Q_limit (Real_intro B HB) _ (eps_divide_4_positive _ Hdlt)) as [N3 HN3].
destruct (take_max_N_0604 _ _ _ _ _ _ HN1 HN2 HN3) as [N [H1 [H2 H3]]].
clear HN1. clear HN2. clear HN3.
clear N1. clear N2. clear N3.

destruct (Cauchy_exists _ HA N) as [qNA HqNA].
destruct (Cauchy_exists _ HB N) as [qNB HqNB].
exists (qNA - dlt*(1#2)).



split.
- apply (Rlt_trans _ ((inject_Q (qNB + dlt*(1#4))))).
  + apply (Rlt_plus_compat_r _ _ (- inject_Q qNB)).
    rewrite <- inject_Q_opp. rewrite <- inject_Q_plus.
    assert (qNB + dlt * (1 # 4) + - qNB == dlt * (1 # 4)) by ring.
    rewrite H. rewrite inject_Q_opp.
    pose proof (H3 N (le_refl _) qNB HqNB).
    apply Rabs_lt_iff in H0. apply (proj2 H0).
    apply Qlt_Rlt. auto using eps_divide_4_positive.
  + apply (Rle_lt_trans _ ((inject_Q (qNA - dlt*(3#4))))).
  * apply (Rle_plus_compat_r _ _ (inject_Q (dlt * (3 # 4)))).
    repeat rewrite <- inject_Q_plus. apply Qle_Rle.
    unfold Qminus. repeat rewrite <- Qplus_assoc.
    repeat rewrite <- Qmult_plus_distr_r.
    assert ((1 # 4) + (3 # 4) == 1) by ring. rewrite H.
    assert ((- (dlt * (3 # 4)) + dlt * (3 # 4)) == 0) by ring. rewrite H0.
    rewrite Qplus_0_r. rewrite Qmult_1_r.
    apply (Qplus_le_l _ _ (-qNB)). assert ( qNB + dlt + - qNB  == dlt) by ring.
    rewrite H4.
    pose proof (H1 N (le_refl _) (qNA-qNB)). apply H5.
    hnf. intros. hnf in H7. rewrite (Cauchy_unique _ HA _ _ _ HqNA H6).
    rewrite (H7 qNB HqNB). ring.
  * apply Qlt_Rlt. unfold Qminus. apply Qlt_minus_iff.
    assert (qNA + - (dlt * (1 # 2)) + - (qNA + - (dlt * (3 # 4))) == dlt*(3#4)+dlt*(-(1#2))) by ring.
    rewrite H. rewrite  <- Qmult_plus_distr_r.
    assert (((3 # 4) + - (1 # 2)) == 1#4) by ring.
    rewrite H0. apply eps_divide_4_positive. auto.
- apply (Rlt_trans _ ((inject_Q (qNA - dlt*(1#4))))).
  + apply Qlt_Rlt. unfold Qminus. apply Qlt_minus_iff.
    assert (qNA + - (dlt * (1 # 4)) + - (qNA + - (dlt * (1 # 2))) == dlt*(1#2)+dlt*(-(1#4))) by ring.
    rewrite H. rewrite  <- Qmult_plus_distr_r.
    assert (((1 # 2) + - (1 # 4)) == 1#4) by ring.
    rewrite H0. apply eps_divide_4_positive. auto.
  + apply (Rlt_plus_compat_r _ _ (- inject_Q qNA)).
    rewrite <- inject_Q_opp. rewrite <- inject_Q_plus.
    assert (qNA - dlt * (1 # 4) + - qNA == - (dlt * (1 # 4))) by ring.
    rewrite H. repeat rewrite inject_Q_opp.
    pose proof (H2 N (le_refl _) qNA HqNA).
    apply Rabs_lt_iff in H0. apply (proj1 H0).
    apply Qlt_Rlt. auto using eps_divide_4_positive.
Qed.



Definition Rlimit (Rseq:Real_seq) (Lim:Real):Prop:=
forall Eps:Real, (0 < Eps)%R -> exists N, forall n,
(n>=N)%nat -> forall A, 
(match Rseq with Rseq_intro RS _ => RS end) n A -> (Rabs (A - Lim) < Eps)%R.

Definition Cauchy_of_R (Rseq:Real_seq):Prop:=
forall Eps:Real, (0 < Eps)%R -> exists N, forall n m,
(n>=N)%nat -> (m>=N)%nat -> forall A B, 
(match Rseq with Rseq_intro RS _ => RS end) n A ->
(match Rseq with Rseq_intro RS _ => RS end) m B ->
 (Rabs (A - B) < Eps)%R.

Theorem CC_necessity: forall (Rseq:Real_seq), (exists Lim:Real, Rlimit Rseq Lim)
 -> Cauchy_of_R Rseq.
Proof. intros. destruct H as [Lim H]. hnf in H. hnf.
  intros. assert (0< Eps*(inject_Q (1#2)))%R. 
  { rewrite <- (Rmult_0_l (inject_Q (1 # 2))%R).
  apply Rlt_mult_r. { hnf. exists (1#4). split. reflexivity. exists O. intros.
   unfold inject_Q in H2. rewrite H2. intros C. discriminate C. } auto. }
  apply H in H1. clear H. destruct H1 as [N HN].
  exists N. intros.
  pose proof (HN _ H _ H2).
  pose proof (HN _ H1 _ H3).
  pose proof (Rlt_plus_compat _ _ _ _ H4 H5).
  apply (Rle_lt_trans _ ((Rabs (A - Lim) + Rabs (B - Lim))%R)).
  rewrite (Rabs_Rminus B Lim).
  assert (Et:(A-B==(A-Lim) +(Lim-B))%R) by ring.
  rewrite Et. apply Rabs_triangle.
  assert (Et: (Eps == Eps * inject_Q (1 # 2) + Eps * inject_Q (1 # 2))%R).
    { rewrite <- Rmult_plus_distr_r. rewrite <- inject_Q_plus.
      assert ((1 # 2) + (1 # 2) == 1) by ring. rewrite H7.
      rewrite Rmult_1_r. reflexivity. }
  rewrite Et. auto.
Qed.


Lemma CCfunlemma1: forall (RS : nat -> Real -> Prop),
R_seq RS-> forall n : nat, exists q : Q,   forall A : Real,  RS n A ->
  forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z -> q == z # Pos.of_nat n.
Proof.
intros. destruct H. destruct (Rseq_exists0 n).
  destruct (Rfloor_exists  (x * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].
  exists (z # Pos.of_nat (n)). intros.
  rewrite (Rseq_unique0 _ _ _ H H0) in Hz.
  rewrite (Rfloor_unique _ _ _ Hz H1). reflexivity.
Qed.


Lemma CCfunlemma2: forall (RS : nat -> Real -> Prop),
R_seq RS->forall (n : nat) (q1 q2 : Q), (forall A : Real,  RS n A ->
 forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z -> q1 == z # Pos.of_nat n) ->
(forall A : Real,  RS n A ->
 forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z -> q2 == z # Pos.of_nat n) ->
q1 == q2.
Proof.
  intros. destruct H. destruct (Rseq_exists0 n).
  destruct (Rfloor_exists (x * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].
  assert (q1 == z # Pos.of_nat n). { apply (H0 x). auto. auto. }
  assert (q2 == z # Pos.of_nat n). { apply (H1 x). auto. auto. }
  rewrite H2,H3. reflexivity.
Qed.

Lemma CCfunlemma3: forall (RS : nat -> Real -> Prop),
R_seq RS -> forall (p q : Q) (n : nat),
p == q -> (forall A : Real,  RS n A ->
 forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z -> p == z # Pos.of_nat n) ->
forall A : Real, RS n A ->
forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z -> q == z # Pos.of_nat n.
Proof.
  intros.
  rewrite <- (H1 A H2). rewrite H0. ring. auto.
Qed.

(* We prove that the sequence construted is a cauchy sequence of rational*)

Lemma Real_constr_help1: forall A z m q, (m<>0)%nat ->
     Rfloor (A * inject_Q (inject_Z (Z.of_nat m))) z -> q == z # Pos.of_nat m
    -> (inject_Q q <= A)%R.
Proof. intros A z m q E. intros.
  apply Rfloor_iff in H. destruct H.
  apply (Rle_mult_l_compat _ _ (inject_Q (inject_Z (Z.of_nat m)))).
  apply Rpositive_gt_0. apply Qlt_Rlt. assert (0==inject_Z 0) by ring.
  rewrite H2. rewrite <- Zlt_Qlt. omega.
  rewrite H0. rewrite Qmake_Qdiv. rewrite <- inject_Q_mult.
  assert (Et: ((Z.of_nat m)) = (Z.pos (Pos.of_nat m))).
    { symmetry. apply Inject_2.  omega. }
  rewrite <- Et.
  assert (Et1: (inject_Z (Z.of_nat m) * (inject_Z z / inject_Z (Z.of_nat m))) == inject_Z z).
    { field. intros C.
      apply inject_Z_nonzero in E. contradiction. }
  rewrite Et1. rewrite Rmult_comm. auto.
Qed.
Lemma Real_constr_help2: forall A z m q, (m<>0)%nat ->
     Rfloor (A * inject_Q (inject_Z (Z.of_nat m))) z -> q == z # Pos.of_nat m
    -> (inject_Q q > A - inject_Q (1# Pos.of_nat m))%R.
Proof. intros A z m q E. intros.
  apply Rfloor_iff in H. destruct H.
  apply (Rlt_mult_compat_r _ _ (inject_Q (inject_Z (Z.of_nat m)))).
  apply Rpositive_gt_0. apply Qlt_Rlt. assert (0==inject_Z 0) by ring.
  rewrite H2. rewrite <- Zlt_Qlt. omega.
  rewrite H0. repeat rewrite Qmake_Qdiv. unfold Rminus. repeat unfold Qdiv.
  rewrite Rmult_plus_distr_l. rewrite <- Ropp_mult_distr.
  repeat rewrite <- inject_Q_mult.
  assert (Et: ((Z.of_nat m)) = (Z.pos (Pos.of_nat m))).
    { symmetry. apply Inject_2.  omega. }
  rewrite <- Et.
  assert (Et1: inject_Z 1 * / inject_Z (Z.of_nat m) * inject_Z (Z.of_nat m) == inject_Z 1).
    { field. intros C.
      apply inject_Z_nonzero in E. contradiction. }
  assert (Et2: inject_Z z * / inject_Z (Z.of_nat m) * inject_Z (Z.of_nat m) == inject_Z z).
    { field. intros C.
      apply inject_Z_nonzero in E. contradiction. }
  rewrite Et1. rewrite Et2.
  assert (Et3:  (- inject_Q (inject_Z 1) == - (1))%R). { reflexivity. }
  rewrite Et3. auto.
Qed.
Lemma CCfun_is_Cauchy: forall (RS : nat -> Real -> Prop)
  (H: R_seq RS) , Cauchy_of_R (Rseq_intro RS H) ->
  forall eps : Q, 0< eps -> exists n : nat,   forall m1 m2 : nat,  (m1 > n)%nat ->  (m2 > n)%nat ->  forall q1 q2 : Q,
  (forall A : Real, RS m1 A -> forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat m1))) z -> q1 == z # Pos.of_nat m1) ->
  (forall A : Real, RS m2 A -> forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat m2))) z -> q2 == z # Pos.of_nat m2) ->
  Qabs (q1 - q2) < eps.
Proof. 
  intros RS. intros [Rseq_exists Rseq_unique Rseq_proper] HS eps Heps.

  remember (Z.to_nat (2*(Qceiling (/eps)%Q)+1)) as N.


  assert (T1:0 == inject_Z 0) by ring.
  destruct (HS (inject_Q (1#(Pos.of_nat N)))) as [M HM]. 
  { apply Qlt_Rlt. rewrite (Qmake_Qdiv 1). unfold Qdiv. rewrite Qmult_1_l. apply Qlt_shift_inv_l.
    rewrite T1. rewrite <- Zlt_Qlt.
    assert (T0:((Z.pos (Pos.of_nat N))>0)%Z). { apply Zgt_pos_0. }
    omega. rewrite Qmult_0_l. reflexivity. }
  clear HS.
  exists (max (N) (M)).
  intros.
  assert (Eeps': /eps>0). { apply Qinv_lt_0_compat. auto. }
  assert (Em1: (m1 <> 0)%nat). { intros C. rewrite C in H. omega. }
  assert (Em2: (m2 <> 0)%nat). { intros C. rewrite C in H0. omega. }
  assert (Eepsceil: ((2 * Qceiling (/ eps) + 1)>0)%Z).
    { apply Z.lt_gt. apply (Z.lt_le_trans _ (1)).
      omega. assert (0<= Qceiling (/ eps) )%Z.
      { assert (0 = Qceiling 0)%Z by reflexivity. rewrite H3.
        apply Qceiling_resp_le. apply Qlt_le_weak. apply Qinv_lt_0_compat. auto. }
      omega. }
  assert (EN: (N<>0)%nat). { intros C. rewrite C in HeqN.
    apply Z.gt_lt in Eepsceil. assert (0<=0)%Z by omega.
    apply (Z2Nat.inj_lt 0 (2 * Qceiling (/ eps) + 1) H3 (Zlt_le_weak _ _ Eepsceil)) in Eepsceil.
    assert (Z.to_nat 0 = 0)%nat by omega. rewrite H4 in Eepsceil. omega. }

  assert (EN0:(0 < Z.pos (Pos.of_nat N))%Z).
  { apply Z.gt_lt. apply Zgt_pos_0. }
  apply Nat.max_lub_lt_iff in H.
  apply Nat.max_lub_lt_iff in H0.

  assert (Em3:(Z.pos (Pos.of_nat m1) > Z.pos (Pos.of_nat N))%Z).
  { rewrite (Inject_2 _ Em1).  rewrite (Inject_2 _ EN). omega. }
  assert (Em4:(Z.pos (Pos.of_nat m2) > Z.pos (Pos.of_nat N))%Z).
  { rewrite (Inject_2 _ Em2).  rewrite (Inject_2 _ EN). omega. }


  assert (EN1: / inject_Z (Z.pos (Pos.of_nat N)) * (2 # 1) < eps).

  { rewrite Qmult_comm. apply Qlt_shift_div_r. rewrite T1. rewrite <- Zlt_Qlt. omega.
    apply (Qmult_lt_r _ _ (/eps));auto.
    assert (Et1: eps * inject_Z (Z.pos (Pos.of_nat N)) * / eps ==inject_Z (Z.pos (Pos.of_nat N)) ).
      { field. intros C. rewrite C in Heps. apply Qlt_irrefl in Heps. auto. }
    rewrite Et1. rewrite Inject_2;auto. rewrite HeqN.
    rewrite Z2Nat.id. pose proof (Qle_ceiling (/eps)).
    assert (inject_Z 2 >0) by auto.
    apply (proj2 (Qmult_le_l _ _ _ H4)) in H3.
    apply (Qle_lt_trans _ _ _ H3). rewrite (inject_Z_plus _ 1).
    rewrite <- Qplus_0_r.  rewrite (inject_Z_mult). apply Qplus_lt_r. reflexivity.
    omega. }
  apply Qabs_Qlt_condition.
  destruct (Rseq_exists m1) as [Am1 HAm1],(Rseq_exists m2) as [Am2 HAm2].
  split.

{ rewrite <- (Qopp_involutive (q1 - q2)). apply Qopp_lt_compat.
  assert (T:- (q1 - q2) == q2-q1) by ring. rewrite T.
  assert (E1: (inject_Q (q2- q1) < Am2 - (Am1 - inject_Q (1#Pos.of_nat m1)))%R).
    { rewrite inject_Q_minus. apply Rle_lt_plus_compat.
      - destruct (Rfloor_exists (Am2 * inject_Q (inject_Z (Z.of_nat m2)))) as [z Hz].
        pose proof (Real_constr_help1 Am2 z m2 q2 Em2 Hz).
        apply H3. apply (H2 Am2). auto. auto.
     - apply Ropp_lt_compat.
       destruct (Rfloor_exists (Am1 * inject_Q (inject_Z (Z.of_nat m1)))) as [z Hz].
       apply (Real_constr_help2 Am1 z m1 q1).
       auto. auto. auto. apply (H1 Am1). auto. auto.
    }
  assert (E2: (Rabs (Am2 - Am1) < inject_Q (1 # Pos.of_nat N))%R).
    { apply (HM m2 m1). omega. omega. auto. auto. }
  apply Qlt_Rlt. apply (Rlt_trans _ (inject_Q (1 # Pos.of_nat N) + inject_Q (1 # Pos.of_nat m1))%R).
  - apply (Rlt_trans _ (Am2 - (Am1 - inject_Q (1 # Pos.of_nat m1)))%R).
    auto. assert ((Am2 - (Am1 - inject_Q (1 # Pos.of_nat m1)) == Am2 - Am1 + inject_Q (1 # Pos.of_nat m1)))%R by ring.
    rewrite H3. apply Rlt_plus_r. apply Rabs_lt_iff in E2. destruct E2. apply H5.
    apply Qlt_Rlt. rewrite (Qmake_Qdiv 1). apply Qinv_lt_0_compat.
    assert (0==inject_Z 0)%Q by ring. rewrite H5. rewrite <- Zlt_Qlt.
    rewrite Inject_2. omega. auto. 
  - rewrite <- inject_Q_plus. apply Qlt_Rlt.
    { repeat rewrite Qmake_Qdiv. repeat unfold Qdiv.
      repeat rewrite Qmult_1_l.
      apply (Qlt_trans _ (/ inject_Z (Z.pos (Pos.of_nat N))+ / inject_Z (Z.pos (Pos.of_nat N)))).
      { apply Qplus_lt_r. apply Qlt_shift_inv_r.
        rewrite T1. rewrite <- Zlt_Qlt. omega.
        rewrite Qmult_comm. apply Qlt_shift_div_l.
        rewrite T1. rewrite <- Zlt_Qlt. omega. rewrite Qmult_1_l.
        rewrite <- Zlt_Qlt. repeat rewrite Inject_2. omega. omega. omega. }
      { rewrite <- (Qmult_1_r (/ inject_Z (Z.pos (Pos.of_nat N)))).
        rewrite <- Qmult_plus_distr_r. assert ((1 + 1==(2#1))%Q) by ring.
        rewrite H3. auto. }
     }
}

{ (*q1 - q2 < Sm1 - Sm2 + 1/m2 < 1/m2 + eps < 2eps*)
  assert (E1: (inject_Q (q1 - q2) < Am1 - (Am2 - inject_Q (1#Pos.of_nat m2)))%R).
  { rewrite inject_Q_minus. apply Rle_lt_plus_compat.
    - destruct (Rfloor_exists (Am1 * inject_Q (inject_Z (Z.of_nat m1)))) as [z Hz].
      pose proof (Real_constr_help1 Am1 z m1 q1 Em1 Hz).
      apply H3. apply (H1 Am1). auto. auto.
   - apply Ropp_lt_compat.
     destruct (Rfloor_exists (Am2 * inject_Q (inject_Z (Z.of_nat m2)))) as [z Hz].
     apply (Real_constr_help2 Am2 z m2 q2).
     auto. auto. auto. apply (H2 Am2). auto. auto.
  }
  assert (E2: (Rabs (Am1 - Am2) < inject_Q (1 # Pos.of_nat N))%R).
    { apply (HM m1 m2). omega. omega. auto. auto. }
  apply Qlt_Rlt. apply (Rlt_trans _ (inject_Q (1 # Pos.of_nat N) + inject_Q (1 # Pos.of_nat m2))%R).
  - apply (Rlt_trans _ (Am1 - (Am2 - inject_Q (1 # Pos.of_nat m2)))%R).
    auto. assert ((Am1 - (Am2 - inject_Q (1 # Pos.of_nat m2)) == Am1 - Am2 + inject_Q (1 # Pos.of_nat m2)))%R by ring.
    rewrite H3. apply Rlt_plus_r. apply Rabs_lt_iff in E2. destruct E2. apply H5.
    apply Qlt_Rlt. rewrite (Qmake_Qdiv 1). apply Qinv_lt_0_compat.
    assert (0==inject_Z 0)%Q by ring. rewrite H5. rewrite <- Zlt_Qlt.
    rewrite Inject_2. omega. auto. 
  - rewrite <- inject_Q_plus. apply Qlt_Rlt.
    { repeat rewrite Qmake_Qdiv. repeat unfold Qdiv.
      repeat rewrite Qmult_1_l.
      apply (Qlt_trans _ (/ inject_Z (Z.pos (Pos.of_nat N))+ / inject_Z (Z.pos (Pos.of_nat N)))).
      { apply Qplus_lt_r. apply Qlt_shift_inv_r.
        rewrite T1. rewrite <- Zlt_Qlt. omega.
        rewrite Qmult_comm. apply Qlt_shift_div_l.
        rewrite T1. rewrite <- Zlt_Qlt. omega. rewrite Qmult_1_l.
        rewrite <- Zlt_Qlt. repeat rewrite Inject_2. omega. omega. omega. }
      { rewrite <- (Qmult_1_r (/ inject_Z (Z.pos (Pos.of_nat N)))).
        rewrite <- Qmult_plus_distr_r. assert ((1 + 1==(2#1))%Q) by ring.
        rewrite H3. auto. }
     } }
Qed.



Definition RCCFun: {X: Real_seq| (Cauchy_of_R X)}%R -> Real.
intros. destruct X as [Rseq HS]. destruct Rseq.
  apply (Real_intro (fun n q => forall A, RS n A -> forall z,
          (Rfloor (A * (inject_Q (inject_Z (Z.of_nat (n)%nat)))) z) -> 
        q == z # (Pos.of_nat (n)%nat))).
split.
- apply CCfunlemma1. auto.
- apply CCfunlemma2. auto.
- apply CCfunlemma3. auto.
- apply (CCfun_is_Cauchy RS H HS).
Defined.



(* We prove that the constructed real is the limit *)



Theorem CC_sufficiency: forall (Rseq:Real_seq),
 Cauchy_of_R Rseq -> (exists Lim:Real, Rlimit Rseq Lim).
Proof. intros.
  exists (RCCFun (exist _ Rseq H)). hnf.
  remember (RCCFun (exist Cauchy_of_R Rseq H)) as RC.
  destruct Rseq as [RS HRS].
  intros.
  pose proof (Real_density_of_Q _ _ H0). destruct H1 as [epsq [Hepsq Hepsq2]].
  apply Qlt_Rlt in Hepsq.
  destruct (Cauchy_Q_limit RC (epsq*(1#2))) as [M HM]. apply eps_divide_2_positive. auto.
  assert (T1:0 == inject_Z 0) by ring.
  assert (Eepsq': /epsq>0). { apply Qinv_lt_0_compat. auto. }
  assert (Eepsceil: ((2 * Qceiling (/ epsq) + 1)>0)%Z).
    { apply Z.lt_gt. apply (Z.lt_le_trans _ (1)).
      omega. assert (0<= Qceiling (/ epsq) )%Z.
      { assert (0 = Qceiling 0)%Z by reflexivity. rewrite H1.
        apply Qceiling_resp_le. apply Qlt_le_weak. apply Qinv_lt_0_compat. auto. }
      omega. }

  assert ( exists N, forall n : nat,
     (n >= N)%nat -> forall A : Real, RS n A -> 
     forall q : Q,
     match RC with
     | Real_intro A0 _ => A0
     end n q -> (Rabs (A - inject_Q q) < inject_Q (epsq * (1 # 2)))%R).
    { exists (2*Z.to_nat((Qceiling (/epsq)%Q)+1))%nat. intros. rewrite HeqRC in H3. hnf in H3.
      pose proof (H3 _ H2). clear H3.
      assert (E0:(n<>0)%nat). { intros C.
      rewrite C in H1.
      destruct (classic (2 * Z.to_nat (Qceiling (/ epsq) + 1) = 0)%nat).
      { apply mult_is_O in H3. destruct H3. omega. 
        assert (Et4: (0 <= Qceiling (/ epsq))%Z). 
      { assert (0 = Qceiling 0)%Z by reflexivity. rewrite H5.
        apply Qceiling_resp_le. apply Qlt_le_weak. apply Qinv_lt_0_compat. auto. }
        assert (Et5: (0<=1)%Z) by omega.
        rewrite (Z2Nat.inj_add _ _ Et4 Et5) in H3.
        assert (Et8: (Z.to_nat 1 = 1)%nat) by reflexivity.
        rewrite Et8 in H3. omega. }
        omega. }

      apply Rabs_lt_iff. { apply Qlt_Rlt. apply eps_divide_2_positive. auto. } split.
      - apply (Rlt_le_trans _ 0)%R. { rewrite (Ropp_involutive 0). apply Ropp_lt_compat.
           assert (-0 == (0))%R by ring. assert (0==inject_Q 0)%R by reflexivity.
          rewrite H3,H5. apply Qlt_Rlt. apply eps_divide_2_positive. auto. } 
        apply (Rle_plus_compat_r 0 _ (inject_Q q)).
        rewrite Rplus_0_l. assert (Et: (A - inject_Q q + inject_Q q == A)%R) by ring.
        rewrite Et. destruct (Rfloor_exists (A * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].
        apply (Real_constr_help1 A z n). omega. auto. apply H4. auto.
      - apply (Rlt_plus_compat_r _ _ (inject_Q q - inject_Q (epsq * (1 # 2)))).
        assert (Et1: (A - inject_Q q + (inject_Q q - inject_Q (epsq * (1 # 2)))
                      == A - inject_Q (epsq *(1#2)))%R) by ring.
        assert (Et2:  (inject_Q (epsq * (1 # 2)) + (inject_Q q - inject_Q (epsq * (1 # 2))) == inject_Q q)%R) by ring.
        rewrite Et2,Et1.
        assert (Et3:  (inject_Q q > A - inject_Q (1# Pos.of_nat n))%R).
          { destruct (Rfloor_exists (A * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz]. 
            apply (Real_constr_help2 _ z). auto. auto. auto. }
        assert (Et4: (A - inject_Q (1 # Pos.of_nat n) > A - inject_Q (epsq * (1 # 2)))%R).
          { unfold Rminus. apply Rlt_plus_l. apply Ropp_lt_compat. apply Qlt_Rlt.
            rewrite Qmake_Qdiv. unfold Qdiv. rewrite Qmult_1_l.
            apply Qlt_shift_inv_r. rewrite Inject_2. rewrite T1. rewrite <- Zlt_Qlt. omega. omega.
            apply (Qmult_lt_r _ _ (inject_Z 2 * (/epsq))).
                apply Qlt_shift_div_l. auto. rewrite Qmult_0_l. reflexivity.
                assert (Te1: epsq * (1 # 2) * inject_Z (Z.pos (Pos.of_nat n)) * (inject_Z 2 * / epsq) ==inject_Z (Z.pos (Pos.of_nat n)) ).
                  { field. intros C. rewrite C in Hepsq. apply Qlt_irrefl in Hepsq. auto. }
                rewrite Te1. rewrite Inject_2;auto. apply (Qlt_le_trans _ (inject_Z (Z.of_nat (2 * Z.to_nat (Qceiling (/ epsq) + 1))))).
                  { apply (Qle_lt_trans _ (inject_Z (Z.of_nat (2 * Z.to_nat (Qceiling (/ epsq)))))).
                    { rewrite Qmult_1_l. rewrite Nat2Z.inj_mul. rewrite inject_Z_mult.
                      apply Qmult_le_l. reflexivity. rewrite Z2Nat.id. apply (Qle_ceiling (/epsq)).
                      pose proof (Qlt_le_weak _ _ Eepsq'). apply (Qceiling_resp_le _ _ H3). }
                    { rewrite <- Zlt_Qlt. apply inj_lt. apply mult_lt_compat_l.
                      apply Z2Nat.inj_lt. pose proof (Qlt_le_weak _ _ Eepsq'). apply (Qceiling_resp_le _ _ H3).
                      pose proof (Qlt_le_weak _ _ Eepsq'). pose proof (Qceiling_resp_le _ _ H3). omega. omega. omega.
                      }
                  }
            rewrite <- Zle_Qle. apply inj_le. auto.
          }
      apply (Rlt_trans _ _ _ Et4 Et3). }
    destruct H1 as [N HN].

  exists (max (S N) (S M)). intros.
  apply Nat.max_lub_lt_iff in H1.
  destruct A as [A HA].
  destruct RC as [RC HRC].
  destruct (Cauchy_exists _ HRC n) as [q Hq].
  apply (Rle_lt_trans _ (Rabs ((Real_intro A HA) - inject_Q q) + Rabs ((Real_intro RC HRC) - inject_Q q)))%R.
  { rewrite (Rabs_Rminus (Real_intro RC HRC)).
    assert (Real_intro A HA - (Real_intro RC HRC) == (Real_intro A HA - inject_Q q) + (inject_Q q - (Real_intro RC HRC)))%R by ring.
    rewrite H3. apply Rabs_triangle. }
  apply (Rlt_trans _ (inject_Q epsq)).
  - assert (Et: (inject_Q epsq == inject_Q (epsq * (1 # 2)) +inject_Q (epsq * (1 # 2)))%R).
     { rewrite <- inject_Q_plus. assert (epsq == (epsq * (1 # 2) + epsq * (1 # 2))) by ring.
      rewrite <- H3. reflexivity. }
    rewrite Et.
    apply Rle_lt_plus_compat.
    + apply Rlt_le_weak. apply (HN n). omega. auto. auto.
    + apply (HM n). omega. auto.
  - auto.
Qed.