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
Lemma Qabs_lt_eps_iff: forall q1 q2 eps, Qabs (q1 - q2) < eps <-> (q1 - q2 < eps /\ q2 - q1 < eps).
Admitted.
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


Theorem Real_density_of_Q:
forall A B, (B<A)%R -> exists q, ((B<inject_Q q) /\ (inject_Q q< A))%R.
Proof.

(* forall dlt,  exists N,  An > Bn + dlt

for dlt/4
exists N1 N2
|An - Am| < dlt/4
|Bn - Bm| < dlt/4

-> EXISTS n0 m>=n0
Am > Bm + dlt
An0 - dlt/4 < Am < An0 + dlt/4
Bn0 - dlt/4 < Bm < Bn0 + dlt/4


Bm < Bn0 + dlt/4 < An0 - 3/4 dlt < (** An0 - dlt/2 **) < An0 - dlt/4 < Am

Take q = An0 - dlt/2
forall m>=N0
Am > An0-dlt/2 > Bm
QED.

*)

Admitted.



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
Admitted.


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
  destruct (HS (inject_Q (1#(Pos.of_nat N)))) as [M HM]. { admit. }
  clear HS.
  exists (max (S N) (S M)).
  intros.

  assert (Em1: (m1 <> 0)%nat). { intros C. rewrite C in H. omega. }
  assert (Em2: (m2 <> 0)%nat). { intros C. rewrite C in H0. omega. }
  assert (EN: (N<>0)%nat). { intros C. rewrite C in HeqN.
  assert ((2 * Qceiling (/ eps) + 1)>0)%Z.
    { admit. } admit. }
  apply Nat.max_lub_lt_iff in H.
  apply Nat.max_lub_lt_iff in H0.
  apply Qabs_lt_eps_iff.
  destruct (Rseq_exists m1) as [Am1 HAm1],(Rseq_exists m2) as [Am2 HAm2].

  split.

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
  admit. }


{ assert (E1: (inject_Q (q2- q1) < Am2 - (Am1 - inject_Q (1#Pos.of_nat m1)))%R).
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
admit. }


Admitted.



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
  destruct (Cauchy_Q_limit RC (epsq*(1#2))) as [M HM]. admit.
  assert ( exists N, forall n : nat,
     (n >= N)%nat -> forall A : Real, RS n A -> 
     forall q : Q,
     match RC with
     | Real_intro A0 _ => A0
     end n q -> (Rabs (A - inject_Q q) < inject_Q (epsq * (1 # 2)))%R).
    { exists (2*Z.to_nat((Qceiling (/epsq)%Q)+1))%nat. intros. rewrite HeqRC in H3. hnf in H3.
      pose proof (H3 _ H2). clear H3.
      assert (E1: (n<>0)%nat). { admit. }
      apply Rabs_lt_iff. admit. split.
      - apply (Rlt_le_trans _ 0)%R. admit.
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
            admit. }
      apply (Rlt_trans _ _ _ Et4 Et3). }
    destruct H1 as [N HN].

  exists (max (S N) (S M)). intros.
  destruct A as [A HA].
  destruct RC as [RC HRC].
  destruct (Cauchy_exists _ HRC n) as [q Hq].
  apply (Rle_lt_trans _ (Rabs ((Real_intro A HA) - inject_Q q) + Rabs ((Real_intro RC HRC) - inject_Q q)))%R.
  { rewrite (Rabs_Rminus (Real_intro RC HRC)).
    assert (Real_intro A HA - (Real_intro RC HRC) == (Real_intro A HA - inject_Q q) + (inject_Q q - (Real_intro RC HRC)))%R by ring.
    rewrite H3. apply Rabs_triangle. }
  apply (Rlt_trans _ (inject_Q epsq)).
  - assert (Et: (inject_Q epsq == inject_Q (epsq * (1 # 2)) +inject_Q (epsq * (1 # 2)))%R).
     { admit. }
    rewrite Et.
    apply Rle_lt_plus_compat.
    + apply Rlt_le_weak. apply (HN n). admit. auto. auto.
    + apply (HM n). admit. auto.
  - auto.
Admitted.

