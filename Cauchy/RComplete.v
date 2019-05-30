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
(*
destruct Am1 as [Am1 HAm1R]. destruct Am2 as [Am2 HAm2R].
destruct (Cauchy_exists _ HAm1R m1) as [qm1 Hqm1].
destruct (Cauchy_exists _ HAm2R m2) as [qm2 Hqm2]. *)
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
  { apply (Rlt_trans _ (Am1 - (Am2 - inject_Q (1 # Pos.of_nat m2)))%R).
    auto. assert ((Am1 - (Am2 - inject_Q (1 # Pos.of_nat m2)) == Am1 - Am2 + inject_Q (1 # Pos.of_nat m2)))%R by ring.
    rewrite H3. apply Rlt_plus_r. apply Rabs_lt_iff in E2. destruct E2. apply H5.
    apply Qlt_Rlt. rewrite (Qmake_Qdiv 1). apply Qinv_lt_0_compat.
    assert (0==inject_Z 0)%Q by ring. rewrite H5. rewrite <- Zlt_Qlt.
    rewrite Inject_2. omega. auto. }
  rewrite <- inject_Q_plus. apply Qlt_Rlt.
  admit.







(** Idea: scaling of RFLOOR 

q1 - q2 < Sm1 - Sm2 + 1/m2 < 1/m2 + eps < 2eps

q2 - q1 < Sm2 - Sm1 + 1/m1 < ... < 2eps


*)
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



  (*
  use similar proof of RFUN_correct to prove |inject_Q (RC n) - (RS n)|<eps%R
                                          i.e. |Rfloor((RS n) * n)/n - (RS n)| < eps%R









Lemma CC_sufficiency_help1 (RS: Real_seq) (H :Cauchy_of_R RS) (eps:Q): eps>0 ->
 exists N, forall n, (n>=N)%nat -> forall A, 
(match RS with Rseq_intro RS0 _ => RS0 end) n A -> 
forall q, (match A with Real_intro A0 _ => A0 end) n q ->
(Rabs (A - (inject_Q q)) < (inject_Q eps))%R.
Proof. 


intros.

destruct (H (inject_Q (eps*(1#2)))) as [M HM]. admit.



destruct RS as [RS HRS].
destruct (Rseq_exists M) as [X HX].

exists M.
intros.
destruct (Cauchy_Q_limit A (eps)) as [N HN]. auto.
apply (HN n). auto.



 Check Cauchy_Q_limit.
(*  forall p , (RS[n][p] - Rfloor(RS[n]*n)/n
      < RS[n][p] - RS[n] + 1/n
      < eps/2 + eps/2
    => eps/2 > 1/n => N > 2/(eps for n)(problem---->

???? forall eps, exists N, forall A in RS, n>=N -> 
    | RS[n][p] - RS[n] | < eps

RS[n] == RS[n]


first take p: n>p
< |RS[n][n] - RS[p][p]| + |RS[n][p]- RS[n][n]| + |RS[p][p] - RS[n]|
< eps/3 + eps/3 + eps/3





    (Rfloor(RS[n]*n - RS[n][n])/n
      < RS[n] - RS[n] < 0

*)
Admitted.








  destruct (CC_sufficiency_help1 (Rseq_intro RS HRS) H
                                 (epsq*(1#2)) (eps_divide_2_positive _ Hepsq)) as [N HN].

  exists (max M N).
Admitted.
(**

IDEA:

(inject_Q Rn - Sn) < eps/2
    
       ->  Sn - [S * n] / n < (Sn - S - 1/n) 
   n>M -> [S * n]/n - Sn < S - Sn



(R - Sn) < (R - inject_Q Rn) OK + (inject_Q Rn - Sn)\
         < eps/2 + eps/2 = eps

*)




(*

(* If rational seq r[n] is a real A, then A is the limit of the seq *)

Lemma Rlimit_of_Q_cons: forall A, R_seq ((fun n B => forall q, 
  (match A with Real_intro A0 _=>A0 end) n q -> (B == inject_Q q)%R)).
Proof. intros. split.
- intros. destruct A as [A HA]. 
  destruct (Cauchy_exists A HA n) as [q0 Hq0]. exists (inject_Q q0).
  intros. rewrite (Cauchy_unique _ HA _ _ _ Hq0 H). reflexivity.
Admitted.

Lemma Rlimit_of_Q: forall (A:Real) (n:nat) q, 
(match A with Real_intro A0 _=>A0 end) n q ->
Rlimit (Rseq_intro ((fun n B => forall q, 
  (match A with Real_intro A0 _=>A0 end) n q -> (B == inject_Q q)%R))
  (Rlimit_of_Q_cons A)) A.
Admitted.
*)






(*
Definition Cauchy_lim_cons (Rseq:Real_seq):Real.
apply (Real_intro (fun n q =>
forall A B q1 q2, (match Rseq with Rseq_intro RS _ => RS end) n A ->
(match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
(match A with Real_intro A0 _ => A0 end) n q1 ->
(match B with Real_intro B0 _ => B0 end) (S n) q2 -> q == q1+q2)).
Admitted.


Theorem CC_sufficiency_weak: forall (Rseq:Real_seq),

(exists N, forall n, (n>=N)%nat -> forall A B, 
(match Rseq with Rseq_intro RS _ => RS end) n A ->
(match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
~(A==B)%R)

-> Cauchy_of_R Rseq -> (exists Lim:Real, Rlimit Rseq Lim).
Admitted.
*)




(*

Lemma CC_sufficiency_help1 (RS: Real_seq) (H :Cauchy_of_R RS) (eps:Q): eps>0 ->
 exists N, forall n, (n>=N)%nat -> forall A, 
(match RS with Rseq_intro RS0 _ => RS0 end) n A -> 
forall q, (match A with Real_intro A0 _ => A0 end) n q ->
(Rabs ( RCCFun (exist Cauchy_of_R (RS) H) - (inject_Q q)) < (inject_Q eps))%R.


Lemma RCCFun_prop: forall (X:Real_seq) n A (H:Cauchy_of_R X),
(match X with Rseq_intro XS _ => XS end) n A ->
(RCCFun (exist Cauchy_of_R X H) *  (inject_Q (inject_Z (Z.of_nat n)))
 > ((A * inject_Q (inject_Z (Z.of_nat n))) - 1))%R.
Proof. intros. unfold RCCFun. destruct X as [X HX].
  hnf.

destruct (Rfloor_exists (A * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].

destruct A as [A HA].

destruct (Cauchy_exists _ HA n) as [qa Hqa].
assert (q == (z # Pos.of_nat n) * n - (qa
unfold RCCFun.
  unfold Rlt. unfold Rminus.
  unfold Ropp.
  unfold Rplus. unfold CauchySeqPlus. unfold Cauchy_opp.
  unfold Rposit
destruct (classic (exists N, forall n, (n>=N)%nat -> forall A B, 
(match Rseq with Rseq_intro RS _ => RS end) n A ->
(match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
~(A==B)%R)).
- auto using CC_sufficiency_weak.
- pose proof (not_ex_all_not _ _ H0).
  assert (E1: forall N, ~  (forall n, (n>=N)%nat ->
    (forall A B : Real,
        match Rseq with
        | Rseq_intro RS _ => RS
        end n A ->
        match Rseq with
        | Rseq_intro RS _ => RS
        end (S n) B -> ~ (A == B)%R))).
    { intros. pose proof (H1 N). auto. }
  clear H1. clear H0.
  assert (E2: forall N, exists n, (n>=N)%nat /\ ~ forall A B : Real,
      match Rseq with
      | Rseq_intro RS _ => RS
      end n A ->
      match Rseq with
      | Rseq_intro RS _ => RS
      end (S n) B -> ~ (A == B)%R).
    { intros. pose proof (not_all_ex_not _ _ (E1 N)).
      destruct H0. exists x. apply imply_to_and. auto. }
  clear E1.
  assert (E3: forall N : nat, exists n : nat, (n >= N)%nat /\
       (forall A B : Real,
        match Rseq with | Rseq_intro RS _ => RS end n A ->
        match Rseq with | Rseq_intro RS _ => RS end (S n) B -> (A == B)%R)).
    { intros. pose proof (E2 N). destruct H0 as [n [Hn H3]].
      exists n. split. apply Hn. intros. destruct (classic (A==B)%R).
      auto. destruct H3. intros. intros C. destruct Rseq.
      rewrite <- (Rseq_unique _ _ _ H0 H3) in C.
      rewrite <- (Rseq_unique _ _ _ H1 H4) in C. contradiction. }
  clear E2.
  assert (E4: forall N : nat, exists n : nat, (n >= N)%nat /\
     (forall A B : Real,
      match Rseq with | Rseq_intro RS _ => RS end n A ->
      match Rseq with | Rseq_intro RS _ => RS end (S n) B -> ~(A == B)%R)).
  { admit. }

assert (E: exists N0, forall n, (n>=N0)%nat -> forall A B, 
  (match Rseq with Rseq_intro RS _ => RS end) n A ->
  (match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
  (A==B)%R).


  assert (E: exists N, forall n, (n>=N)%nat -> (forall A B : Real,
        match Rseq with
        | Rseq_intro RS _ => RS
        end n A ->
        match Rseq with
        | Rseq_intro RS _ => RS
        end (S n) B -> (A == B)%R)).
  { apply not_all_not_ex. intros C.
    assert (CE:(forall N : nat,
     exists n : nat,
       (n >= N)%nat /\
       (forall A B : Real,
        match Rseq with
        | Rseq_intro RS _ => RS
        end n A ->
        match Rseq with
        | Rseq_intro RS _ => RS
        end (S n) B -> ~(A == B)%R))).
      { intros. pose proof (C N).



  pose proof (E3 O). clear E2. clear E3. destruct H0 as [N [_ HN]].
  destruct Rseq. destruct (Rseq_exists N).
  assert (E: forall n, (n>=N)%nat -> forall A, RS N A -> (A==x)%R).
    { intros.


assert (E: exists N0, forall n, (n>=N0)%nat -> forall A B, 
  (match Rseq with Rseq_intro RS _ => RS end) n A ->
  (match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
  (A==B)%R).
{ destruct (classic (exists N0, forall n, (n>=N0)%nat -> forall A B, 
  (match Rseq with Rseq_intro RS _ => RS end) n A ->
  (match Rseq with Rseq_intro RS _ => RS end) (S n) B ->
  (A==B)%R)). auto.
  pose proof (not_ex_all_not _ _ H0). clear H0.
  pose proof (H1 O).
  destruct H0. intros.
  pose proof (H2 n).
  destruct H5. intros.

  


 apply all_not_not_ex in H0.

*)

(*IDEA : USE RFLOOR! rfloor [An * n ] / n *)
