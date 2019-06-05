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



Lemma Inject_2: forall m:nat, (m<>0)%nat -> Z.pos (Pos.of_nat m ) = Z.of_nat m.
Proof. intros. induction m.
  - omega.
  - destruct m. + reflexivity.
  + assert (S m <> 0)%nat. { omega. }
    apply IHm in H0. rewrite Nat2Z.inj_succ. rewrite <- H0.
    rewrite <- Pos2Z.inj_succ.
    rewrite <- Nat2Pos.inj_succ.
    reflexivity.
    omega.
Qed.
Lemma inject_of_nat_equiv: forall m, (m<>0 )%nat-> (Z.of_nat m # Pos.of_nat m) == 1.
Proof. intros. rewrite Qmake_Qdiv. rewrite Inject_2. field.
  intros C. assert (0==inject_Z 0) by reflexivity. rewrite H0 in C.
  rewrite inject_Z_injective in C. omega. omega.
Qed.

Lemma Qinject_nat_pos: forall m, (m<>0)%nat -> inject_Z(Z.of_nat m)>0.
Proof. intros. assert (0==inject_Z 0) by reflexivity. rewrite H0. rewrite <- Zlt_Qlt.
    omega.
Qed.
Lemma Qmake_pos_inject_Z: forall m, (m<>0)%nat -> (1 / inject_Z (Z.of_nat m)) == (1 # Pos.of_nat m).
Proof. intros. rewrite (Qmake_Qdiv _ (Pos.of_nat m)).
       rewrite Inject_2. reflexivity. auto.
Qed.


(** ---------- Single2Element Function ----------------*)

(** Single Element Set to Element Function *)


Lemma funlemma1: forall (S:Real->Prop),(exists x, S x) -> (
forall n : nat,
exists (q : Q) (A : Real),
  S A /\
  (forall z : Z,
   Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z ->
   q == z # Pos.of_nat n)).
Proof.
  intros S H1 n. destruct H1 as [A0 HA0].
  destruct (Rfloor_exists  (A0 * inject_Q (inject_Z (Z.of_nat n)))) as [z Hz].
  exists (z # Pos.of_nat (n)).
  exists A0. split. auto. intros. rewrite (Rfloor_unique _ _ _ Hz H). reflexivity.
Qed.


Lemma funlemma2: forall (S:Real->Prop), (forall x1 x2, S x1 ->
 S x2 -> (x1 == x2)%R) ->
(forall (n : nat) (q1 q2 : Q),
(exists A : Real,
   S A /\
   (forall z : Z,
    Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z ->
    q1 == z # Pos.of_nat n)) ->
(exists A : Real,
   S A /\
   (forall z : Z,
    Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z ->
    q2 == z # Pos.of_nat n)) -> q1 == q2).
Proof.
  intros S H2. intros. destruct H as[A1 [SHA1 HA1]]. destruct H0 as [A2 [SHA2 HA2]].
  destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat n)))) as [z1 Hz1].
  destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat n)))) as [z2 Hz2].
  assert (E:z1=z2). { apply (Rfloor_unique _ _ _ Hz1 Hz2). }
  rewrite (H2 _ _ SHA1 SHA2) in Hz2.
  rewrite (HA1 _ Hz1),(HA2 _ Hz2). rewrite E. reflexivity.
Qed.

Lemma funlemma3: forall (S:Real->Prop), ( Proper (Real_equiv ==> iff) (S)) ->
forall (p q : Q) (n : nat),
p == q ->
(exists A : Real,
   S A /\
   (forall z : Z,
    Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z ->
    p == z # Pos.of_nat n)) ->
exists A : Real,
  S A /\
  (forall z : Z,
   Rfloor (A * inject_Q (inject_Z (Z.of_nat n))) z ->
   q == z # Pos.of_nat n).
Proof.
  intros S H3. intros. destruct H0 as [A [SHA HA]]. exists A. split. auto. 
  intros. rewrite <- H. apply (HA z). auto.
Qed.


Lemma funlemma4: forall (S:Real->Prop), (exists x, S x) -> (forall x1 x2, S x1 ->
 S x2 -> (x1 == x2)%R) -> Proper (Real_equiv ==> iff) (S) -> 
forall eps : Q,0 < eps -> exists n : nat,  forall m1 m2 : nat,
  (m1 > n)%nat ->  (m2 > n)%nat ->  forall q1 q2 : Q,
  (exists A : Real, S A /\ (forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat m1))) z -> q1 == z # Pos.of_nat m1)) ->
  (exists A : Real, S A /\ (forall z : Z, Rfloor (A * inject_Q (inject_Z (Z.of_nat m2))) z -> q2 == z # Pos.of_nat m2)) ->
   Qabs (q1 - q2) < eps.
Proof. intros S H1 H2 H3. intros. exists (max 2 (Z.to_nat (1 + (Qceiling (1/eps))))).
  intros. destruct H5 as [A1 [HA1 Hq1]].
  assert (Em1: m1 <> 0%nat).
  { intros C. rewrite C in H0. omega. }
  assert (Em2: m2 <> 0%nat).
  { intros C. rewrite C in H4. omega. }
  assert (Em3: (m1 - 1 <> 0)%nat).
  { intros C. assert (m1 = 1)%nat by omega. rewrite H5 in H0.
    apply max_lt_lub_l in H0. assert (foo: (~ 2<1)%nat). omega. contradiction. }
  assert (Em4: (m2 - 1 <> 0)%nat).
  { intros C. assert (m2 = 1)%nat by omega. rewrite H5 in H4.
    apply max_lt_lub_l in H4. assert (foo: (~ 2<1)%nat). omega. contradiction. }
    destruct H6 as [A2 [HA2 Hq2]].
    assert (A1==A2)%R by (apply (H2 _ _ HA1 HA2)).
    destruct (Rfloor_exists (A1 * inject_Q (inject_Z (Z.of_nat m1)))) as [z1 Hz1].
    destruct (Rfloor_exists (A2 * inject_Q (inject_Z (Z.of_nat m2)))) as [z2 Hz2].
    assert (Hqz1: q1 == z1 # Pos.of_nat m1) by auto.
    assert (Hqz2: q2 == z2 # Pos.of_nat m2) by auto.
    clear Hq1. clear Hq2. 
    assert (E1: - (1/(inject_Z (Z.of_nat m1))) < (q1 - q2)
          /\ q1 - q2 < 1/(inject_Z (Z.of_nat m2))).
    { destruct Hz1 as [P1 P2].
      assert (T1: (inject_Q q1 > (A1 - (inject_Q (1#Pos.of_nat m1))))%R).
        { unfold Rgt. rewrite Hqz1. rewrite <- (Rmult_1_r A1).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em1))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m1)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em1).
          rewrite <- inject_Q_inv. reflexivity. }
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R as Rden.
        rewrite Et2. clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m1)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m1) * (1 # Pos.of_nat m1) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc.
              assert (Et': inject_Z (Z.of_nat m1) * / inject_Z (Z.pos (Pos.of_nat m1)) ==
                            inject_Z (Z.of_nat m1)  / inject_Z (Z.pos (Pos.of_nat m1))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rlt_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m1))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m1)) > 0)).
          { rewrite (Inject_2 _ Em1). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z1) /
          inject_Z (Z.pos (Pos.of_nat m1)) * inject_Z (Z.pos (Pos.of_nat m1)) == 
          inject_Z (z1)).
          { field. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite Et5. unfold Rminus. rewrite Rmult_plus_distr_l.
        assert (Et6: (Rden * inject_Q (inject_Z (Z.pos (Pos.of_nat m1))) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            rewrite Qmake_Qdiv. unfold Qdiv. rewrite <- Qmult_assoc.
            rewrite (Qmult_comm (/ inject_Z (Z.pos (Pos.of_nat m1)))).
            rewrite Qmult_inv_r. reflexivity. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite <- Ropp_mult_distr. rewrite Et6.
        apply (Rlt_plus_compat_r _ _ 1%R).
        assert (Et7: (1 == (inject_Q 1))%R) by reflexivity.
        rewrite Rplus_assoc. rewrite (Rplus_comm (-(1))%R).
        rewrite Rplus_opp_r. rewrite Rplus_0_r. rewrite Et7.
        rewrite <- inject_Q_plus. rewrite (Inject_2 _ Em1). auto. }
      assert (T2: (inject_Q q1 <= A1 )%R).
        { rewrite Hqz1. rewrite <- (Rmult_1_r A1).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em1))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m1)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em1).
          rewrite <- inject_Q_inv. reflexivity. } 
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m1)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m1)) (inject_Z_nonzero _ Em1)))%R as Rden.
        clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m1)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m1) * (1 # Pos.of_nat m1) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m1) * / inject_Z (Z.pos (Pos.of_nat m1)) ==
                            inject_Z (Z.of_nat m1)  / inject_Z (Z.pos (Pos.of_nat m1))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rle_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m1))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m1)) > 0)).
          { rewrite (Inject_2 _ Em1). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z1) /
          inject_Z (Z.pos (Pos.of_nat m1)) * inject_Z (Z.pos (Pos.of_nat m1)) == 
          inject_Z (z1)).
          { field. rewrite (Inject_2 _ Em1). apply inject_Z_nonzero. auto. }
        rewrite Et5. rewrite (Inject_2 _ Em1). auto. }
      clear P1. clear P2.
      destruct Hz2 as [P1 P2].
      assert (T3: (inject_Q q2 > (A2 - (inject_Q (1#Pos.of_nat m2))))%R).
        { unfold Rgt. rewrite Hqz2. rewrite <- (Rmult_1_r A2).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em2))).
          assert (Et2: ((inject_Q (1 # Pos.of_nat m2)) == /
          exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em2).
          rewrite <- inject_Q_inv. reflexivity. }
          remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R as Rden.
        rewrite Et2. clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m2)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m2) * (1 # Pos.of_nat m2) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m2) * / inject_Z (Z.pos (Pos.of_nat m2)) ==
                            inject_Z (Z.of_nat m2)  / inject_Z (Z.pos (Pos.of_nat m2))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rlt_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m2))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m2)) > 0)).
          { rewrite (Inject_2 _ Em2). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z2) /
          inject_Z (Z.pos (Pos.of_nat m2)) * inject_Z (Z.pos (Pos.of_nat m2)) == 
          inject_Z (z2)).
          { field. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite Et5. unfold Rminus. rewrite Rmult_plus_distr_l.
        assert (Et6: (Rden * inject_Q (inject_Z (Z.pos (Pos.of_nat m2))) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            rewrite Qmake_Qdiv. unfold Qdiv. rewrite <- Qmult_assoc.
            rewrite (Qmult_comm (/ inject_Z (Z.pos (Pos.of_nat m2)))).
            rewrite Qmult_inv_r. reflexivity. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite <- Ropp_mult_distr. rewrite Et6.
        apply (Rlt_plus_compat_r _ _ 1%R).
        assert (Et7: (1 == (inject_Q 1))%R) by reflexivity.
        rewrite Rplus_assoc. rewrite (Rplus_comm (-(1))%R).
        rewrite Rplus_opp_r. rewrite Rplus_0_r. rewrite Et7.
        rewrite <- inject_Q_plus. rewrite (Inject_2 _ Em2). auto. }
      assert (T4: (inject_Q q2 <= A2 )%R).
        { rewrite Hqz2. rewrite <- (Rmult_1_r A2).
          rewrite <- (Rmult_inv_r' _ (inject_Q_nonzero _ (inject_Z_nonzero _ Em2))).
        assert (Et2: ((inject_Q (1 # Pos.of_nat m2)) == /
        exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R).
        { rewrite Qmake_Qdiv. unfold Qdiv. rewrite inject_Q_mult.
          assert (Ett: (inject_Q (inject_Z 1) == 1)%R). { reflexivity. }
          rewrite Ett. rewrite Rmult_1_l. rewrite (Inject_2 _ Em2).
          rewrite <- inject_Q_inv. reflexivity. } 
        remember (/ exist (fun a0 : Real => ~ a0 == 0) (inject_Q (inject_Z (Z.of_nat m2)))
          (inject_Q_nonzero (inject_Z (Z.of_nat m2)) (inject_Z_nonzero _ Em2)))%R as Rden.
        clear HeqRden.
        assert (Et3: ((inject_Q (inject_Z (Z.of_nat m2)) * Rden) == 1)%R).
          { rewrite <- Et2. rewrite <- inject_Q_mult.
            assert(Et: inject_Z (Z.of_nat m2) * (1 # Pos.of_nat m2) == 1).
            { rewrite Qmake_Qdiv. unfold Qdiv. rewrite (Qmult_comm (inject_Z 1)).
              rewrite Qmult_assoc. 
              assert (Et': inject_Z (Z.of_nat m2) * / inject_Z (Z.pos (Pos.of_nat m2)) ==
                            inject_Z (Z.of_nat m2)  / inject_Z (Z.pos (Pos.of_nat m2))) by reflexivity.
            rewrite Et'. rewrite <- Qmake_Qdiv. rewrite inject_of_nat_equiv. reflexivity. omega. }
        rewrite Et. reflexivity. }
        rewrite Et3. rewrite Rmult_1_r.
        rewrite Qmake_Qdiv. apply (Rle_mult_compat_r _ _ (inject_Q (inject_Z (Z.pos (Pos.of_nat m2))))).
        assert (Et4: (inject_Z (Z.pos (Pos.of_nat m2)) > 0)).
          { rewrite (Inject_2 _ Em2). apply Qinject_nat_pos. auto. }
        apply inject_Q_pos. auto. rewrite <- inject_Q_mult.
        assert (Et5: inject_Z (z2) /
          inject_Z (Z.pos (Pos.of_nat m2)) * inject_Z (Z.pos (Pos.of_nat m2)) == 
          inject_Z (z2)).
          { field. rewrite (Inject_2 _ Em2). apply inject_Z_nonzero. auto. }
        rewrite Et5. rewrite (Inject_2 _ Em2). auto. }
      rewrite <- H5 in T3. rewrite <- H5 in T4.
      apply Ropp_le_compat in T2. apply Ropp_le_compat in T4.
      assert (inject_Q q1 + (- (inject_Q q2)) > A1 - inject_Q (1 # Pos.of_nat m1) + (-A1))%R.
      { apply Rlt_le_plus_compat. auto. auto. }
      assert (inject_Q q2 + (- (inject_Q q1)) > A1 - inject_Q (1 # Pos.of_nat m2) + (-A1))%R.
      { apply Rlt_le_plus_compat. auto. auto. }
      assert (Et1: (inject_Q q1 + - inject_Q q2== inject_Q (q1 - q2))%R).
      { rewrite <- inject_Q_opp. rewrite <- inject_Q_plus. reflexivity. }
      assert (Et2: (inject_Q q2 + - inject_Q q1== inject_Q (-(q1 - q2)))%R).
      { rewrite <- inject_Q_opp. rewrite <- inject_Q_plus.
        assert ((q2 + - q1)==- (q1 - q2)) by ring. rewrite H8. reflexivity. }
      assert (Et3: (A1 - inject_Q (1 # Pos.of_nat m1) + - A1 == - inject_Q (1 # Pos.of_nat m1))%R).
      { unfold Rminus. rewrite (Rplus_comm A1). rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity. }
      assert (Et4: (A1 - inject_Q (1 # Pos.of_nat m2) + - A1 == - inject_Q (1 # Pos.of_nat m2))%R).
      { unfold Rminus. rewrite (Rplus_comm A1). rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity. }
      rewrite Et1 in H6. rewrite Et2 in H7. rewrite Et3 in H6. rewrite Et4 in H7.
      clear Et1. clear Et2. clear Et3. clear Et4. unfold Rgt in H6,H7.
      rewrite <- inject_Q_opp in H6,H7.
      apply inject_Q_lt_inv in H6. apply inject_Q_lt_inv in H7.
      apply Qopp_lt_compat in H7. rewrite Qopp_involutive in H7,H7.
      rewrite Qmake_pos_inject_Z. split. auto. rewrite Qmake_pos_inject_Z. auto. auto. auto.
}

  assert (E2: eps > 1 / inject_Z (Z.of_nat (m2 - 1))).
  { apply Qlt_shift_div_r. apply Qinject_nat_pos. omega.
    apply (Qmult_lt_l _ _ _ (Qinv_lt_0_compat _ H)).
    assert (Et: / eps * (eps * inject_Z (Z.of_nat (m2-1))) == inject_Z (Z.of_nat (m2-1))).
      { field. intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
    rewrite Et. rewrite Qmult_1_r.
    assert (Et1: / eps <= inject_Z (Qceiling (1 / eps))).
      { assert (Et0: / eps == 1 / eps). { field.
        intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
        rewrite Et0. apply Qle_ceiling. }
    apply (Qle_lt_trans _ _ _ Et1).
    rewrite <- Zlt_Qlt.
    assert( Et2: (m2 - 1 + 1 = m2)%nat). { omega. }
    apply (Zplus_lt_reg_r _ _ (Z.of_nat 1)).
    rewrite <- Nat2Z.inj_add. rewrite Et2.
    assert (Et3: (0<=Qceiling (1 / eps))%Z).
    { rewrite Zle_Qle. apply Qlt_le_weak. apply (Qlt_le_trans _ (1/eps)).
      unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. auto.
      apply Qle_ceiling. }
    rewrite <- (Z2Nat.id (Qceiling (1 / eps))).
    rewrite Zplus_comm.
    rewrite <- Nat2Z.inj_add.
    rewrite <- Nat2Z.inj_lt.
    assert (Et4: 1%nat = (Z.to_nat 1)) by reflexivity.
    rewrite Et4.
    rewrite <- Z2Nat.inj_add.
    apply Nat.max_lub_lt_iff in H0.
    apply Nat.max_lub_lt_iff in H4.
    apply (proj2 H4). omega. auto. auto. }


  assert (E3: eps > 1 / inject_Z (Z.of_nat (m1 - 1))).
  { apply Qlt_shift_div_r. apply Qinject_nat_pos. omega.
    apply (Qmult_lt_l _ _ _ (Qinv_lt_0_compat _ H)).
    assert (Et: / eps * (eps * inject_Z (Z.of_nat (m1-1))) == inject_Z (Z.of_nat (m1-1))).
      { field. intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
    rewrite Et. rewrite Qmult_1_r.
    assert (Et1: / eps <= inject_Z (Qceiling (1 / eps))).
      { assert (Et0: / eps == 1 / eps). { field.
        intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
        rewrite Et0. apply Qle_ceiling. }
    apply (Qle_lt_trans _ _ _ Et1).
    rewrite <- Zlt_Qlt.
    assert( Et2: (m1 - 1 + 1 = m1)%nat). { omega. }
    apply (Zplus_lt_reg_r _ _ (Z.of_nat 1)).
    rewrite <- Nat2Z.inj_add. rewrite Et2.
    assert (Et3: (0<=Qceiling (1 / eps))%Z).
    { rewrite Zle_Qle. apply Qlt_le_weak. apply (Qlt_le_trans _ (1/eps)).
      unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. auto.
      apply Qle_ceiling. }
    rewrite <- (Z2Nat.id (Qceiling (1 / eps))).
    rewrite Zplus_comm.
    rewrite <- Nat2Z.inj_add.
    rewrite <- Nat2Z.inj_lt.
    assert (Et4: 1%nat = (Z.to_nat 1)) by reflexivity.
    rewrite Et4.
    rewrite <- Z2Nat.inj_add.
    apply Nat.max_lub_lt_iff in H0.
    apply Nat.max_lub_lt_iff in H4.
    apply (proj2 H0). omega. auto. auto. }
  destruct E1 as [E0 E1].
  assert (E4: Qabs(q1 - q2) <=  (1 / inject_Z (Z.of_nat m1))
              \/ Qabs (q1 - q2) <= (1 / inject_Z (Z.of_nat m2))).
  { destruct (classic (1/(inject_Z (Z.of_nat m1)) < (1/inject_Z (Z.of_nat m2)))).
    - right. apply Qabs_Qle_condition. split.
      + apply (Qle_trans _  (-(1 / inject_Z (Z.of_nat (m1))))).
        apply Qopp_le_compat. apply Qlt_le_weak. auto.
        apply Qlt_le_weak. auto.
      + apply Qlt_le_weak. auto.
    - left. apply Qabs_Qle_condition. apply Qnot_lt_le in H6. split.
      + apply Qlt_le_weak. auto.
      + apply (Qle_trans _  ((1 / inject_Z (Z.of_nat (m2))))).
        apply Qlt_le_weak. auto. auto. }

  assert (E5: 1 / inject_Z (Z.of_nat m1) < 1 / inject_Z (Z.of_nat (m1 - 1))).
    { apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat m1))). apply Qinject_nat_pos. omega.
      unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm  (/ inject_Z (Z.of_nat m1) )).
      rewrite Qmult_inv_r. rewrite Qmult_1_r.
      apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat (m1-1)))). apply Qinject_nat_pos. omega.
      rewrite Qmult_1_l. rewrite Qmult_1_l.
      rewrite Qmult_comm. rewrite Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_l.
      rewrite <- Zlt_Qlt. apply inj_lt. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m1 - 1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega. }

  assert (E6: 1 / inject_Z (Z.of_nat m2) < 1 / inject_Z (Z.of_nat (m2 - 1))).
    { apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat m2))). apply Qinject_nat_pos. omega.
      unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm  (/ inject_Z (Z.of_nat m2) )).
      rewrite Qmult_inv_r. rewrite Qmult_1_r.
      apply (Qmult_lt_r _ _ (inject_Z (Z.of_nat (m2-1)))). apply Qinject_nat_pos. omega.
      rewrite Qmult_1_l. rewrite Qmult_1_l.
      rewrite Qmult_comm. rewrite Qmult_assoc. rewrite Qmult_inv_r.
      rewrite Qmult_1_l.
      rewrite <- Zlt_Qlt. apply inj_lt. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m2 - 1)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega.
      intros C. inversion C. rewrite Zmult_1_r in H7.
      assert (Z.to_nat (Z.of_nat (m2)) = 0%nat).
      { rewrite H7. reflexivity. }
      rewrite Nat2Z.id in H6. omega. }
  destruct E4.
  * apply (Qle_lt_trans _ _ _ H6). apply (Qlt_trans _ _ _ E5).
    auto.
  * apply (Qle_lt_trans _ _ _ H6). apply (Qlt_trans _ _ _ E6).
    auto.
Qed.

Definition RSingleFun : {X: Real -> Prop|(exists x, X x) /\ (forall x1 x2, X x1 ->
 X x2 -> x1 == x2) /\ Proper (Real_equiv ==> iff) (X)
 }%R -> Real.

Proof. intros. destruct X as [S [H1 [H2 H3]]].
  apply (Real_intro (fun n q => exists A, S A /\ forall z,
          (Rfloor (A * (inject_Q (inject_Z (Z.of_nat (n)%nat)))) z) -> 
        q == z # (Pos.of_nat (n)%nat))).
  split.
- apply funlemma1;auto.
- apply funlemma2;auto.
- apply funlemma3;auto.
- apply funlemma4;auto.
Defined.

Theorem Cauchy_Q_limit: forall A eps, eps>0->
exists N, forall n, (n>=N)%nat ->
forall q, (match A with Real_intro A0 _ => A0 end) n q ->
(Rabs (A - (inject_Q q)) < inject_Q eps)%R.
Proof. intros. destruct A as [A HA].
  destruct (Cauchy_def _ HA (eps * (1 # 2)) (eps_divide_2_positive _ H)) as [N HN].
  exists (S N).
  intros.
  assert (forall m, (m >= n)%nat ->  forall qm : Q,
    A m qm -> Qabs (q - qm) < eps * (1 # 2)).
    { intros.
      apply (HN n m). auto. omega. auto. auto. }
  hnf. repeat (unfold Rminus; unfold Ropp; unfold Rplus; unfold Cauchy_abs;
               unfold CauchySeqPlus; unfold Cauchy_opp; unfold Rabs; unfold inject_Q).
  exists (eps*(1#2)). split. apply eps_divide_2_positive. auto.
  exists n. intros. destruct (Cauchy_exists _ HA n0) as [qn0 Hqn0].
  assert (q0 == eps - Qabs (qn0 - q)).
   { apply H4. ring. intros. rewrite (H5 (qn0 - q)). reflexivity.
     intros. rewrite (H7 q). rewrite (Cauchy_unique _ HA _ _ _ Hqn0 H6).
     ring. ring. }
  rewrite H5. apply (Qplus_le_r _ _ (Qabs (qn0 - q) - eps * (1 # 2))).
   assert (Et1: Qabs (qn0 - q) - eps * (1 # 2) + eps * (1 # 2) == Qabs (qn0 -q)) by ring.
    rewrite Et1. clear Et1.
  assert (Et2: Qabs (qn0 - q) - eps * (1 # 2) + (eps - Qabs (qn0 - q)) == eps * (1-(1#2))) by ring.
  rewrite Et2. assert (Et3: (1-(1#2)==1#2)) by ring. rewrite Et3. clear Et2. clear Et3.
  apply Qlt_le_weak. rewrite Qabs_Qminus. apply (H2 n0). auto. auto.
Qed.

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

Lemma inject_Q_minus:forall a b, (inject_Q (a-b) == inject_Q a- inject_Q b)%R.
Proof. intros. unfold Qminus. rewrite inject_Q_plus. rewrite inject_Q_opp. reflexivity.
Qed.

Theorem Rsinglefun_correct: forall X H, X (RSingleFun (exist _ X H)).
Proof. intros. hnf in *. destruct H as [H1 [H2 H3]].
  hnf in H3. 
  assert (T1:0 == inject_Z 0) by ring.
  destruct H1.
  apply (H3 x);auto. hnf. unfold RSingleFun. destruct x as [A HA].
  intros.
  pose proof (Cauchy_Q_limit (Real_intro A HA) _ (eps_divide_2_positive _ H)).
  destruct H0 as [N0 HN0].
  exists (max N0 (2* Z.to_nat (Qceiling (/eps))+1)).
  intros n Hn. apply Nat.max_lub_lt_iff in Hn.
  intros. destruct H1 as [A' [HA' H5]].
  assert ((Real_intro A HA)==A')%R. { apply H2. auto. auto. }
    clear HA'.
  assert (n<>0)%nat. {intros C. rewrite C in Hn. destruct Hn. omega. }
  destruct (Rfloor_exists (A' * inject_Q (inject_Z (Z.of_nat n)))%R) as [z0 Hz0].
  pose proof (Real_constr_help2 _ _ _ _ H4 Hz0 (H5 _ Hz0)).
  pose proof (Real_constr_help1 _ _ _ _ H4 Hz0 (H5 _ Hz0)).
  apply Qabs_Qlt_condition. split.
  - assert (q1-q2==-(q2-q1))by ring. rewrite H8. apply Qopp_lt_compat. 
    apply Qlt_Rlt. rewrite inject_Q_minus. clear H8.
    apply (Rle_lt_trans _ (A'-inject_Q q1)%R).
    repeat unfold Rminus. apply Rle_plus_r. auto.
    rewrite <- H1.
    assert ((Rabs (Real_intro A HA - inject_Q q1) < inject_Q (eps * (1 # 2)))%R).
    { apply (HN0 n). omega. auto. }
    apply Rabs_lt_iff in H8. destruct H8.
    apply (Rlt_trans _ _ _ H9). apply Qlt_Rlt. rewrite <- (Qmult_1_r eps).
    rewrite <- Qmult_assoc.
    apply Qmult_lt_l. auto. reflexivity.
    apply Qlt_Rlt. apply eps_divide_2_positive. auto.
  - apply Qlt_Rlt. rewrite inject_Q_minus.
    apply (Rlt_le_trans _ (inject_Q q1 - A' + inject_Q (1 # Pos.of_nat n))%R).
    repeat unfold Rminus. rewrite Rplus_assoc. apply Rlt_plus_l.
    assert (- A' + inject_Q (1 # Pos.of_nat n) == - (A' - inject_Q (1 # Pos.of_nat n)))%R by ring.
    rewrite H8. apply Ropp_lt_compat. auto.

    assert ((Rabs (Real_intro A HA - inject_Q q1) < inject_Q (eps * (1 # 2)))%R).
    { apply (HN0 n). omega. auto. }
    apply Rabs_lt_iff in H8. destruct H8. clear H9.
    rewrite <- H1.
    apply Ropp_lt_compat in H8.
    assert (Real_intro A HA - inject_Q q1 == -(inject_Q q1 - Real_intro A HA))%R by ring.
    rewrite H9 in H8. repeat  rewrite <- Ropp_involutive in H8.
    apply (Rle_trans _ (inject_Q (eps * (1 # 2)) + inject_Q (1 # Pos.of_nat n))).
    apply Rle_plus_r. left. auto.
    rewrite <- inject_Q_plus. apply Qle_Rle.
    apply (Qplus_le_l _ _ (-eps * (1 # 2) )).
    assert (eps * (1 # 2) + (1 # Pos.of_nat n) + - eps * (1 # 2) == (1 # Pos.of_nat n)) by ring.
    assert (eps + - eps * (1 # 2) == eps * (1 # 2)) by ring.
    rewrite H10,H11.
  clear Hz0. clear H6. clear H7. clear H8. clear H9. clear H10. clear H11.
  pose proof (proj2 Hn).
  pose proof (Qle_ceiling (/ eps)).
  apply (Qmult_le_l _ _ (inject_Z 2)) in H7.
  assert (inject_Z 2*/eps<= inject_Z 2*inject_Z (Qceiling (/ eps))+1).
  { apply (Qle_trans _ _ _ H7). rewrite <- Qplus_0_r. rewrite <- Qplus_assoc. apply Qplus_le_r.
    intros C. discriminate C. }
  rewrite Qmake_Qdiv.
  apply Qle_shift_div_r. rewrite Inject_2. rewrite T1. rewrite <- Zlt_Qlt. omega. omega.
  apply (Qle_trans _ (eps * (1 # 2) * (inject_Z 2 * inject_Z (Qceiling (/ eps)) + 1))).
    { apply (Qmult_le_l _ _ (eps * (1 # 2) )) in H8.
      assert (eps * (1 # 2) * (inject_Z 2 * / eps) == 1). { field. intros C. rewrite C in H. apply Qlt_irrefl in H. auto. }
      rewrite H9 in H8. auto. apply eps_divide_2_positive. auto. }
    { apply Qmult_le_l. apply eps_divide_2_positive. auto.  rewrite <- inject_Z_mult.
      assert (1==inject_Z 1) by ring. rewrite H9.
      rewrite <- inject_Z_plus. rewrite<-  Zle_Qle. rewrite Inject_2.
      apply inj_lt in H6. rewrite inj_plus in H6. rewrite inj_mult in H6.
      rewrite  Z2Nat.id in H6.
      assert (Z.of_nat 2 = 2)%Z by reflexivity. rewrite H10 in H6.
      assert (Z.of_nat 1 = 1)%Z by reflexivity. rewrite H11 in H6.
      apply Z.lt_le_incl. auto.
       assert (0 = Qceiling 0)%Z by reflexivity. rewrite H10.
          apply Qceiling_resp_le. apply Qlt_le_weak. apply Qinv_lt_0_compat. auto. auto. }
      reflexivity.
      apply Qlt_Rlt. apply eps_divide_2_positive. auto.
Qed.



