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




Import ListNotations.


Definition Cauchy (CSeq :nat -> Q) : Prop :=
  forall (eps:Q), eps > 0 -> (exists (n:nat),
     forall (m1 m2:nat), (m1 > n)%nat /\ (m2 > n)%nat
         -> Qabs ((CSeq m1) + (- CSeq m2)) < eps).

Inductive Real : Type :=
| Real_intro (x : nat -> Q) (H:Cauchy x).

Definition Real_equiv (x1 x2 : Real) : Prop :=
  match x1 with
  | Real_intro CSeq1 H1 =>
    match x2 with
    | Real_intro CSeq2 H2 =>
      forall (eps:Q), eps>0 -> (exists (n:nat),
        forall (m:nat), (m > n)%nat ->
         Qabs (CSeq1 m + - CSeq2 m) < eps) end end.

(*Some basic definition & properties of relations*)

Definition relation (X: Type) := X -> X -> Prop.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* We show that the equiv we've defined is an equivalence relation*)

Theorem Real_def_refl: reflexive Real_equiv.
Proof. unfold reflexive. unfold Real_equiv.
  intros. destruct a. unfold Cauchy in *.
  intros eps. exists 0%nat. intros. rewrite Qplus_opp_r. apply H0.
Qed.

Theorem Real_def_symm: symmetric Real_equiv.
Proof. unfold symmetric. unfold Real_equiv.
  intros. destruct a as [Seqa Ha]. destruct b as [Seqb Hb].
  intros. apply H in H0. destruct H0. exists x. intros.
  replace (Seqb m + - Seqa m) with (Seqb m - Seqa m) by reflexivity.
  rewrite (Qabs_Qminus (Seqb m) (Seqa m)). apply H0. apply H1.
Qed.
(*A helping lemma in Qabs-related proofs.*)
Lemma Qabs_triangle_extend: forall (a b c:Q), Qabs (a - c) <=
   Qabs (a - b) + Qabs (b - c).
Proof. intros.
    assert (Heq: a - c == (a - b) + (b - c)). 
      {  rewrite <- (Qplus_assoc a (-b) (b - c)).
         rewrite (Qplus_assoc (-b) b (-c)).
         rewrite (Qplus_comm (- b)). rewrite (Qplus_opp_r).
         rewrite Qplus_0_l. reflexivity.  }
    rewrite Heq.
    apply Qabs_triangle.
Qed.
Lemma eps_divide_2_positive: forall (eps:Q), 0 < eps -> eps * (1 # 2) > 0.
Proof. intros. unfold Qmult. unfold Qlt. simpl.
    rewrite <- Zmult_assoc. simpl. apply H.
Qed.
Lemma eps_over_2_plus : forall (eps:Q),  eps == eps *(1#2) + eps *(1#2).
Proof. intros. rewrite <- Qmult_plus_distr_r. unfold Qplus.
  simpl. assert (His1:(4 # 4) == 1) by reflexivity.
  rewrite His1. rewrite Qmult_1_r. reflexivity.
Qed.

Theorem Real_def_trans: transitive Real_equiv.
Proof. unfold transitive. unfold Real_equiv.
  intros a b c Hab Hbc. destruct a as [Seqa Ha].
  destruct b as [Seqb Hb]. destruct c as [Seqc Hc]. intros.
  destruct (Hab _ (eps_divide_2_positive eps H)) as [n1 H1].
  destruct (Hbc _ (eps_divide_2_positive eps H)) as [n2 H2].

assert (H7: eps == eps *(1#2) + eps *(1#2)) by (apply eps_over_2_plus).


assert (H0: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct H0.
  * exists n2. intros. assert (H4: (m > n1)%nat). { omega. }
    assert (H5: Qabs (Seqa m + - Seqb m) < (eps *(1 # 2))).
      { apply H1. apply H4. }
    assert (H6: Qabs (Seqb m + - Seqc m) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H2. apply H3. }
    apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend (Seqa m) (Seqb m) (Seqc m))). rewrite H7.
    apply (Qplus_lt_le_compat _ _ _ _ H5 H6).
  * apply not_le in H0. exists n1. intros.
    assert (H4: (m > n2)%nat). { omega. }
    assert (H5: Qabs (Seqa m + - Seqb m) < (eps *(1 # 2))).
      { apply H1. apply H3. }
    assert (H6: Qabs (Seqb m + - Seqc m) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H2. apply H4. }
    apply (Qle_lt_trans _ _ _ (Qabs_triangle_extend (Seqa m) (Seqb m) (Seqc m))). rewrite H7.
    apply (Qplus_lt_le_compat _ _ _ _ H5 H6).
Qed.


Theorem Real_equiv_holds: equivalence Real_equiv.
Proof. unfold equivalence. split.
- apply Real_def_refl.
- split.
  + apply Real_def_symm.
  + apply Real_def_trans.
Qed.






(* We show that a constant sequence of Q is Real *)

Theorem Real_has_Q: forall (x1:Q) , Cauchy (fun (n:nat) => x1).
Proof. intros. unfold Cauchy. intros. exists 1%nat. intros m1 m2 [H1 H2].
  rewrite Qplus_opp_r. simpl. apply H.
Qed.


Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_Scope with R.

(*Next, define the plus operation *)
Definition CauchySeqPlus (A B: nat -> Q): (nat->Q) :=
  fun (n:nat) => (A n + B n).

Theorem Cauchy_Plus_Cauchy: forall A B, Cauchy A -> Cauchy B
  -> Cauchy (CauchySeqPlus A B).

Proof. intros. unfold Cauchy in *. intros.

  destruct (H _ (eps_divide_2_positive eps H1)) as [n1 H3].
  destruct (H0 _ (eps_divide_2_positive eps H1)) as [n2 H4].

assert (H2: eps == eps *(1#2) + eps *(1#2)) by (apply eps_over_2_plus).



assert (Hn: le n1 n2 \/ ~ (le n1 n2)). { apply classic. } destruct Hn.
  * exists n2. intros. assert (H7: (m1 > n1 /\ m2 > n1)%nat). { omega. } 
    apply H3 in H7. apply H4 in H6. unfold CauchySeqPlus.
    assert (H': A m1 + B m1 + - (A m2 + B m2) == (A m1 + - A m2) + (B m1 + - B m2)).
    { rewrite -> Qopp_plus. rewrite Qplus_assoc. rewrite <- (Qplus_assoc (A m1)).
      rewrite (Qplus_comm (B m1)). rewrite <- Qplus_assoc. rewrite <- (Qplus_assoc (A m1)).
      rewrite (Qplus_assoc ( - A m2)). reflexivity. }
    rewrite H'. apply (Qle_lt_trans _ _ _ (Qabs_triangle (A m1 + - A m2) (B m1 + - B m2))).
    rewrite H2. assert (H8: Qabs (B m1 + - B m2) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H6. }
    apply (Qplus_lt_le_compat _ _ _ _ H7 H8).

  * apply not_le in H5. exists n1. intros.
    assert (H7: (m1 > n2 /\ m2 > n2)%nat). { omega. } 
    apply H4 in H7. apply H3 in H6. unfold CauchySeqPlus.
    assert (H': A m1 + B m1 + - (A m2 + B m2) == (A m1 + - A m2) + (B m1 + - B m2)).
    { rewrite -> Qopp_plus. rewrite Qplus_assoc. rewrite <- (Qplus_assoc (A m1)).
      rewrite (Qplus_comm (B m1)). rewrite <- Qplus_assoc. rewrite <- (Qplus_assoc (A m1)).
      rewrite (Qplus_assoc ( - A m2)). reflexivity. }
    rewrite H'. apply (Qle_lt_trans _ _ _ (Qabs_triangle (A m1 + - A m2) (B m1 + - B m2))).
    rewrite H2. assert (H8: Qabs (B m1 + - B m2) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H7. }
    apply (Qplus_lt_le_compat _ _ _ _ H6 H8).

Qed.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (CauchySeqPlus A B) (Cauchy_Plus_Cauchy A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B) (at level 50,left associativity).

Definition Rzero:Real := Real_intro (fun n => 0) (Real_has_Q 0).


Theorem Cauthy_Plus_equiv: forall (A1 A2 B1 B2: Real),
  (Real_equiv A1 A2) -> (Real_equiv B1 B2) ->
  Real_equiv (Rplus A1 B1) (Rplus A2 B2). 
Proof. intros A1 A2 B1 B2 Heqa Heqb. unfold Real_equiv.
  destruct A1, A2, B1, B2.
  unfold Rplus. intros eps Heps.
  unfold Real_equiv in *.
  destruct (Heqa _ (eps_divide_2_positive eps Heps)) as [na Ha].
  destruct (Heqb _ (eps_divide_2_positive eps Heps)) as [nb Hb].
  assert (H6: eps == eps *(1#2) + eps *(1#2)) by (apply eps_over_2_plus).


assert (Hn: le na nb \/ ~ (le na nb)). { apply classic. } destruct Hn.
  * exists nb. intros. assert (H5: (m > na)%nat). { omega. }
    unfold CauchySeqPlus. apply Hb in H4. apply Ha in H5.
  assert (H': x m + x1 m + -(x0 m + x2 m) == (x m + - x0 m) + (x1 m + - x2 m)).
  { rewrite -> Qopp_plus. rewrite Qplus_assoc.
    rewrite <- (Qplus_assoc (x m)).
      rewrite (Qplus_comm (x1 m)). rewrite <- Qplus_assoc. rewrite <- (Qplus_assoc (-x0 m)).
      rewrite (Qplus_assoc (x m)). reflexivity. }
  rewrite H'.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (x m + -x0 m) (x1 m + - x2 m))).
  rewrite H6. 
  assert (H7: Qabs (x1 m + - x2 m) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H4. }
  apply (Qplus_lt_le_compat _ _ _ _ H5 H7).


  * apply not_le in H3. exists na. intros.
    assert (H5: (m > nb)%nat). { omega. }
    unfold CauchySeqPlus. apply Ha in H4. apply Hb in H5.
  assert (H': x m + x1 m + -(x0 m + x2 m) == (x m + - x0 m) + (x1 m + - x2 m)).
  { rewrite -> Qopp_plus. rewrite Qplus_assoc.
    rewrite <- (Qplus_assoc (x m)). rewrite (Qplus_comm (x1 m)).
    rewrite <- Qplus_assoc. rewrite <- (Qplus_assoc (-x0 m)).
    rewrite (Qplus_assoc (x m)). reflexivity. }
  rewrite H'.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle (x m + -x0 m) (x1 m + - x2 m))).
  rewrite H6. 
  assert (H7: Qabs (x1 m + - x2 m) <= (eps *(1 # 2))).
      { apply Qle_lteq. left. apply H5. }
  apply (Qplus_lt_le_compat _ _ _ _ H4 H7).
Qed.




Theorem Rplus_comm : forall (A B: Real),
  Real_equiv (A + B) (B + A).
Proof. intros. destruct A as [A Ha] ,B as [B Hb]. unfold Rplus.
  unfold Real_equiv. intros eps Heps. unfold Cauchy in *.
  unfold CauchySeqPlus. clear Ha Hb.
  exists O. intros. rewrite Qopp_plus. rewrite Qplus_assoc.
  rewrite <- (Qplus_assoc (A m)). rewrite Qplus_opp_r. rewrite Qplus_0_r.
  rewrite Qplus_opp_r. simpl. apply Heps.
Qed.

Theorem Rplus_assoc: forall (A B C: Real),
  Real_equiv (A + B + C)  (A + (B + C)).
Proof. intros. destruct A as [A Ha] ,B as [B Hb], C as [C Hc]. unfold Rplus.
  unfold Real_equiv. unfold Cauchy in *.
  unfold CauchySeqPlus. clear Ha Hb.
  exists O. intros. rewrite Qplus_assoc. rewrite Qplus_opp_r. simpl. apply H.
Qed.

Theorem Rplus_Zero: forall (A : Real),
  Real_equiv (A + Rzero) A.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros. unfold CauchySeqPlus.
  exists O. intros. rewrite Qplus_0_r. rewrite Qplus_opp_r. apply H.
Qed.


Definition Cauchy_opp (A : nat -> Q): (nat->Q) :=
  fun (n:nat) => - A n.

Theorem Cauchy_opp_Cauchy: forall A, Cauchy A 
  -> Cauchy (Cauchy_opp A).
Proof. intros. unfold Cauchy in *. unfold Cauchy_opp. intros.
  apply H in H0. destruct H0 as [n Hn]. 
  exists n. intros. rewrite Qopp_involutive. rewrite Qplus_comm.
  assert (H': (A m2 + - A m1 == A m2 - A m1)%Q). { reflexivity. }
  rewrite H'. rewrite Qabs_Qminus. apply Hn. apply H0.
Qed.

Fixpoint Ropp(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (Cauchy_opp A) (Cauchy_opp_Cauchy A HA) 
  end.

Theorem Rplus_opp_r : forall (A:Real), Real_equiv (A + (Ropp A))  Rzero.
Proof. intros. unfold Real_equiv. destruct A as [A Ha]. unfold Rzero. 
  unfold Ropp. unfold Cauchy in *. unfold Cauchy_opp. unfold Rplus.
  unfold CauchySeqPlus. intros.
  exists O. intros. rewrite Qplus_opp_r. apply H.
Qed.

