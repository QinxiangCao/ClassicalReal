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

(*MCS refers to "monotone convergence sequence" *)
Record MCS (CSeq :nat -> Q) : Prop :={
P1: exists (M:Q),forall (n:nat),CSeq n<M;
P2: exists (N:Q),forall (n:nat),CSeq n>N;
P3: (forall (n:nat),CSeq n<=CSeq (S n))\/(forall(n:nat),CSeq (S n)<=CSeq n);
}.

Inductive Real : Type :=
| Real_intro (x : nat -> Q) (H:MCS x).

Definition Real_equiv (x1 x2 : Real) : Prop :=
  match x1, x2 with
  | Real_intro CSeq1 H1,
    Real_intro CSeq2 H2 =>
      forall (eps:Q), eps>0 -> (exists (n:nat),
        forall (m:nat), (m > n)%nat ->
         Qabs (CSeq1 m + - CSeq2 m) < eps)
  end.

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
  intros. destruct a. intros eps. exists 0%nat. intros. rewrite Qplus_opp_r. apply H0.
Qed.

Theorem Real_def_symm: symmetric Real_equiv.
Proof. unfold symmetric. unfold Real_equiv.
  intros. destruct a as [Seqa Ha]. destruct b as [Seqb Hb].
  intros. apply H in H0. destruct H0. exists x. intros.
  replace (Seqb m + - Seqa m) with (Seqb m - Seqa m) by reflexivity.
  rewrite (Qabs_Qminus (Seqb m) (Seqa m)). apply H0. apply H1.
Qed.

Lemma Qabs_triangle_extend: forall (a b c:Q), Qabs (a - c) <=
   Qabs (a - b) + Qabs (b - c).
Proof. intros.
    assert (Heq: a - c == (a - b) + (b - c)) by ring.
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

Theorem Real_has_Q: forall (x1:Q) ,MCS(fun (n:nat) => x1).
Proof. 
intros. split.
- exists (x1+1). assert(x1==x1+0).
  { rewrite Qplus_0_r. reflexivity. } 
  assert (x1 + 0< x1 + 1). Search Qlt.
  { apply Qplus_lt_r. reflexivity. }
  intros. rewrite H . assert(0 + 1==1). 
  { apply Qplus_0_l. } rewrite<- Qplus_assoc.
  rewrite H1. apply H0.
- exists (x1+Qopp 1). assert(x1==x1+0).
  { rewrite Qplus_0_r. reflexivity. } 
  assert (x1 +(Qopp 1)< x1 +0 ). Search Qlt.
  { apply Qplus_lt_r. reflexivity. }
  intros. rewrite H . assert(0 +(Qopp 1)==Qopp 1). 
  { apply Qplus_0_l. } Search Qopp Qplus. rewrite<- Qplus_assoc.
  rewrite H1. apply H0.
- left. intros. apply Qle_refl.
Qed.


Notation "a == b" := (Real_equiv a b) :Real_scope.

Bind Scope Real_scope with Real.

Delimit Scope Real_scope with R.

Definition MCSPlus (A B: nat -> Q): (nat->Q) :=
  fun (n:nat) => (A n + B n).

Theorem MCS_Plus_MCS: forall A B, MCS A -> MCS B
  -> MCS (MCSPlus A B). (*where the problem lies*)

Proof. (*intros. split.
- unfold MCSPlus. destruct H. destruct H0.
  destruct P3. destruct P5. exists (x+x0). intros.
  apply QOrderedType.QOrder.le_lt_trans with (A n+x0). 
  + rewrite Qplus_le_r. apply Qlt_le_weak. apply H0.
  + apply Qplus_lt_l. apply H.
- destruct H. destruct H0. destruct P4.
  destruct P6. exists (x+x0)%nat. intros.
  unfold monotoneSeqPlus. apply Qle_trans with (A n+B(S n)).
  + apply Qplus_le_r. apply H0. unfold gt.  unfold gt in *.
    apply Nat.le_lt_trans with (x+x0)%nat. rewrite plus_comm.
    apply Nat.le_add_r. apply H1.
  + apply Qplus_le_l. apply H. unfold gt.  unfold gt in *.
    apply Nat.le_lt_trans with (x+x0)%nat. 
    apply Nat.le_add_r. apply H1.
Qed.*) Admitted.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_intro A HA) => match b with
                            | (Real_intro B HB) =>
                               Real_intro (MCSPlus A B) (MCS_Plus_MCS A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B) (at level 50,left associativity).

Definition Rzero:Real := Real_intro (fun n => 0) (Real_has_Q 0).


Theorem MCS_Plus_equiv: forall (A1 A2 B1 B2: Real),
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
    unfold MCSPlus. apply Hb in H4. apply Ha in H5.
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
    unfold MCSPlus. apply Ha in H4. apply Hb in H5.
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
  unfold Real_equiv. intros eps Heps. destruct Ha. destruct Hb.
  unfold MCSPlus. 
  exists O. intros. rewrite Qopp_plus. rewrite Qplus_assoc.
  rewrite <- (Qplus_assoc (A m)). rewrite Qplus_opp_r. rewrite Qplus_0_r.
  rewrite Qplus_opp_r. simpl. apply Heps.
Qed.

Theorem Rplus_assoc: forall (A B C: Real),
  Real_equiv (A + B + C)  (A + (B + C)).
Proof. intros. destruct A as [A Ha] ,B as [B Hb], C as [C Hc]. unfold Rplus.
  unfold Real_equiv. unfold MCSPlus. clear Ha Hb.
  exists O. intros. rewrite Qplus_assoc. rewrite Qplus_opp_r. simpl. apply H.
Qed.

Theorem Rplus_Zero: forall (A : Real),
  Real_equiv (A + Rzero) A.
Proof. intros. destruct A as [A Ha]. unfold Rzero. unfold Rplus.
  unfold Real_equiv. intros. unfold MCSPlus.
  exists O. intros. rewrite Qplus_0_r. rewrite Qplus_opp_r. apply H.
Qed.


Definition MCS_opp (A : nat -> Q): (nat->Q) :=
  fun (n:nat) => - A n.

Theorem MCS_opp_MCS: forall A, MCS A 
  -> MCS (MCS_opp A).
Proof. intros. destruct H. unfold MCS_opp. split.
- destruct P5. exists (Qopp x). intros.
  rewrite Qlt_minus_iff. rewrite Qopp_opp. rewrite Qplus_comm.
  Search Qopp. rewrite <-Qlt_minus_iff. apply H.
- destruct P4. exists (Qopp x). intros.
  rewrite Qlt_minus_iff. rewrite Qopp_opp. rewrite Qplus_comm.
  Search Qopp. rewrite <-Qlt_minus_iff. apply H.
- destruct P6. 
  + right. intros.  rewrite Qle_minus_iff. rewrite Qopp_opp. rewrite Qplus_comm.
  rewrite <-Qle_minus_iff. apply H.
  + left. intros.  rewrite Qle_minus_iff. rewrite Qopp_opp. rewrite Qplus_comm.
  rewrite <-Qle_minus_iff. apply H.
Qed.

Fixpoint Ropp(a : Real) : Real :=
  match a with
    | (Real_intro A HA) => Real_intro (MCS_opp A) (MCS_opp_MCS A HA) 
  end.

Theorem Rplus_opp_r : forall (A:Real), Real_equiv (A + (Ropp A))  Rzero.
Proof. intros. unfold Real_equiv. destruct A as [A Ha]. unfold Rzero. 
  unfold Ropp. unfold Rplus.
  unfold MCSPlus. intros.
  exists O. intros. rewrite Qplus_opp_r. apply H.
Qed.

