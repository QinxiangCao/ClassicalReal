(** * Real: Simple real number definition *)

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
Import ListNotations.

Module Definition_1.
(** In this part, we use Dedekind Cut to constructing real numbers.*)

(** First, we shoule know what is Dedekind Cut.
    According to Rudin's "principles_of_mathematical_analysis",
    a Cut is any set A which is a subset of Q with the following three properties,
      i. A is not empty, and A != Q
      ii. If p is in A, q is in Q, and q < p  =>  q is in A
      iii. If p is in A, => exists r in A, p < r.
    And we call the cuts as the members of R.
    We use the letters p,q,r to denote rational numbers and A,B,C to denote the cuts.
*)

Record Dedekind ( A : Q-> Prop) : Prop := {
  Dedekind_properties1 : (exists (x : Q) , A x) /\ (exists (x : Q) , ~ A x) ;
  Dedekind_properties2 : forall (p q : Q) , A p /\ (Qle q p) -> A q ;
  Dedekind_properties3 : forall (p : Q) , A p -> (exists r, A r /\ (Qlt p r)) ;
  Dedekind_properties4 : forall (p q : Q), p == q -> A p -> A q ;
}.

Inductive Real : Type :=
  | Real_cons (A : Q -> Prop) (H : Dedekind A)
.

(** Then we will add some properties to ensure R become a field.*)

(** First , we find some members to denote zero and one.*)

Theorem Dedekind_Q : forall x1 : Q , Dedekind (fun x=> x < x1).
Proof.
  split.
  - split.
    Search Qlt.
    exists (x1 - 1).
    + intros. unfold Qlt.
      simpl.
      rewrite -> Zmult_plus_distr_l.
      replace (Z.pos (Qden x1 * 1) % positive) with (QDen x1 * 1)%Z by reflexivity.
      repeat rewrite -> Zmult_1_r.
      rewrite <- Z.add_0_r.
      apply Zplus_lt_compat_l.
      reflexivity.
    + exists x1. apply Qlt_irrefl.
  - intros.
    inversion H.
    apply Qle_lt_trans with (y := q).
    apply Qle_lteq. right. reflexivity.
    apply Qle_lt_trans with (y := p). apply H1.
    apply H0.
  - intros.
    Search Qmake.
    exists ((p + x1) * / (2 # 1) ).
    split.
    + apply Qlt_shift_div_r. 
      reflexivity.
      assert(H' : x1 * (2 # 1) == x1 + x1).
      {
        unfold Qmult.
        unfold Qplus.
        simpl. rewrite <- Zmult_plus_distr_l.
        rewrite Zmult_comm.
        rewrite <- Z.add_diag.
        unfold Qeq.
        simpl. rewrite -> Pos.mul_1_r.
        rewrite Pos2Z.inj_mul.
        rewrite Zmult_assoc. reflexivity.
      }
      rewrite H'.
      apply Qplus_lt_le_compat. apply H. apply Qle_refl.
    + apply Qlt_shift_div_l. 
      reflexivity.
      assert(H' : p * (2 # 1) == p + p).
      {
        unfold Qmult.
        unfold Qplus.
        simpl. rewrite <- Zmult_plus_distr_l.
        rewrite Zmult_comm.
        rewrite <- Z.add_diag.
        unfold Qeq.
        simpl. rewrite -> Pos.mul_1_r.
        rewrite Pos2Z.inj_mul.
        rewrite Zmult_assoc. reflexivity.
      }
      rewrite H'.
      apply Qplus_lt_r. apply H.
  - intros. 
    apply Qle_lt_trans with p.
    + apply Qle_lteq. right.
      symmetry. apply H.
    + apply H0. 
Qed.

Definition Rzero : Real := Real_cons (fun x => x < 0) (Dedekind_Q 0).

Definition Rone : Real := Real_cons (fun x => x < 1) (Dedekind_Q 1).

(** Next, we will define the plus operation and the mult operation. *)
(** First, we will define order of Real and proof some theorem about the order.*)
Definition Rle (a b:Real) : Prop :=
  match a with
    | Real_cons A HA => match b with
                          | Real_cons B HB => (forall x , A x -> B x)
                        end
  end.

Notation "a <= b" := (Rle a b).

Definition Rlt (a b:Real) : Prop :=
  match a with
    | Real_cons A HA => match b with
                          | Real_cons B HB => (forall x , A x -> B x) /\ (exists x , B x /\ ~(A x))
                        end
  end.

Notation "a < b" := (Rlt a b).

Definition Reqb(a b : Real) : Prop := a <= b /\ b <= a.

Notation "a == b" := (Reqb a b).

Theorem Rle_refl: forall x : Real, x <= x.
Proof.
  intros.
  destruct x.
  unfold Rle.
  intros. apply H0.
Qed.

Theorem Reqb_refl: forall x : Real, x == x.
Proof.
  intros.
  unfold Reqb.
  split.
  apply Rle_refl.
  apply Rle_refl.
Qed.

Theorem Rlt_le_weak: forall x y : Real, x < y -> x <= y.
Proof.
  intros.
  destruct x.
  destruct y.
  inversion H.
  unfold Rle.
  apply H2.
Qed.

Theorem Rle_trans: forall x y z : Real, x <= y -> y <= z -> x <= z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  intros.
  apply H0. apply H. apply H4.
Qed.

Theorem Rlt_trans: forall x y z : Real, x < y -> y < z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H. destruct H0. inversion H4. inversion H5. 
    exists x. split. apply H0. apply H6. apply H6.
Qed.

Theorem Rle_not_lt: forall x y : Real, x <= y -> ~ y < x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold not.
  unfold Rle in *.
  unfold Rlt.
  simpl.
  intros.
  destruct H2.
  inversion H3.
  destruct H4.
  apply H in H4.
  apply H5. apply H4.
Qed.

Theorem Rlt_not_le: forall x y : Real, x < y -> ~ y <= x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold not.
  unfold Rle.
  unfold Rlt in *.
  simpl.
  intros.
  destruct H.
  inversion H3.
  destruct H4.
  apply H2 in H4.
  apply H5. apply H4.
Qed.

Theorem Rle_antisym: forall x y : Real, x <= y -> y <= x -> x == y.
Proof.
  intros.
  unfold Reqb.
  split. apply H. apply H0.
Qed.

Theorem Rle_lt_trans: forall x y z : Real, x <= y -> y < z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H0.
    destruct H4.
    exists x.
    split.
    + apply H4.
    + unfold not in *.
      intros.
      apply H4. apply H. apply H5.
Qed.

Theorem Rlt_le_trans: forall x y z : Real, x < y -> y <= z -> x < z.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold Rle in *.
  unfold Rlt in *.
  split.
  - intros. apply H0. apply H. apply H4.
  - destruct H.
    destruct H4.
    exists x.
    split.
    + apply H0. apply H4.
    + unfold not in *.
      intros.
      apply H4. apply H5.
Qed.

Theorem not_exists_not_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) <-> (forall x, P x).
Proof.
  split.
  - apply not_ex_not_all.
  - unfold not. intros. destruct H0. apply H0. apply H.
Qed.

Theorem not_exists_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, P x) <-> (forall x, ~ P x).
Proof.
  split.
  - apply not_ex_all_not.
  - unfold not. intros. destruct H0. apply H in H0. apply H0.
Qed.

Theorem Rnot_le_lt: forall x y : Real, ~ x <= y -> y < x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold Rle in *.
  unfold Rlt in *.
  destruct H0, H1.
  split.
  - apply not_all_ex_not in H.
    rewrite <- not_exists_not_dist.
    unfold not in *. intros.
    destruct H, H0.
    assert(H': Qle x x0 \/ Qle x0 x).
    { assert(H'':Qle x x0 \/ ~ Qle x x0). apply classic.
      destruct H''.
      - left. apply H1.
      - right. apply Qnot_le_lt in H1. apply Qlt_le_weak. apply H1. }
    destruct H'.
    + apply H0. intros. exfalso. apply H. intros.
      apply (Dedekind_properties10 x0 x ).
      split.
      apply H2. apply H1.
    + apply H. intros. exfalso. apply H0. intros.
      apply (Dedekind_properties6 x x0 ).
      split.
      apply H2. apply H1.
  - apply not_all_ex_not in H.
    destruct H.
    exists x.
    split.
    + apply not_imply_elim in H. apply H.
    + apply not_imply_elim2 in H. apply H.
Qed.

Theorem Rnot_lt_le: forall x y : Real, ~ x < y -> y <= x.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold Rle in *.
  unfold Rlt in *.
  destruct H0, H1.
  apply not_and_or in H.
  destruct H.
  - apply not_all_ex_not in H.
    rewrite <- not_exists_not_dist.
    unfold not in *. intros.
    destruct H, H0.
    assert(H': Qle x x0 \/ Qle x0 x).
    { assert(H'':Qle x x0 \/ ~ Qle x x0). apply classic.
      destruct H''.
      - left. apply H1.
      - right. apply Qnot_le_lt in H1. apply Qlt_le_weak. apply H1. }
    destruct H'.
    + apply H0. intros. exfalso. apply H. intros.
      apply (Dedekind_properties10 x0 x ).
      split.
      apply H2. apply H1.
    + apply H. intros. exfalso. apply H0. intros.
      apply (Dedekind_properties6 x x0 ).
      split.
      apply H2. apply H1.
  - rewrite not_exists_dist in H.
    intros.
    assert(H': ~(A0 x /\ ~ A x)).
    { apply H. }
    apply not_and_or in H'.
    destruct H'.
    + exfalso. apply H1. apply H0.
    + apply NNPP in H1. apply H1.
Qed.

(** Second , we will define the plus operation of Set and Real and proof some theorem about it. *)

Definition Cut_plus_Cut (A : Q -> Prop) (B : Q -> Prop) : Q -> Prop :=
  (fun x => exists x0 x1 : Q, A x0 /\ B x1 /\ (Qeq (x0 + x1) x))
.

Lemma Dedekind_le : forall A x x1, Dedekind A -> (~ A x) -> A x1 -> x > x1.
Proof.
  intros.
  destruct H.
  apply Qnot_le_lt.
  unfold not.
  intros. 
  apply H0. 
  apply Dedekind_properties6 with x1.
  split.
  apply H1.
  apply H.
Qed.

Theorem Dedekind_plus : forall A B, Dedekind A -> Dedekind B -> Dedekind (Cut_plus_Cut A B).
Proof.
  intros.
  inversion H.
  inversion H0.
  split.
  - destruct Dedekind_properties5.
    destruct Dedekind_properties9.
    split.
    + inversion H1.
      inversion H3.
      exists (x0 + x), x , x0.
      split.
      * apply H5.
      * split. 
        apply H6.
        apply Qplus_comm.
    + inversion H2. inversion H4.
      unfold not in *.
      exists (x + x0).
      intros. destruct H7. destruct H7.
      assert (H' : x > x1 /\ x0 > x2).
      {
        split.
        apply Dedekind_le with A.
        apply H. unfold not. apply H5. apply H7.
        apply Dedekind_le with B.
        apply H0. unfold not. apply H6. apply H7.
      }
      assert (H'' : Qlt (x1 + x2)(x + x0)).
      {
        apply Qplus_lt_le_compat.  apply H'.
        apply Qlt_le_weak.  apply H'.
      }
      destruct H7.  destruct H8. rewrite H9 in H''.
      apply Qlt_irrefl with (x + x0). apply H''.
  - intros.
    destruct H1. destruct H1. destruct H1.
    unfold Cut_plus_Cut.
    exists x , (q + - x).
    split. apply H1.
    split. apply Dedekind_properties10 with x0.
    split. apply H1. 
    apply Qplus_le_l with (z := x).
    destruct H1. destruct H3.
    rewrite Qplus_comm in H4.
    rewrite H4.  apply Qle_trans with q.
    rewrite <- Qplus_assoc.  rewrite (Qplus_comm (- x)).
    rewrite Qplus_opp_r.  rewrite Qplus_0_r.
    apply Qle_refl. apply H2.
    rewrite Qplus_comm. rewrite <- Qplus_assoc.
    rewrite (Qplus_comm (- x)).  rewrite Qplus_opp_r.
    apply Qplus_0_r.
  - intros.
    repeat destruct H1. destruct H2.
    apply Dedekind_properties7 in H1.
    apply Dedekind_properties11 in H2 as goal.
    destruct H1. destruct goal.
    exists (x1 + x0).
    split. unfold Cut_plus_Cut.
    exists x1,x0.
    split. apply H1.
    split. apply H2. reflexivity.
    rewrite <- H3.
    apply Qplus_lt_l.  apply H1.
  - intros.
    repeat destruct H2.
    unfold Cut_plus_Cut.
    exists x,x0.
    split. apply H2.
    split. apply H3.
    rewrite <- H1. apply H3.
Qed.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_cons A HA) => match b with
                            | (Real_cons B HB) =>
                               Real_cons (Cut_plus_Cut A B) (Dedekind_plus A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B).

Theorem Rplus_O_r : forall a : Real, a + Rzero == a.
Proof.
  intros.
  destruct a.
  unfold Rplus.
  simpl.
  unfold Reqb.
  unfold Rle.
  destruct H.
  split.
  - intros.
    destruct H.
    destruct H.
    apply Dedekind_properties6 with x0.
    split.
    + apply H.
    + destruct H. destruct H0.
      rewrite <- Qplus_0_r with (x := x0).
      rewrite <- H1.
      apply Qplus_le_r.
      apply Qlt_le_weak. apply H0.
  - intros.
    unfold Cut_plus_Cut.
    apply Dedekind_properties7 in H.
    destruct H.
    exists x0,(Qplus x (-x0)).
    split.
    + apply H.
    + split.
      * apply Qplus_lt_l with (z := x0).
        rewrite Qplus_0_l.
        rewrite <- Qplus_assoc.
        rewrite Qplus_comm with (y := x0).
        rewrite Qplus_opp_r.
        rewrite Qplus_0_r. apply H.
      * rewrite Qplus_comm.
        rewrite <- Qplus_assoc.
        rewrite Qplus_comm with (y := x0).
        rewrite Qplus_opp_r.
        apply Qplus_0_r.
Qed. 

Theorem Rplus_comm : forall a b : Real, a + b == b + a.
Proof.
  intros.
  destruct a.
  destruct b.
  unfold Reqb.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H1; destruct H2; exists x1,x0.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
Qed. 

Theorem Rplus_assoc : forall a b c : Real, a + b + c == a + (b + c).
Proof.
  intros.
  destruct a.
  destruct b.
  destruct c.
  unfold Reqb.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H2; repeat destruct H3.
  - exists x2 , (Qplus x (-x2)).
    split. apply H2.
    split.
    + exists x3 , x1.
      split. apply H4.
      split. apply H3.
      rewrite <- H5. destruct H4. rewrite <- H6.
      remember (Qplus x3 x1) as xp.
      rewrite <- Qplus_comm. rewrite <- Qplus_assoc. rewrite <- Heqxp.
      rewrite Qplus_comm with (y := xp).
      rewrite Qplus_comm. rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      symmetry. apply Qplus_0_r.
    + rewrite Qplus_comm with (x := x).
      rewrite Qplus_assoc. rewrite Qplus_opp_r. apply Qplus_0_l.
  - exists (Qplus x (-x3)) , x3.
    split.
    + exists x0,x2.
      split. apply H2.
      split. apply H3.
      rewrite <- H4. destruct H5. rewrite <- H6.
      rewrite <- Qplus_assoc.
      rewrite <- Qplus_assoc.
      rewrite Qplus_opp_r. rewrite Qplus_0_r. reflexivity.
    + split. apply H5.
      rewrite <- Qplus_assoc.
      rewrite Qplus_comm with (y:=x3).
      rewrite Qplus_opp_r.
      apply Qplus_0_r.
Qed.

Definition Cut_opp (A : Q -> Prop) : Q -> Prop :=
  (fun x => exists r : Q, (r > 0 -> ~(A (Qplus (-x) (-r)))))
.

Theorem Dedekind_opp : forall A : Q -> Prop , Dedekind A -> Dedekind (Cut_opp A).
Proof.
  intros.
  destruct H.
  unfold Cut_opp.
  split.
  - destruct Dedekind_properties5. split.
    + destruct H0.
      exists (Qplus (- x) (-1 # 1) ), 1.
      remember (Qplus (- x) (-1 # 1) ) as x0.
      unfold not in *.  intros.   apply H0.
      apply Dedekind_properties8 with (p := Qplus (- x0)  (- (1))).
      * apply Qplus_inj_l with (z := x0).
        rewrite Qplus_assoc.  rewrite Qplus_opp_r.
        rewrite Qplus_0_l. rewrite Qplus_comm.
        rewrite Heqx0.
        rewrite Qplus_assoc. rewrite Qplus_opp_r.
        reflexivity.
      * apply H2.
   + destruct H.
     exists (-x).
     apply not_exists_dist.
     intros.
     unfold not.
     intros.
     assert (H' : (Qlt 0 x0)\/ ~(Qlt 0 x0)).
Admitted.

Definition Ropp (a : Real) : Real :=
  match a with
    | Real_cons A HA => Real_cons (Cut_opp A) (Dedekind_opp A HA)
  end.

Notation " - a" := (Ropp a).

Theorem Rplus_opp :
  forall a : Real, a + - a == Rzero.
Proof.
Admitted.

Theorem Rplus_l_compat :
  forall a b c : Real, b == c -> a + b == a + c.
Proof. 
  unfold Reqb, Rle. destruct a, b, c. simpl. unfold Cut_plus_Cut.
  intros.
  destruct H2.
  split.
  - intros.
    destruct H4, H4, H4, H5.
    exists x0, x1.
    split. apply H4.
    split. apply H2, H5.
    apply H6.
  - intros.
    destruct H4, H4, H4, H5.
    exists x0, x1.
    split. apply H4.
    split. apply H3, H5.
    apply H6.
Qed.

Theorem Rplus_compat_l :
  forall a b c : Real, a + b == a + c -> b == c.
Proof. 
Admitted.

(** Third , we will define the plus operation of Set and Real and proof some theorem about it. *)
Theorem Rmult_O : forall a : Real, a * Rzero == Rzero.
Proof.
Admitted.

Theorem Rmult_1 : forall a : Real, a * Rone == a.
Proof.
Admitted.

Theorem Rmult_comm : forall a b : Real, a * b == b * a.
Proof.
Admitted.

Theorem Rmult_assoc : forall a b c : Real, a * b * c == a * (b * c).
Proof.
Admitted.

Theorem Rmult_distr :
  forall a b c : Real, a * (b + c) == (a * b) + (a * c).
Proof.
Admitted.

Theorem Rmult_inv :
  forall a : Real, (a <> Rzero) -> exists b, a * b == Rone.
Proof.
Admitted.

End Definition_1.

(* Sat 2019.3.2 16:37 Wu Xiwei , Hu Zhixuan *)
