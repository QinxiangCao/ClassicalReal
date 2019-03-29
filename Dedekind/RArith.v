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
From CReal Require Import Dedekind.RBase.
From CReal Require Import Dedekind.ROrder.
Import ListNotations.

(** Second , we will define the plus operation of Set and Real and proof some theorem about it. *)

Definition Cut_plus_Cut (A : Q -> Prop) (B : Q -> Prop) : Q -> Prop :=
  (fun x => exists x0 x1 : Q, A x0 /\ B x1 /\ (Qeq (x0 + x1) x))
.

Theorem Dedekind_plus : forall A B, Dedekind A -> Dedekind B -> Dedekind (Cut_plus_Cut A B).
Proof.
  intros.
  rename H into DA, H0 into DB.
  split.
  - destruct (Dedekind_properties1 _ DA).
    destruct (Dedekind_properties1 _ DB).
    split.
    + inversion H.
      inversion H1.
      exists (x0 + x), x , x0.
      split.
      * apply H3.
      * split. 
        apply H4.
        apply Qplus_comm.
    + inversion H0. inversion H2.
      unfold not in *.
      exists (x + x0).
      intros. destruct H5. destruct H5.
      assert (H' : x > x1 /\ x0 > x2).
      {
        split.
        apply Dedekind_le with A.
        apply DA. unfold not. apply H3. apply H5.
        apply Dedekind_le with B.
        apply DB. unfold not. apply H4. apply H5.
      }
      assert (H'' : Qlt (x1 + x2)(x + x0)).
      {
        apply Qplus_lt_le_compat.  apply H'.
        apply Qlt_le_weak.  apply H'.
      }
      destruct H5.  destruct H6. rewrite H7 in H''.
      apply Qlt_irrefl with (x + x0). apply H''.
  - intros.
    destruct H. destruct H. destruct H.
    unfold Cut_plus_Cut.
    exists x , (q + - x).
    split; [apply H |].
    split; [apply (Dedekind_properties2 _ DB) with x0 |].
    split; [apply H |]. 
    apply Qplus_le_l with (z := x).
    destruct H. destruct H1.
    rewrite Qplus_comm in H2.
    rewrite H2.  apply Qle_trans with q.
    rewrite <- Qplus_assoc.  rewrite (Qplus_comm (- x)).
    rewrite Qplus_opp_r.  rewrite Qplus_0_r.
    apply Qle_refl. apply H0.
    rewrite Qplus_comm. rewrite <- Qplus_assoc.
    rewrite (Qplus_comm (- x)).  rewrite Qplus_opp_r.
    apply Qplus_0_r.
  - intros.
    repeat destruct H. destruct H0.
    apply (Dedekind_properties3 _ DA) in H.
    apply (Dedekind_properties3 _ DB) in H0 as goal.
    destruct H. destruct goal.
    exists (x1 + x0).
    split. unfold Cut_plus_Cut.
    exists x1,x0.
    split. apply H.
    split. apply H0. reflexivity.
    rewrite <- H1.
    apply Qplus_lt_l.  apply H.
  - intros.
    repeat destruct H0.
    unfold Cut_plus_Cut.
    exists x,x0.
    split. apply H0.
    split. apply H1.
    rewrite <- H. apply H1.
Qed.

Fixpoint Rplus(a b : Real) : Real :=
  match a with
    | (Real_cons A HA) => match b with
                            | (Real_cons B HB) =>
                               Real_cons (Cut_plus_Cut A B) (Dedekind_plus A B HA HB)
                          end
  end.

Notation "A + B" := (Rplus A B) (at level 50, left associativity)
                       : R_scope.

Theorem Rplus_O_r : forall a : Real, (a + Rzero)%R == a.
Proof.
  intros.
  destruct a.
  unfold Rplus.
  simpl.
  unfold Req.
  unfold Rle.
  rename H into DA.
  split.
  - intros.
    destruct H.
    destruct H.
    apply (Dedekind_properties2 _ DA) with x0.
    split.
    + apply H.
    + destruct H. destruct H0.
      rewrite <- Qplus_0_r with (x := x0).
      rewrite <- H1.
      apply Qplus_le_r.
      apply Qlt_le_weak. apply H0.
  - intros.
    unfold Cut_plus_Cut.
    apply (Dedekind_properties3 _ DA) in H.
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

Theorem Rplus_comm : forall a b : Real, (a + b)%R == (b + a)%R.
Proof.
  intros.
  destruct a.
  destruct b.
  unfold Req.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H1; destruct H2; exists x1,x0.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
  - split.  apply H2. split. apply H1. rewrite <- H3. apply Qplus_comm.
Qed.

Theorem Rplus_assoc : forall a b c : Real, (a + b + c)%R == (a + (b + c))%R.
Proof.
  intros.
  destruct a.
  destruct b.
  destruct c.
  unfold Req.
  unfold Rplus.
  simpl.
  unfold Cut_plus_Cut.
  split; intros; repeat destruct H2; repeat destruct H3.
  - exists x2 , (x + -x2).
    split. apply H2.
    split.
    + exists x3 , x1.
      split. apply H4.
      split. apply H3.
      rewrite <- H5. destruct H4. rewrite <- H6.
      remember (x3 + x1) as xp.
      rewrite <- Qplus_comm. rewrite <- Qplus_assoc. rewrite <- Heqxp.
      rewrite Qplus_comm with (y := xp).
      rewrite Qplus_comm. rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      symmetry. apply Qplus_0_r.
    + rewrite Qplus_comm with (x := x).
      rewrite Qplus_assoc. rewrite Qplus_opp_r. apply Qplus_0_l.
  - exists (x + - x3) , x3.
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
  (fun x => exists r : Q, (r > 0 /\ ~(A (-x + -r))))
.

Theorem Dedekind_opp : forall A : Q -> Prop , Dedekind A -> Dedekind (Cut_opp A).
Proof.
  intros.
  rename H into DA.
  unfold Cut_opp.
  split.
  - destruct (Dedekind_properties1 _ DA). split.
    + destruct H0.
      exists (- x +  (-1 # 1) ), 1.
      remember ((- x) + (-1 # 1) ) as x0.
      unfold not in *. split. reflexivity. intros.   apply H0.
      apply (Dedekind_properties4 _ DA) with (p := (- x0) + (- (1))).
      * apply Qplus_inj_l with (z := x0).
        rewrite Qplus_assoc.  rewrite Qplus_opp_r.
        rewrite Qplus_0_l. rewrite Qplus_comm.
        rewrite Heqx0.
        rewrite Qplus_assoc. rewrite Qplus_opp_r.
        reflexivity.
      * apply H1.
    + destruct H.
      exists (-x).
      apply not_exists_dist.
      intros.
      unfold not.
      intros.
      assert (H' : (Qlt 0 x0) -> A (- - x + - x0)).
      { intros.
        assert(H': (--x == x)%Q).
        { apply Qopp_involutive. }
        { apply (Dedekind_properties2 _ DA x).
          split.
          * apply H.
          * rewrite <- (Qplus_0_r x).
            apply Qplus_le_compat. rewrite Qplus_0_r. rewrite H'. apply Qle_refl.
            apply (Qopp_le_compat 0 x0).
            apply Qlt_le_weak. apply H2. } }
      destruct H1. apply H2. apply H'. apply H1.
  - intros. destruct H. destruct H. destruct H. 
    exists x. split.
    + apply H.
    + unfold not. intros. apply H1. apply (Dedekind_properties2 _ DA (Qplus (Qopp q) (Qopp x))).
      split.
      * apply H2.
      * apply Qplus_le_compat. apply Qopp_le_compat. apply H0. apply Qle_refl.
  - intros.
    inversion H.
    exists (p + (x * / (2 # 1))).
    split.
    exists (x * / (2 # 1)).
    split.
    + assert (H' : (0 == (0 * / (2 # 1)))%Q).
      { reflexivity. }
      rewrite H'.
      apply Qmult_lt_compat_r.
      reflexivity.
      apply H0.
    + unfold not in *.
      intros. apply H0.
      apply (Dedekind_properties4 _ DA) with (p := (- ( p + (x * / (2 # 1)))) + (-(x * / (2 # 1)))).
      assert (H' : (x == ((x * / (2 # 1)) + (x * / (2 # 1))))%Q).
      { rewrite <- Qmult_plus_distr_r. rewrite <- Qmult_1_r.
        rewrite <- Qmult_assoc.
        rewrite Qmult_inj_l with (z := x).
        reflexivity.
        apply Qnot_eq_sym. apply Qlt_not_eq. apply H0.
      }
      apply Qplus_inj_l with (z := p + (x * / (2 # 1))).
      rewrite Qplus_assoc. rewrite Qplus_opp_r.
      rewrite Qplus_0_l.  rewrite Qplus_assoc.  rewrite Qplus_comm.
      rewrite Qplus_comm with (x := p).
      rewrite <- Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_r.
      rewrite Qplus_comm.
      apply Qplus_inj_l with (z := (x * / (2 # 1))).
      rewrite Qplus_opp_r. rewrite Qplus_assoc.
      rewrite <- H'. symmetry.
      apply Qplus_opp_r.
      apply H1.
    + rewrite <- Qplus_0_r.
      rewrite <- Qplus_assoc.
      rewrite Qplus_lt_r with (z := p).
      rewrite Qplus_0_l.
      apply Qlt_shift_div_l ; try (reflexivity).
      assert (H' : (0 == (0 * (2 # 1)))%Q).
      { reflexivity. }
      rewrite <- H'. apply H0.
  - intros.
    inversion H0.
    exists x.
    split. apply H1.
    unfold not in *.
    intros.
    apply H1.
    apply (Dedekind_properties4 _ DA) with (p := Qplus (-q) (-x)).
    apply Qplus_inj_r.
    apply Qplus_inj_l with (z := p + q).
    rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
    rewrite Qplus_0_r.
    rewrite <- Qplus_assoc. rewrite Qplus_comm with (x := q). 
    rewrite Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_l.
    apply H. apply H2.
Qed.

Definition Ropp (a : Real) : Real :=
  match a with
    | Real_cons A HA => Real_cons (Cut_opp A) (Dedekind_opp A HA)
  end.

Notation " - a" := (Ropp a) : R_scope.

Lemma PPNN : forall P :Prop, P -> ~ ~ P.
Proof.
  intros. unfold not. intros. apply H0, H.
Qed.

Lemma inverse_not: forall P Q : Prop,  (P -> Q) <-> (~ Q -> ~ P).
Proof.
  split.
  intros. apply imply_to_or in H. destruct H. apply H. exfalso. apply H0, H.
  intros. apply imply_to_or in H. destruct H. apply NNPP, H. exfalso. apply H, H0.
Qed.

Theorem exists_dist :
  forall (X:Type) (P : X -> Prop),
    (exists x, P x) <-> ~ (forall x, ~ P x).
Proof.
  intros. split.
  - apply inverse_not. intros. rewrite not_exists_dist. apply NNPP, H.
  - apply inverse_not. intros. rewrite <- not_exists_dist. apply PPNN, H.
Qed.

Lemma Qarchimedean : forall p q :Q, p > 0 -> q > 0 -> exists n : Q, n*p>q.
Proof.
  intros. exists ((q*/p)+1)%Q. rewrite Qmult_plus_distr_l.
  assert(H':(~p==0)%Q).
  { apply Qlt_not_eq in H.
    unfold not.
    intros.
    apply H. rewrite H1. reflexivity.
  }
  rewrite Qmult_comm.
  apply (Qmult_div_r q) in H'.
  rewrite H'.
  rewrite Qmult_1_l.
  apply Qplus_lt_l with (z:=0).
  rewrite <- Qplus_assoc.
  rewrite Qplus_lt_r with (z:=q).
  rewrite Qplus_0_r. apply H.
Qed.

Lemma mylemma1 : forall (A : Q -> Prop),
 Dedekind A -> ~ (forall x : Q, A x -> A (x + 1)).
Proof.
  intros.
  destruct (Dedekind_properties1 _ H ).
  destruct H0, H1.
  unfold not.
  intros.
Admitted.

Lemma Rarchimedean : forall (A : Q -> Prop),
 Dedekind A -> (exists n:Q, A n /\ ~ A(n + 1)).
Proof.
  intros. destruct (Dedekind_properties1 _ H ).
  destruct H0, H1.
  (* exists m:Z, m > 0 /\ x0 - m < x.
     exists m:Z, m = 0 /\ x0 - m > x. *)
  (* Define: P (u: nat) := x0 - u > x.
     P 0, ~ P m, -> exists n, P n /\ ~ P (n + 1). *)
  Check Z.of_nat.
  Check Z.to_nat.
  SearchAbout Z Q.
  Check inject_Z.
(** Check these functions and proof approached. -- Qinxiang  *)
  rewrite exists_dist. unfold not. intros.
Admitted.

Theorem Rplus_opp :
  forall a : Real, (a + (Ropp a))%R == Rzero.
Proof.
  intros.
  destruct a.
  unfold Req.
  simpl. split.
  - intros.
    repeat destruct H0.
    destruct H1.
    destruct H1.
    destruct H1.
    rewrite <- H2.
    apply Qplus_lt_l with (z := (-x1)).
    rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
    rewrite Qplus_0_r. rewrite Qplus_0_l.
    apply Qlt_trans with (y := Qplus (-x1) (-x2)).
    apply Dedekind_le with A ; auto.
    apply Qplus_lt_r with (z := Qplus x2 x1).
    rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite <- Qplus_comm. rewrite Qplus_assoc. 
    rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite Qplus_comm.
    rewrite Qplus_opp_r. rewrite Qplus_0_r. apply H1.
  - intros.
    unfold Cut_plus_Cut.
    rename H into DA.
    destruct (Dedekind_properties1 _ DA).
    destruct H. destruct H1.
    assert(H': (exists x2 : Q, A x2 /\ Cut_opp A (x - x2))
     -> exists x2 x3 : Q, A x2 /\ Cut_opp A x3 /\ (x2 + x3 == x)%Q).
    { intros.
      destruct H2.
      exists x2, (Qplus x (-x2)).
      split. apply H2.
      split. apply H2.
      rewrite Qplus_assoc. rewrite <- Qplus_comm. rewrite Qplus_assoc.
      rewrite <- (Qplus_comm x2). rewrite Qplus_opp_r. rewrite Qplus_0_l. reflexivity.
    }
    apply H'. unfold Cut_opp.
    
(*     exists x0, (Qplus (-x0) x).
    split; [apply H |].
    split.
    * unfold Cut_opp.
      destruct H1.
      exists (Qplus (-x1) (Qplus (-x0) (-x))).
      split.
     ++ apply Qplus_lt_l with (z := Qplus x0 x).
        rewrite Qplus_0_l. rewrite <- Qplus_assoc.
        assert (H' : Qeq (Qplus (Qplus (-x0) (-x)) (Qplus x0 x)) 0).
        {
          rewrite Qplus_assoc.
          rewrite Qplus_comm.
          rewrite <- Qplus_assoc.
          rewrite Qplus_comm with (y := Qplus (-x) x0).
          rewrite <- Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_r.
          apply Qplus_opp_r.
        }
        rewrite H'. 
        apply Qplus_lt_le_compat.
        apply Dedekind_le with A ; auto. *)
Abort.

Theorem Rplus_l_compat :
  forall a b c : Real, b == c -> (a + b == a + c)%R.
Proof. 
  unfold Req, Rle. destruct a, b, c. simpl. unfold Cut_plus_Cut.
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
  forall a b c : Real, (a + b == a + c)%R -> b == c.
Proof. 
Admitted.

Definition Cut_multPP (A B : Q -> Prop) : Q -> Prop :=
 (fun x => (exists x0 x1 : Q, x0>0 /\ x1>0 /\ A x0 /\ B x1 /\ (x <= (x0*x1))))
.
Definition Cut_multNP (A B : Q -> Prop) : Q -> Prop :=
 Cut_opp (fun x => (exists x0 x1 : Q, x0>0 /\ x1>0 /\ Cut_opp A x0 /\ B x1 /\ (x <= (x0*x1))))
.
Definition Cut_multPN (A B : Q -> Prop) : Q -> Prop :=
 Cut_opp (fun x => (exists x0 x1 : Q, x0>0 /\ x1>0 /\ A x0 /\ Cut_opp B x1 /\ (x <= (x0*x1))))
.
Definition Cut_multNN (A B : Q -> Prop) : Q -> Prop :=
 (fun x => (exists x0 x1 : Q, x0>0 /\ x1>0 /\ Cut_opp A x0 /\ Cut_opp B x1 /\ (x <= (x0*x1))))
.
Definition Cut_mult0 (A B : Q -> Prop) : Q -> Prop :=
 (fun x =>  x<0)
.

Definition Cut_mult : (Q -> Prop) -> (Q -> Prop) -> (Q -> Prop):=
  (fun A B x => (A 0 /\ B 0 /\ Cut_multPP A B x) \/
                (Cut_opp A 0 /\ B 0 /\ Cut_multNP A B x) \/
                (A 0 /\Cut_opp B 0 /\ Cut_multPN A B x) \/
                (Cut_opp A 0 /\ Cut_opp B 0 /\ Cut_multNN A B x)\/
                ((~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0))
                /\ Cut_mult0 A B x)
.

Lemma Cut_multPP_spec: forall A B: Q -> Prop,
  A 0 -> B 0 ->
  (forall x, Cut_multPP A B x <-> Cut_mult A B x).
Abort.
(** Use this lemma to separate the proof that "the multiplication of
two Dedekind cut is still a Dedekind cut". -- Qinxiang *)

(** To make sure the definition is correct.  *)
Lemma Rmult_situation : forall A B, Dedekind A -> Dedekind B ->
  (A 0/\B 0)\/
  (Cut_opp A 0 /\ B 0)\/
  (A 0 /\Cut_opp B 0)\/
  (Cut_opp A 0 /\ Cut_opp B 0)\/
  (~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0).
Proof.
  intros.
  assert(A 0 \/~ A 0).  { apply classic. }
  assert(B 0 \/~ B 0).  { apply classic. }
  assert(Cut_opp A 0 \/~ Cut_opp A 0).  { apply classic. }
  assert(Cut_opp B 0 \/~ Cut_opp B 0).  { apply classic. }
  destruct H1, H2.
  - left. split. auto. auto.
  - destruct H4.
    + right. right. left. split. auto. auto.
    + repeat right. split. auto. auto.
  - destruct H3.
    + right. left. split. auto. auto.
    + right. right. right. right. left. split. auto. auto.
  - destruct H3.
    + destruct H4.
      * right. right. right. left. split. auto. auto.
      * repeat right; split; auto.
    + right. right. right. right. left. split. auto. auto.
Qed.

(** Write definition like this:
Definition Cut_mult: (Q -> Prop) -> (Q -> Prop) -> (Q -> Prop) :=
  fun A B x =>
    (A 0 /\ B 0 /\ Cut_multPP A B x) \/
    ..
    
    
    -- Qinxiang *)

Fact Qdiv2 : forall x : Q, (x == ((x * / (2 # 1)) + (x * / (2 # 1))))%Q.
Proof.
  intros. assert( x == 0 \/~ x == 0)%Q. { apply classic. } destruct H.
  - rewrite H. reflexivity.
  - rewrite <- Qmult_plus_distr_r. rewrite <- Qmult_1_r.
    rewrite <- Qmult_assoc.
    rewrite Qmult_inj_l with (z := x).
    reflexivity. apply H.
Qed.

Fact Qdiv2_opp : forall x : Q, (- x == - (x * / (2 # 1)) + - (x * / (2 # 1)))%Q.
Proof.
  intros.
  rewrite <- Qplus_inj_l with (z:=(x / (2 # 1))).
  rewrite Qplus_assoc.
  rewrite Qplus_opp_r with (q:=(x / (2 # 1))). rewrite Qplus_0_l.
  rewrite <- Qplus_inj_l with (z:=(x / (2 # 1))).
  rewrite Qplus_assoc.
  rewrite Qplus_opp_r with (q:=(x / (2 # 1))).
  rewrite <- Qplus_inj_r with (z:=x).
  rewrite <- Qplus_assoc. rewrite (Qplus_comm (-x) x ).
  rewrite Qplus_opp_r with (q:=x).
  rewrite Qplus_0_l. rewrite Qplus_0_r.
  symmetry. apply Qdiv2.
Qed.

Fact Qdiv2_x_y : forall x y :Q, x>0 -> y>0 -> x / (2 # 1) * (y / (2 # 1)) <= x * y.
Proof.
  unfold Qdiv. intros. rewrite Qmult_assoc.
  rewrite (Qmult_comm x (/(2#1))).
  rewrite <- (Qmult_assoc (/(2#1)) x y).
  rewrite <- (Qmult_comm (x*y) (/(2#1))).
  rewrite <- (Qmult_assoc (x*y) (/(2#1)) (/(2#1)) ).
  rewrite (Qmult_comm x y). rewrite <- (Qmult_1_r (y*x)).
  rewrite <- (Qmult_assoc (y*x) 1 ((/(2#1)) *(/(2#1)))).
  apply Qlt_le_weak.
  rewrite Qmult_lt_l.
  { reflexivity. }
  { SearchAbout Qmult Qlt. rewrite <- (Qmult_0_l x). apply (Qmult_lt_compat_r 0 y x).
  auto. auto. }
Qed.

Lemma Qmult_lt_compat : forall x y z t : Q,
0 < x -> 0 < z -> x < y -> z < t -> x * z < y * t .
Proof.
  intros. apply Qlt_trans with (y:= y*z).
  - apply Qmult_lt_compat_r. auto. auto.
  - rewrite Qmult_comm. rewrite (Qmult_comm y t).
    apply Qmult_lt_compat_r.
    apply Qlt_trans with (y:=x). auto. auto. auto.
Qed.


Theorem Dedekind_mult (A B : Q -> Prop) : 
Dedekind A -> Dedekind B -> Dedekind (Cut_mult A B).
Proof.
  intros. split.
  - split.
    + unfold Cut_mult.
      assert(
  (A 0/\B 0)\/
  (Cut_opp A 0 /\ B 0)\/
  (A 0 /\Cut_opp B 0)\/
  (Cut_opp A 0 /\ Cut_opp B 0)\/
  (~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0)).
      { apply Rmult_situation. auto. auto. }
        destruct H1. destruct H1.
      * destruct (Dedekind_properties3 _ H 0). apply H1.
        destruct (Dedekind_properties3 _ H0 0). apply H2.
        exists (x*x0). left.
        repeat split; auto.
        unfold Cut_multPP. exists x, x0. destruct H3, H4.
        repeat split; auto. apply Qle_refl.
      * destruct H1. ** destruct H1.
        assert(Dedekind (Cut_opp A)).
        { apply Dedekind_opp, H. }
        destruct (Dedekind_properties1 _ H3). destruct H5.
        destruct (Dedekind_properties1 _ H0). destruct H7.
        assert(x>0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H5.
          apply (Dedekind_properties2 _ H3 0).
          split. auto. auto. }
        assert(x0>0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H7.
          apply (Dedekind_properties2 _ H0 0).
          split. auto. auto. }
        exists (-((2#1)*x*x0)). right. left. repeat split; auto.
        exists (x*x0). split. rewrite <- (Qmult_0_l x0).
        apply (Qmult_lt_compat_r 0 x x0). auto. auto.
        unfold not. intros.
        destruct H10, H10, H10, H11, H12, H13.
        assert(x1<x).
        { apply (Dedekind_le (Cut_opp A)). auto. apply H5. auto. }
        assert(x2<x0).
        { apply (Dedekind_le B). auto. apply H7. auto. }
        rewrite Qopp_involutive in H14.
        rewrite <- (Qmult_assoc (2#1) x x0) in H14.
        rewrite <- (Qmult_1_l (-(x*x0))) in H14.
        assert((1 * (- (x * x0)) == (- 1%Q) * (x * x0))%Q).
        { rewrite Qmult_1_l. reflexivity. }
        rewrite H17 in H14.
        rewrite <- (Qmult_plus_distr_l (2#1) (-1%Q) (x*x0)) in H14.
        assert(((2 # 1) + - (1))==1)%Q. reflexivity.
        rewrite H18 in H14. rewrite Qmult_1_l in H14.
        apply Qle_not_lt in H14. apply H14.
        apply Qmult_lt_compat. auto. auto. auto. auto.
     ** destruct H1. *** destruct H1.
        assert(Dedekind (Cut_opp B)).
        { apply Dedekind_opp, H0. }
        destruct (Dedekind_properties1 _ H3). destruct H5.
        destruct (Dedekind_properties1 _ H). destruct H7.
        assert(x>0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H5.
          apply (Dedekind_properties2 _ H3 0).
          split. auto. auto. }
        assert(x0>0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H7.
          apply (Dedekind_properties2 _ H 0).
          split. auto. auto. }
        exists (-((2#1)*x*x0)). right. right. left. repeat split; auto.
        exists (x*x0). split. rewrite <- (Qmult_0_l x0).
        apply (Qmult_lt_compat_r 0 x x0). auto. auto.
        unfold not. intros.
        destruct H10, H10, H10, H11, H12, H13.
        assert(x2<x).
        { apply (Dedekind_le (Cut_opp B)). auto. apply H5. auto. }
        assert(x1<x0).
        { apply (Dedekind_le A). auto. apply H7. auto. }
        rewrite Qopp_involutive in H14.
        rewrite <- (Qmult_assoc (2#1) x x0) in H14.
        rewrite <- (Qmult_1_l (-(x*x0))) in H14.
        assert((1 * (- (x * x0)) == (- 1%Q) * (x * x0))%Q).
        { rewrite Qmult_1_l. reflexivity. }
        rewrite H17 in H14.
        rewrite <- (Qmult_plus_distr_l (2#1) (-1%Q) (x*x0)) in H14.
        assert(((2 # 1) + - (1))==1)%Q. reflexivity.
        rewrite H18 in H14. rewrite Qmult_1_l in H14.
        apply Qle_not_lt in H14. apply H14. rewrite Qmult_comm.
        apply Qmult_lt_compat. auto. auto. auto. auto.
    *** destruct H1. **** destruct H1.
        assert(Dedekind (Cut_opp A)).
        { apply Dedekind_opp, H. }
        assert(Dedekind (Cut_opp B)).
        { apply Dedekind_opp, H0. }
        destruct (Dedekind_properties3 _ H3 0). apply H1.
        destruct (Dedekind_properties3 _ H4 0). apply H2.
        exists (x*x0). right. right. right. left.
        repeat split; auto.
        unfold Cut_multNN. exists x, x0. destruct H5, H6.
        repeat split; auto. apply Qle_refl.
   **** exists (-1%Q). repeat right. split. auto. reflexivity.
      + 
(*      * destruct (Dedekind_properties1 _ H ).
        destruct (Dedekind_properties1 _ H0).
        destruct H6. assert(x>0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H6.
          apply (Dedekind_properties2 _ H0 0).
          split. auto. auto. }
        destruct H3. assert(x0<0).
        { apply Qnot_le_lt. unfold not in *. intros. apply H1.
          apply (Dedekind_properties2 _ H x0).
          split. auto. auto. }
        exists (x0*x). right. left.
        repeat split; auto.
        exists x0, x.
        repeat split; auto. apply Qle_refl.
      * destruct (Dedekind_properties1 _ H ).
        destruct (Dedekind_properties1 _ H0).
        assert((Cut_opp A 0 /\ Cut_opp B 0)\/~(Cut_opp A 0 /\ Cut_opp B 0)).
        { apply classic. }
        destruct H7.
        ++ unfold Cut_opp in H7. destruct H7, H7, H7, H8, H8.
        exists (x/(2#1)*(x0/(2#1))). right. right. right. left.
        repeat split; auto.
        exists (x/(2#1)), (x0/(2#1)).
        repeat split.
        *** apply (Qlt_shift_div_l 0 x (2#1)).
        { reflexivity. }
        { rewrite Qmult_0_l. auto. }
        *** apply (Qlt_shift_div_l 0 x0 (2#1)).
        { reflexivity. }
        { rewrite Qmult_0_l. auto. }
        *** unfold Cut_opp. exists (x/(2#1)). split.
        { apply (Qlt_shift_div_l 0 x (2#1)).
        { reflexivity. }
        { rewrite Qmult_0_l. auto. } }
        unfold not in *. intros. apply H9.
        apply (Dedekind_properties4 _ H (- (x / (2 # 1)) + - (x / (2 # 1)))).
        { symmetry. rewrite Qplus_0_l. apply Qdiv2_opp. }
        { auto. }
        *** unfold Cut_opp. exists (x0/(2#1)). split.
        { apply (Qlt_shift_div_l 0 x0 (2#1)).
        { reflexivity. }
        { rewrite Qmult_0_l. auto. } }
        unfold not in *. intros. apply H10.
        apply (Dedekind_properties4 _ H0 (- (x0 / (2 # 1)) + - (x0 / (2 # 1)))).
        { symmetry. rewrite Qplus_0_l. apply Qdiv2_opp. }
        { auto. }
        *** apply Qle_refl.
        ++ exists (-1%Q). repeat right. unfold Cut_mult0.
           repeat split; auto.
    + unfold Cut_mult, not.
      assert(A 0 \/~ A 0).  { apply classic. }
      assert(B 0 \/~ B 0).  { apply classic. }
      destruct H1, H2.
      * destruct (Dedekind_properties1 _ H). destruct H4.
        destruct (Dedekind_properties1 _ H0). destruct H6.
        exists (x*x0). intros. destruct H7.
        ++ destruct H7, H8. unfold Cut_multPP in H9.
           destruct H9, H9.
        unfold Cut_multPP in H6.
        destruct H6, H7, H8, H8, H8, H9, H10, H11.
        apply Qlt_le_weak in H8. apply Qlt_le_weak in H9.
        apply Qmult_le_0_compat with (a:=x2) in H8.
        unfold Cut_multPP. exists x, x0. destruct H3, H4.
        repeat split; auto. *)
Admitted.

Definition Rmult (a b :Real) : Real :=
  match a with
  | Real_cons A HA => match b with
                      | Real_cons B HB =>
                        Real_cons (Cut_mult A B) (Dedekind_mult A B HA HB)
                      end
  end.

Notation "A * B" := (Rmult A B) (at level 40, left associativity)
                       : R_scope.

(** Third , we will define the plus operation of Set and Real
    and proof some theorem about it. *)
Theorem Rmult_0 : forall a : Real, (a * Rzero == Rzero)%R.
Proof.
  intros. unfold Rmult. destruct a. unfold Rzero.
  unfold Cut_mult, Req. split.
  - unfold Rle. intros.
    destruct H0.
  * destruct H0, H1. inversion H1.
  * destruct H0. ** destruct H0, H1. inversion H1.
 ** destruct H0. *** destruct H0, H1, H1, H1.
    Search Qopp. rewrite Qlt_minus_iff in H3.
    rewrite Qplus_0_l in H3. rewrite Qplus_0_l in H3.
    rewrite Qopp_involutive in H3.
    exfalso. apply H3, H1.
*** destruct H0. **** destruct H0, H1, H1, H1.
    Search Qopp. rewrite Qlt_minus_iff in H3.
    rewrite Qplus_0_l in H3. rewrite Qplus_0_l in H3.
    rewrite Qopp_involutive in H3.
    exfalso. apply H3, H1.
**** destruct H0. unfold Cut_mult0 in H1. apply H1.
  - unfold Rle. intros. repeat right. split.
  + right. split.
  * unfold not. intros. inversion H1.
  * unfold not. intros. destruct H1, H1.
    Search Qopp. rewrite Qlt_minus_iff in H2.
    rewrite Qplus_0_l in H2. rewrite Qplus_0_l in H2.
    rewrite Qopp_involutive in H2.
    exfalso. apply H2, H1.
  + apply H0.
Qed.

Theorem Rmult_1 : forall a : Real, (a * Rone == a)%R.
Proof.
Admitted.

Theorem Rmult_comm : forall a b : Real, (a * b == b * a)%R.
Proof.
Admitted.

Theorem Rmult_assoc : forall a b c : Real, (a * b * c == a * (b * c))%R.
Proof.
Admitted.

Theorem Rmult_distr_l :
  forall a b c : Real, (a * (b + c) == (a * b) + (a * c))%R.
Proof.
Admitted.

Theorem Rmult_inv :
  forall a : Real, (a <> Rzero) -> exists b, (a * b == Rone)%R.
Proof.
Admitted.

