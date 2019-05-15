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
From CReal Require Import QArith_ext.QArith_base_ext.
From CReal Require Import QArith_ext.Inject_lemmas.
From Coq Require Import QArith.Qfield.
Import ListNotations.

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

Lemma funlemma1 : forall x : Real -> Prop, (exists x0 : Real, x x0)
 -> exists (x0 : Q) (x1 : Real), x x1 /\ (Q_to_R x0 < x1)%R.
Proof.
  intros. destruct H. remember x0. destruct x0. destruct (Dedekind_properties1 _ H0), H1.
  exists x0, r. split;auto. hnf. rewrite Heqr. split.
  - intros. apply (Dedekind_properties2 _ H0 x0).
    split;auto;apply Qlt_le_weak;auto.
  - destruct (Dedekind_properties3 _ H0 x0). auto.
    exists x1. split. apply H3. apply Qle_not_lt.
    apply Qlt_le_weak. apply H3.
Qed.

Lemma funlemma2 : forall x : Real -> Prop,(forall x1 x2, x x1 -> x x2 ->
 x1 == x2) -> (exists x0 : Real, x x0)
 -> exists x0 : Q, ~ (exists x1 : Real, x x1 /\ (Q_to_R x0 < x1)%R).
Proof.
  intros. apply not_all_ex_not. hnf. intros.
  destruct H0. destruct x0. destruct (Dedekind_properties1 _ H2), H4.
  destruct (H1 x0). destruct H5. apply (H (Real_cons A H2)) in H5;auto.
  rewrite <- H5 in H6. hnf in H6. destruct H6.
  destruct H7, H7. apply Qnot_lt_le in H8. apply H4.
  apply (Dedekind_properties2 _ H2 x2). split;auto.
Qed.

Lemma funlemma3 : forall x : Real -> Prop,(forall x1 x2, x x1 -> x x2 ->
 x1 == x2) -> (exists x0 : Real, x x0)
 -> forall p q : Q,
(exists x0 : Real, x x0 /\ (Q_to_R p < x0)%R) /\ q <= p 
-> exists x0 : Real, x x0 /\ (Q_to_R q < x0)%R.
Proof.
  intros. destruct H1, H1, H1. exists x0.
  split;auto. hnf in H3. hnf. destruct x0. destruct H3. split.
  - intros. apply H3. apply Qlt_le_trans with (y:=q);auto.
  - destruct H5, H5. exists x0. split;auto.
    hnf. intros. apply H6.
    apply Qlt_le_trans with (y:=q);auto.
Qed.


Lemma funlemma4 : forall x : Real -> Prop,(forall x1 x2, x x1 -> x x2 ->
 x1 == x2) -> (exists x0 : Real, x x0)
 -> forall p : Q,
(exists x0 : Real, x x0 /\ (Q_to_R p < x0)%R) ->
exists r : Q, (exists x0 : Real, x x0 /\ (Q_to_R r < x0)%R) /\ p < r.
Proof.
  intros. destruct H1, x0, H1, H3. destruct H4, H4.
  apply (Dedekind_properties3 _ H2) in H4.
  destruct H4, H4. exists x1. split.
  - exists (Real_cons A H2). split;auto. hnf. split.
    + intros.
 apply (Dedekind_properties2 _ H2 x1);split;try apply Qlt_le_weak;auto.
    + exists x1. split;auto;apply Qlt_irrefl.
  - apply Qnot_lt_le in H5. apply Qle_lt_trans with (y:=x0);auto.
Qed.

Lemma funlemma5 : forall x : Real -> Prop,(forall x1 x2, x x1 -> x x2 ->
 x1 == x2) -> (exists x0 : Real, x x0) ->
forall p q : Q,
(p == q)%Q -> (exists x0 : Real, x x0 /\ (Q_to_R p < x0)%R)
  -> exists x0 : Real, x x0 /\ (Q_to_R q < x0)%R.
Proof.
  intros. destruct H2, H2. exists x0. destruct x0, H3.
  split;auto. split.
  - intros. rewrite <- H1 in H6. apply H3;auto.
  - destruct H5. rewrite H1 in H5. exists x0. auto.
Qed.


Definition Rsinglefun : {X: Real -> Prop | (forall x1 x2, X x1 -> X x2 ->
 x1 == x2) /\ (exists x, X x) /\ Proper ( Req ==> iff) X}%R -> Real.
  intros. destruct X, a, H0. hnf in *.
  apply (Real_cons (fun q : Q => exists x0 : Real, x x0 /\ (Q_to_R q < x0)%R)).
  split.
  - split.
    + apply funlemma1;auto.
    + apply funlemma2;auto.
  - apply funlemma3;auto.
  - apply funlemma4;auto.
  - apply funlemma5;auto. Defined.

Theorem Rsinglefun_correct: forall X H, X (Rsinglefun (exist _ X H)).
Proof.
  intros. hnf in *. destruct H, a. hnf in p. destruct e.
  apply (p x);auto. hnf. destruct x. split.
  - hnf. intros. exists (Real_cons A H). split;auto. hnf. split.
    + intros. apply (Dedekind_properties2 _ H x).
      split;try apply Qlt_le_weak;auto.
    + destruct (Dedekind_properties3 _ H x);auto. exists x1.
      destruct H1.
      split;try apply Qle_not_lt;try apply Qlt_le_weak;auto.
  - hnf. intros. destruct H0, H0. destruct x1.
    destruct H1, H3, H3. apply Qnot_lt_le in H4.
    assert((Real_cons A H)==(Real_cons A0 H2)).
    apply r;auto. destruct H5. hnf in H6. apply H6.
    apply (Dedekind_properties2 _ H2 x1);auto.
Qed.

Definition R2fun : {f:Real -> Real -> Prop | (forall x1 x2 y1 y2, f x1 y1 -> f x2 y2
  -> x1 == x2 -> y1 == y2) /\ (forall x, exists y, f x y) /\
Proper (Req ==> Req ==> iff) f }%R -> (Real -> Real).
intros. destruct X, a, H0. apply Rsinglefun. exists (x X0). split.
  - intros. apply (H X0 X0 x1 x2);auto. reflexivity.
  - split.
    + apply (H0 X0).
    + split.
      { intros. rewrite H2 in H3. auto. }
      { intros. rewrite H2. auto. } Defined.


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

Instance Rplus_comp : Proper (Req ==> Req ==> Req) Rplus.
Proof.
  split ; destruct H; destruct H0; 
  destruct x ; destruct y;destruct x0;destruct y0;
  unfold Rle in * ; simpl in *;
  unfold Cut_plus_Cut in * ; simpl in *; intros ;
  repeat destruct H7 ; destruct H8; exists x0;exists x1; split; auto.
Qed.

Theorem Rplus_0_r : forall a : Real, (a + Rzero)%R == a.
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

Definition Rminus (a b : Real) : Real := (a + (- b))%R.

Notation "A - B" := (Rminus A B) (at level 50, left associativity)
                       : R_scope.

Instance Ropp_comp : Proper(Req ==> Req)Ropp.
Proof.
  split.
  - unfold Req, Ropp, Rle in *. destruct x, y. intros.
    destruct H. destruct H2, H2.
    exists x0. split;auto.
  - unfold Req, Ropp, Rle in *. destruct x, y. intros.
    destruct H. destruct H2, H2.
    exists x0. split;auto.
Qed.

Lemma Cut_cut_opp_not : forall (A : Q -> Prop) (x : Q),
  Dedekind A -> A x -> ~ Cut_opp A (- x).
Proof.
  unfold not. intros. destruct H1, H1. apply H2.
  rewrite Qopp_involutive.
  apply (Dedekind_properties2 _ H x).
  split; auto.
  rewrite Qplus_comm.
  rewrite <- Qplus_le_l with (z:=(-x)).
  rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
  rewrite <- Qplus_le_r with (z:=x0).
  rewrite Qplus_assoc. rewrite Qplus_opp_r.
  repeat rewrite Qplus_0_r. apply Qlt_le_weak. auto.
Qed.

Lemma mylemma2 : forall (A : Q -> Prop),
 Dedekind A ->
(forall m : Z, A (inject_Z m) -> A (inject_Z (m+ 1)))
 -> exists x1, forall m1, A (inject_Z (x1 + m1)).
Proof.
  intros.
  destruct (Dedekind_properties1 _ H ).
  destruct H1, H2.
  assert(forall x : Q, exists m : Z, inject_Z m <= x).
  apply le_inject_Z.
  destruct (H3 x).
  assert (A (inject_Z x1)). {
  apply (Dedekind_properties2 _ H x (inject_Z x1)).
  repeat split; auto. } exists x1. apply Zind.
  - rewrite Zplus_0_r. auto.
  - unfold Z.succ. intros.
    assert(inject_Z (x1 + (x2 + 1))=inject_Z (x1 + x2 + 1)).
    { rewrite Zplus_assoc. reflexivity. }
    rewrite H7. apply H0. apply H6.
  - intros.
    apply (Dedekind_properties2 _ H (inject_Z (x1 + x2))).
    split; auto.
    rewrite <- Zle_Qle. apply Zplus_le_compat_l.
    apply Z.le_pred_l.
Qed.

Lemma Zarchimedean : forall (A : Q -> Prop),
 Dedekind A ->
(forall m : Z, A (inject_Z m) -> A (inject_Z (m+ 1)))
 -> forall m1 : Z, A (inject_Z m1).
Proof.
  intros. assert((forall m : Z, A (inject_Z m) -> A (inject_Z (m+ 1)))
 -> exists x1, forall m1, A (inject_Z (x1 + m1))).
  { apply mylemma2. auto. }
  apply H1 in H0. destruct H0.
  assert(A (inject_Z (x+(-x+m1)))).
  { apply (H0 (-x+m1)%Z). }
  apply (Dedekind_properties2 _ H (inject_Z (x + (- x + m1)))).
  split; auto.
  rewrite <- Zle_Qle. rewrite Zplus_assoc.
  rewrite Z.add_opp_diag_r. reflexivity.
Qed.

Lemma forall_imply_to_exists_and :
  forall (P T :Q -> Prop), forall y : Q, y>0 ->
 ~(forall (m : Q), P m -> T (m + y)%Q) -> exists m1 : Q, P m1 /\ ~ T (m1 + y)%Q.
Proof.
  intros. apply exists_dist. unfold not in *. intros.
  apply H0. intros. 
  assert (P m /\ (T (m + y)%Q -> False) -> False).
  apply (H1 m).
  apply not_and_or in H3. destruct H3.
  - destruct H3. auto.
  - apply NNPP. apply H3.
Qed.

Lemma mylemma1 : forall (A : Q -> Prop),
 Dedekind A ->
~(forall m : Z, A (inject_Z m) -> A (inject_Z (m+ 1))).
Proof.
  unfold not. intros. assert((forall m1 : Z, A (inject_Z m1)) -> False).
  { intros. destruct (Dedekind_properties1 _ H).
    destruct H3.
    assert(exists m : Z, inject_Z m >= x).
    { apply inject_Z_le. }
    destruct H4. apply H3.
    apply (Dedekind_properties2 _ H (inject_Z x0)). split.
    apply H1.
    apply H4. }
  apply H1. apply Zarchimedean. auto. auto.
Qed.

Lemma mylemma3 : forall (A : Q -> Prop),
 Dedekind A -> forall y : Q, y>0 -> (forall x : Q, A x -> A (x + y))
 -> forall (x : Q) (m : Z), A x -> A (x + y*(inject_Z m)).
Proof.
  intros. apply (Zind (fun m => A (x + y * inject_Z m))).
  - unfold inject_Z. rewrite Qmult_0_r. rewrite Qplus_0_r. auto.
  - intros. unfold Z.succ. rewrite inject_Z_plus.
    rewrite Qmult_plus_distr_r. rewrite Qplus_assoc.
    rewrite Qmult_1_r.
    apply (H1 (x + y * inject_Z x0)).
    apply H3.
  - intros. apply (Dedekind_properties2 _ H (x + y * inject_Z x0)).
    split; auto.
    rewrite Qmult_comm.
    rewrite Qmult_comm with (y:=(inject_Z x0)).
    rewrite Qplus_le_r. apply Qmult_le_compat_r.
    rewrite <- Zle_Qle. apply Z.le_pred_l.
    apply Qlt_le_weak. auto.
Qed.

Lemma mylemma4 : forall (A : Q -> Prop),
 Dedekind A -> forall y : Q, y>0 -> (forall x : Q, A x -> A (x + y))
 -> forall (x : Q) (m : Z), A (x + y*(inject_Z m)).
Proof.
  intros. assert(forall (x : Q) (m : Z), A x -> A (x + y*(inject_Z m))).
  { apply mylemma3. auto. auto. auto. }
  destruct (Dedekind_properties1 _ H).
  destruct H3.
  assert(forall x1:Q, exists m : Z, (inject_Z m) * y > x1).
  { intros. assert(forall p q :Q, p > 0 -> exists n : Q, n*p>q).
  { apply Qarchimedean. } assert(exists n : Q, x1 < n * y).
  { apply (H5 y x1). auto. }
    destruct H6. assert(exists m : Z, inject_Z m >= x2).
    { apply inject_Z_le. }
    destruct H7. exists x3. apply Qlt_le_trans with (y:=x2 * y).
    auto. apply Qmult_le_compat_r. auto. apply Qlt_le_weak. auto. }
  destruct (H5 (x + y * inject_Z m - x0)).
  apply (H2 x0 x1) in H3.
  rewrite <- Qplus_lt_l with (z:=x0) in H6.
  rewrite <- (Qplus_assoc (x + y * inject_Z m) (-x0) x0) in H6.
  rewrite (Qplus_comm (-x0) x0 ) in H6. rewrite Qplus_opp_r in H6.
  apply (Dedekind_properties2 _ H (x0 + y * inject_Z x1)).
  split; auto.
  apply Qlt_le_weak.
  rewrite Qplus_comm with (y:=y * inject_Z x1).
  rewrite Qplus_0_r in H6. rewrite Qmult_comm with (y:=inject_Z x1).
  auto.
Qed.

Lemma mylemma5 : forall (A : Q -> Prop),
 Dedekind A -> forall y : Q, y>0 -> (forall x : Q, A x -> A (x + y))
 -> forall (x : Q), A x.
Proof.
  intros. assert(forall (x : Q) (m : Z), A (x + y*(inject_Z m))).
  { apply mylemma4. auto. auto. auto. }
  assert(A (x + y * 0)). { apply (H2 x 0%Z). }
  rewrite Qmult_0_r in H3. rewrite Qplus_0_r in H3. auto.
Qed.

Lemma mylemma6 : forall (A : Q -> Prop),
 Dedekind A -> forall y : Q, y>0 ->
~(forall x : Q, A x -> A (x + y)).
Proof.
  unfold not. intros. assert((forall (x : Q), A x) -> False).
  { intros. destruct (Dedekind_properties1 _ H).
    destruct H4.
    destruct H4.
    apply mylemma5 with (y:=y). auto. auto. apply H1. }
  apply H2. intros. apply mylemma5 with (y:=y). auto. auto. auto.
Qed.

Lemma Dedekind1_strong : forall (A : Q -> Prop),
 Dedekind A -> forall y : Q, y>0 -> (exists x:Q, A x /\ ~ A (x + y)).
Proof.
  intros.
  apply forall_imply_to_exists_and. auto.
  apply mylemma6. auto. auto.
Qed.

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
    assert(exists y:Q, A y /\ ~ A (y +(- x/(2#1)))).
    { apply Dedekind1_strong. auto.
      apply Qmult_lt_r with (z:=2#1). reflexivity.
      assert(H'':~(2#1==0)%Q). { unfold not. intros. inversion H2. }
      apply (Qdiv_mult_l (-x)) in H''.
      rewrite <- (Qmult_assoc (-x) (/(2#1)) (2#1)).
      rewrite (Qmult_comm (/(2 # 1))).
      rewrite (Qmult_assoc (-x) (2#1) (/(2#1))). rewrite H''.
      rewrite Qmult_0_l.
      rewrite <- (Qplus_0_l (-x)). rewrite <- Qlt_minus_iff. auto. }
    destruct H2, H2. exists x2. split. auto.
    exists (-x/(2#1)). split.
    + apply Qmult_lt_r with (z:=2#1). reflexivity.
      assert(H'':~(2#1==0)%Q). { unfold not. intros. inversion H4. }
      apply (Qdiv_mult_l (-x)) in H''.
      rewrite <- (Qmult_assoc (-x) (/(2#1)) (2#1)). rewrite (Qmult_comm (/(2 # 1))).
      rewrite (Qmult_assoc (-x) (2#1) (/(2#1))). rewrite H''.
      rewrite Qmult_0_l.
      rewrite <- (Qplus_0_l (-x)). rewrite <- Qlt_minus_iff. auto.
    + unfold not. intros. apply H3.
      apply (Dedekind_properties4 _ DA (- (x - x2) + - (- x / (2 # 1)))).
      * rewrite <- Qplus_inj_r with (z:= - x / (2 # 1)).
        rewrite <- Qplus_assoc.
        rewrite (Qplus_comm (- (- x / (2 # 1)))).
        rewrite Qplus_opp_r. rewrite <- Qplus_assoc.
        rewrite <- (Qdiv2 (-x)).
        rewrite Qplus_0_r. rewrite <- Qplus_inj_l with (z:=(x-x2)).
        rewrite Qplus_opp_r. rewrite (Qplus_comm x2).
        rewrite (Qplus_comm (x) (-x2)).
        rewrite <- Qplus_assoc. rewrite Qplus_assoc with (y:=(-x)).
        rewrite Qplus_opp_r. rewrite Qplus_0_l.
        rewrite Qplus_comm. symmetry. apply Qplus_opp_r.
      * auto.
Qed.

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
  intros.
  apply Rplus_l_compat with (a:= (-a)%R) in H.
  repeat rewrite <- Rplus_assoc in H.
  assert (H' : (-a + a)%R == Rzero).
  { 
    rewrite Rplus_comm.
    apply Rplus_opp.
  }
  rewrite H' in H. rewrite <- Rplus_comm in H. 
  rewrite <- Rplus_comm with (a := c) in H.
  repeat rewrite Rplus_0_r in H.
  auto.
Qed.

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

Definition PP (A B : Q -> Prop) : Prop := (A 0 /\ B 0).
Definition NP (A B : Q -> Prop) : Prop := (Cut_opp A 0 /\ B 0).
Definition PN (A B : Q -> Prop) : Prop := (A 0 /\Cut_opp B 0).
Definition NN (A B : Q -> Prop) : Prop := (Cut_opp A 0 /\ Cut_opp B 0).
Definition O (A B : Q -> Prop) : Prop := ((~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0)).

Definition Cut_mult : (Q -> Prop) -> (Q -> Prop) -> (Q -> Prop):=
  (fun A B x => (PP A B /\ Cut_multPP A B x) \/
                (NP A B /\ Cut_multNP A B x) \/
                (PN A B /\ Cut_multPN A B x) \/
                (NN A B /\ Cut_multNN A B x)\/
                (O A B /\ Cut_mult0 A B x))
.

Definition Cuteq (A B : Q -> Prop) := forall x : Q, A x <-> B x.

Instance Cut_Setoid : Equivalence Cuteq.
Proof.
  split.
  - hnf. intros. hnf. intros. reflexivity.
  - hnf. intros. hnf in *. intros. split.
    + intros. rewrite H. auto.
    + intros. rewrite <- H. auto.
  - hnf. intros. hnf in *. intros. split.
    + intros. apply H0, H, H1.
    + intros. rewrite H, H0. auto.
Qed.



Lemma Cut_opp_opp :
  forall (A : Q -> Prop), Dedekind A ->
forall x : Q, A x <-> (Cut_opp (Cut_opp A) x).
Proof.
  intros. split.
  - intros. hnf. apply (Dedekind_properties3 _ ) in H0.
    + destruct H0. exists (x0 - x). split.
      * unfold Qminus. rewrite <- Qlt_minus_iff. apply H0.
      * unfold Cut_opp. rewrite exists_dist. apply PPNN. intros.
        hnf in *. intros. destruct H1, H2.
        apply (Dedekind_properties2 _ H x0). split. apply H0.
        assert(- (- x + - (x0 - x)) == x0)%Q.
        { rewrite <- Qplus_opp_assoc. rewrite Qopp_involutive.
          unfold Qminus. rewrite Qplus_comm. rewrite <- (Qplus_0_r x0).
          rewrite <- Qplus_assoc. rewrite <- Qplus_assoc. rewrite Qplus_inj_l.
          rewrite Qplus_assoc. rewrite Qplus_0_l. rewrite Qplus_comm.
          apply Qplus_opp_r. }
        rewrite H2. rewrite <- Qplus_le_l with (z:=x1).
        rewrite <- Qplus_assoc. rewrite Qplus_le_r.
        apply Qlt_le_weak. rewrite Qplus_comm. rewrite Qplus_opp_r. auto.
    + auto.
  - intros. hnf in H0. destruct H0, H0. hnf in H1. unfold Cut_opp in H1.
    rewrite exists_dist in H1. apply NNPP in H1.
    assert(~(0<x0/\~ A (- (- x + - x0) + - x0))).
    { apply (H1 x0). } apply not_and_or in H2. destruct H2.
    + destruct H2. auto.
    + apply NNPP in H2.
    rewrite <- (Qplus_opp_assoc x x0) in H2. rewrite Qopp_involutive in H2.
      rewrite <- Qplus_assoc in H2. rewrite Qplus_opp_r in H2.
      rewrite <- Qplus_0_r. auto.
Qed.

Lemma Cut_opp_eq :
forall (A B : Q -> Prop), Dedekind A -> Dedekind B -> 
Cuteq A B <-> Cuteq (Cut_opp A) (Cut_opp B).
Proof.
  intros. split.
  - intros. hnf in *. intros. split.
    + intros. hnf in *. destruct H2, H2.
      exists x0. split;auto. hnf in *. intros. apply H3.
      apply H1. auto.
    + intros. hnf in *. destruct H2, H2.
      exists x0. split;auto. hnf in *. intros. apply H3.
      apply H1. auto.
  - intros. hnf in *. intros. split.
    + intros. apply Cut_opp_opp. auto. apply Cut_opp_opp in H2.
      * destruct (H1 x). hnf in *. destruct H2, H2.
      exists x0. split;auto. hnf in *. intros. apply H5.
      apply H1. auto. * auto.
    + intros. apply Cut_opp_opp. auto. apply Cut_opp_opp in H2.
      * destruct (H1 x). hnf in *. destruct H2, H2.
      exists x0. split;auto. hnf in *. intros. apply H5.
      apply H1. auto. * auto.
Qed.

(* Instance Cut_mult_comp : Proper(Cuteq ==> Cuteq ==> Qeq ==> iff) Cut_mult.
Proof.
  split.
  - intros. unfold Cut_mult in *. destruct H2 as [?|[?|[?|[?|[]]]]].
    + left. destruct H2. repeat split.
      * apply H, H2.
      * apply H0, H2.
      * destruct H3, H3. rewrite H1 in H3. destruct H3 as [?[?[?[?]]]].
        exists x2, x3. repeat split;auto.
        { apply H. auto. }
        { apply H0. auto. }
    + right; left. destruct H2, H2. repeat split.
      * rewrite Cut_opp_eq in H. apply H, H2. auto. auto.
      * apply H0, H2.
      * destruct H3, H3. rewrite H1 in H3. destruct H3 as [?[?[?[?]]]].
        exists x2, x3. repeat split;auto.
        { apply H. auto. }
        { apply H0. auto. }
Admitted. *)



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

Lemma Cut_mult_comm'' : forall (A B : Q -> Prop) (x : Q),
 Cut_mult A B x -> Cut_mult B A x.
Proof.
  intros. unfold Cut_mult. intros. destruct H as [ |[|[|[|[]]]] ].
    + destruct H. left. split.
      * split. apply H. apply H.
      * unfold Cut_multPP in *. destruct H0, H0.
        exists x1, x0. destruct H0 as [?[?[?[?]]]]. repeat split; auto.
        rewrite Qmult_comm. auto.
    + destruct H. right. right. left. split.
      * split. apply H. apply H.
      * unfold Cut_multNP in *. unfold Cut_multPN. unfold Cut_opp in *.
        destruct H0, H0. exists x0. split. auto.
        unfold not. intros. destruct H1. destruct H2, H1.
        exists x2, x1. destruct H1 as [?[?[?[?]]]]. repeat split; auto.
        rewrite Qmult_comm. auto.
    + destruct H. right. left. split.
      * split. apply H. apply H.
      * unfold Cut_multNP in *. unfold Cut_multPN. unfold Cut_opp in *.
        destruct H0, H0. exists x0. split. auto.
        unfold not. intros. destruct H1. destruct H2, H1.
        exists x2, x1. destruct H1 as [?[?[?[?]]]]. repeat split; auto.
        rewrite Qmult_comm. auto.
    + destruct H. right. right. right. left. split.
      * split. apply H. apply H.
      * unfold Cut_multNN in *. destruct H0, H0.
        exists x1, x0. destruct H0 as [?[?[?[?]]]]. repeat split; auto.
        rewrite Qmult_comm. auto.
    + right. right. right. right. split.
      * unfold O in *. destruct H.
        right. apply H.
        left. apply H.
      * auto.
Qed.

Lemma Cut_mult_comm' : forall (A B : Q -> Prop),
 Cuteq (Cut_mult A B) (Cut_mult B A).
Proof.
  intros. split.
  - apply Cut_mult_comm''.
  - apply Cut_mult_comm''.
Qed.

Lemma Cut_mult_comm : forall (A B : Q -> Prop) (x : Q),
 Cut_mult A B x <-> Cut_mult B A x.
Proof.
  intros. split.
  - apply Cut_mult_comm''.
  - apply Cut_mult_comm''.
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
  { rewrite <- (Qmult_0_l x). apply (Qmult_lt_compat_r 0 y x).
  auto. auto. }
Qed.

Lemma Qmult_lt_compat : forall x y z t : Q,
0 <= x -> 0 <= z -> x < y -> z < t -> x * z < y * t .
Proof.
  intros. apply Qle_lt_trans with (y:= y*z).
  - apply Qmult_le_compat_r. apply Qlt_le_weak. auto. auto.
  - rewrite Qmult_comm. rewrite (Qmult_comm y t).
    apply Qmult_lt_compat_r.
    apply Qle_lt_trans with (y:=x). auto. auto. auto.
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
        apply Qmult_lt_compat.
        apply Qlt_le_weak; auto. apply Qlt_le_weak; auto. auto. auto.
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
        apply Qmult_lt_compat.
        apply Qlt_le_weak; auto. apply Qlt_le_weak; auto. auto. auto.
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
    + assert(
  (A 0/\B 0)\/
  (Cut_opp A 0 /\ B 0)\/
  (A 0 /\Cut_opp B 0)\/
  (Cut_opp A 0 /\ Cut_opp B 0)\/
  (~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0)).
      { apply Rmult_situation. auto. auto. }
      destruct H1. * destruct H1.
      destruct (Dedekind_properties1 _ H).
      destruct (Dedekind_properties1 _ H0).
      destruct H4, H6.
      exists (x*x0). unfold not, Cut_mult. intros.
      destruct H7. { destruct H7, H8, H8, H8, H9, H10, H11.
      apply Qle_not_lt in H12. apply H12.
      apply Qmult_lt_compat.
      apply Qlt_le_weak; auto.
      apply Qlt_le_weak; auto.
      apply (Dedekind_le A); auto; auto; auto.
      apply (Dedekind_le B); auto; auto; auto. }
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H1. apply H1. auto. auto. }
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H2. apply H2. auto. auto. }
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H2. apply H2. auto. auto. }
      destruct H7. destruct H7, H7, H7. auto. auto.
    * destruct H1. ** destruct H1.
      assert(H':Dedekind (Cut_opp A)). { apply Dedekind_opp. auto. }
      destruct (Dedekind_properties3 _ H' 0). auto.
      destruct (Dedekind_properties3 _ H0 0). auto.
      destruct H3, H4.
      exists 1. unfold not, Cut_mult. intros.
      destruct H7. { destruct H7, H7.
      apply (Cut_cut_opp_not A 0) in H.
      { apply H. auto. } auto. }
      destruct H7. { destruct H7, H8, H8, H9.
      exists x, x0. repeat split; auto.
      apply Qle_trans with (y:=0).
      { rewrite <- (Qplus_0_r 0). apply Qplus_le_compat.
      { apply Qlt_le_weak. reflexivity. }
      { rewrite <- (Qopp_involutive 0). apply Qopp_le_compat.
        apply Qlt_le_weak. auto. } }
      { repeat apply Qmult_le_0_compat; apply Qlt_le_weak; auto. } }
      destruct H7. { apply Cut_cut_opp_not in H2.
      { apply H2. apply H7. } auto. }
      destruct H7. { apply Cut_cut_opp_not in H2.
      { apply H2. apply H7. } auto. }
      destruct H7, H7. { destruct H7. apply H9, H1. }
                       { destruct H7. apply H7, H2. }
   ** destruct H1. *** destruct H1.
      assert(H':Dedekind (Cut_opp B)). { apply Dedekind_opp. auto. }
      destruct (Dedekind_properties3 _ H' 0). auto.
      destruct (Dedekind_properties3 _ H 0). auto.
      destruct H3, H4.
      exists 1. rewrite Cut_mult_comm. unfold not, Cut_mult. intros.
      destruct H7. { destruct H7, H7.
      apply (Cut_cut_opp_not B 0) in H0.
      { apply H0. auto. } auto. }
      destruct H7. { destruct H7, H8, H8, H9.
      exists x, x0. repeat split; auto.
      apply Qle_trans with (y:=0).
      { rewrite <- (Qplus_0_r 0). apply Qplus_le_compat.
      { apply Qlt_le_weak. reflexivity. }
      { rewrite <- (Qopp_involutive 0). apply Qopp_le_compat.
        apply Qlt_le_weak. auto. } }
      { repeat apply Qmult_le_0_compat; apply Qlt_le_weak; auto. } }
      destruct H7. { apply Cut_cut_opp_not in H1.
      { apply H1. apply H7. } auto. }
      destruct H7. { apply Cut_cut_opp_not in H1.
      { apply H1. apply H7. } auto. }
      destruct H7, H7. { destruct H7. apply H9, H2. }
                       { destruct H7. apply H7, H1. }
  *** destruct H1. **** destruct H1.
      rename H into H'. rename H0 into H0'.
      assert (Dedekind (Cut_opp A)).
      { apply Dedekind_opp. auto. }
      assert (Dedekind (Cut_opp B)).
      { apply Dedekind_opp. auto. }
      destruct (Dedekind_properties1 _ H).
      destruct (Dedekind_properties1 _ H0).
      destruct H4, H6.
      exists (x*x0). unfold not, Cut_mult. intros.
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H7. apply H7. auto. auto. }
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H9. apply H9. auto. auto. }
      destruct H7. { destruct H7, H7.
      apply Cut_cut_opp_not in H7. apply H7. auto. auto. }
      destruct H7. { destruct H7, H8, H8, H8, H9, H10, H11.
      apply Qle_not_lt in H12. apply H12.
      apply Qmult_lt_compat.
      apply Qlt_le_weak; auto.
      apply Qlt_le_weak; auto.
      apply (Dedekind_le (Cut_opp A)); auto; auto; auto.
      apply (Dedekind_le (Cut_opp B)); auto; auto; auto. }
      destruct H7, H7. { destruct H7. apply H9. auto. }
                       { destruct H7. apply H9. auto. }
 **** exists 0. destruct H1. ***** destruct H1.
      unfold Cut_mult, not. intros.
      destruct H3. { apply H1, H3. }
      destruct H3. { apply H2, H3. }
      destruct H3. { apply H1, H3. }
      destruct H3. { apply H2, H3. }
      destruct H3. inversion H4. ***** destruct H1.
      unfold Cut_mult, not. intros.
      destruct H3. { apply H1, H3. }
      destruct H3. { apply H1, H3. }
      destruct H3. { apply H2, H3. }
      destruct H3. { apply H2, H3. }
      destruct H3. inversion H4.
  - intros. destruct H1, H1. *
    destruct H1, H3, H3, H3, H4, H5, H6.
    left. split; auto. exists x, x0.
    repeat split; auto.
    apply Qle_trans with (y:=p). auto. auto.
    * destruct H1. ** destruct H1, H3, H3.
      right; left; split; auto. exists x.
      split; auto. unfold not. intros. apply H4.
      destruct H5, H5, H5, H6, H7, H8. exists x0, x1.
      repeat split; auto.
      apply Qle_trans with (y:=-q+-x).
      { rewrite Qplus_le_l. apply Qopp_le_compat. auto. }
      { auto. }
   ** destruct H1. *** destruct H1, H3, H3.
      right; right; left; split; auto. exists x.
      split; auto. unfold not. intros. apply H4.
      destruct H5, H5, H5, H6, H7, H8. exists x0, x1.
      repeat split; auto.
      apply Qle_trans with (y:=-q+-x).
      { rewrite Qplus_le_l. apply Qopp_le_compat. auto. }
      { auto. }
  *** destruct H1. **** destruct H1, H3, H3, H3, H4, H5, H6.
      right; right; right; left; split; auto. exists x, x0.
      repeat split; auto. apply Qle_trans with (y:=p). auto. auto.
 **** destruct H1.
      right; right; right; right; split; auto.
      destruct H1, H1. *****
      apply Qle_lt_trans with (y:=p). auto. auto.
***** apply Qle_lt_trans with (y:=p). auto. auto.
  - intros. destruct H1 as [?|[?|[?|[?|[]]]]].
    * destruct H1, H2, H2, H2, H3, H4, H5, H1.
      assert(exists r : Q, A r /\ x < r).
      { apply (Dedekind_properties3 _ H). auto. }
      assert(exists r : Q, B r /\ x0 < r).
      { apply (Dedekind_properties3 _ H0). auto. }
      destruct H9, H9, H8, H8. exists (x2*x1). split.
      { left. repeat split; auto. exists x2, x1.
        repeat split.
        + apply Qlt_trans with (y:=x). auto. auto.
        + apply Qlt_trans with (y:=x0). auto. auto.
        + auto.
        + auto.
        + apply Qle_refl. }
      apply Qle_lt_trans with (y:=(x*x0)). auto.
      apply Qmult_lt_compat.
      + apply Qlt_le_weak. auto.
      + apply Qlt_le_weak. auto.
      + auto.
      + auto.
    * destruct H1, H2, H2. exists (p+(x/(2#1))). split.
      + right; left. split; auto.
        unfold Cut_multNP, Cut_opp, not. exists (x/(2#1)).
        split. { apply Qlt_shift_div_l. reflexivity. auto. }
        intros. apply H3. destruct H4, H4, H4, H5, H6, H7.
        exists x0, x1. repeat split; auto.
        rewrite (Qplus_opp_assoc p (x / (2 # 1))) in H8.
        rewrite <- (Qplus_assoc) in H8. unfold Qdiv in H8.
        rewrite <- Qdiv2_opp in H8. auto.
      + rewrite Qplus_comm. rewrite <- Qplus_0_l. apply Qplus_lt_le_compat.
        { apply Qlt_shift_div_l. reflexivity. auto.  }
        { rewrite Qplus_0_l. apply Qle_refl. }
    * destruct H1, H2, H2. exists (p+(x/(2#1))). split.
      + right; right; left. split; auto.
        unfold Cut_multPN, Cut_opp, not. exists (x/(2#1)).
        split. { apply Qlt_shift_div_l. reflexivity. auto. }
        intros. apply H3. destruct H4, H4, H4, H5, H6, H7.
        exists x0, x1. repeat split; auto.
        rewrite (Qplus_opp_assoc p (x / (2 # 1))) in H8.
        rewrite <- (Qplus_assoc) in H8. unfold Qdiv in H8.
        rewrite <- Qdiv2_opp in H8. auto.
      + rewrite Qplus_comm. rewrite <- Qplus_0_l. apply Qplus_lt_le_compat.
        { apply Qlt_shift_div_l. reflexivity. auto.  }
        { rewrite Qplus_0_l. apply Qle_refl. }
    * destruct H1, H2, H2, H2, H3, H4, H5, H1.
      rename H into H'. rename H0 into H0'.
      assert (Dedekind (Cut_opp A)).
      { apply Dedekind_opp. auto. }
      assert (Dedekind (Cut_opp B)).
      { apply Dedekind_opp. auto. }
      assert(exists r : Q, (Cut_opp A) r /\ x < r).
      { apply (Dedekind_properties3 _ H). auto. }
      assert(exists r : Q, (Cut_opp B) r /\ x0 < r).
      { apply (Dedekind_properties3 _ H0). auto. }
      destruct H9, H9, H8, H8. exists (x2*x1). split.
      { right; right; right; left. repeat split; auto. exists x2, x1.
        repeat split.
        + apply Qlt_trans with (y:=x). auto. auto.
        + apply Qlt_trans with (y:=x0). auto. auto.
        + auto.
        + auto.
        + apply Qle_refl. }
      apply Qle_lt_trans with (y:=(x*x0)). auto.
      apply Qmult_lt_compat.
      + apply Qlt_le_weak. auto.
      + apply Qlt_le_weak. auto.
      + auto.
      + auto.
    * destruct H1.
      { destruct H1. apply Qdensity in H2. destruct H2.
        exists (x). split.
        { repeat right. split. left; auto. apply H2. }
        apply H2. }
      { destruct H1. apply Qdensity in H2. destruct H2.
        exists (x). split.
        { repeat right. split. right; auto. apply H2. }
        apply H2. }
  - intros. destruct H2 as [?|[?|[?|[?|[]]]]].
    * left. destruct H2. split; auto.
      destruct H3, H3. destruct H3 as [?[?[?[?]]]].
      exists x, x0. repeat split; auto. rewrite <- H1. auto.
    * right; left. destruct H2. split; auto.
      destruct H3, H3. exists x. split; auto.
      unfold not. intros. apply H4. destruct H5, H5. destruct H5 as [?[?[?[?]]]].
      exists x0, x1. repeat split; auto. rewrite H1. auto.
    * right; right; left. destruct H2. split; auto.
      destruct H3, H3. exists x. split; auto.
      unfold not. intros. apply H4. destruct H5, H5. destruct H5 as [?[?[?[?]]]].
      exists x0, x1. repeat split; auto. rewrite H1. auto.
    * right; right; right; left. destruct H2. split; auto.
      destruct H3, H3. destruct H3 as [?[?[?[?]]]].
      exists x, x0. repeat split; auto. rewrite <- H1. auto.
    * repeat right. split; auto. unfold Cut_mult0. rewrite <- H1. auto.
Qed.

Definition Rmult (a b :Real) : Real :=
  match a with
  | Real_cons A HA => match b with
                      | Real_cons B HB =>
                        Real_cons (Cut_mult A B) (Dedekind_mult A B HA HB)
                      end
  end.

Notation "A * B" := (Rmult A B) (at level 40, left associativity)
                       : R_scope.

Lemma NP0_false : forall (A B : Q -> Prop),
  Dedekind A -> Dedekind B -> NP A B -> Cut_multNP A B 0 -> False.
Proof.
  intros. destruct H1. destruct H2, H2, H4.
  apply Dedekind_opp in H.
  apply (Dedekind_properties3 _) in H1.
  apply (Dedekind_properties3 _) in H3.
  { destruct H1, H1, H3, H3. exists x0, x1.
    repeat split;auto. apply Qlt_le_weak. rewrite Qplus_0_l.
    apply Qlt_trans with (y:=0). { rewrite Qlt_minus_iff.
    rewrite Qopp_involutive. rewrite Qplus_0_l. auto. }
    rewrite <- (Qmult_0_l 0).
    repeat apply (Qmult_lt_compat 0 x0 0 x1).
    apply Qle_refl. apply Qle_refl. auto. auto. }
    auto. auto.
Qed.

Lemma PN0_false : forall (A B : Q -> Prop),
  Dedekind A -> Dedekind B -> PN A B -> Cut_multPN A B 0 -> False.
Proof.
  intros. destruct H1. destruct H2, H2, H4.
  apply Dedekind_opp in H0.
  apply (Dedekind_properties3 _) in H1.
  apply (Dedekind_properties3 _) in H3.
  { destruct H1, H1, H3, H3. exists x0, x1.
    repeat split;auto. apply Qlt_le_weak. rewrite Qplus_0_l.
    apply Qlt_trans with (y:=0). { rewrite Qlt_minus_iff.
    rewrite Qopp_involutive. rewrite Qplus_0_l. auto. }
    rewrite <- (Qmult_0_l 0).
    repeat apply (Qmult_lt_compat 0 x0 0 x1).
    apply Qle_refl. apply Qle_refl. auto. auto. }
    auto. auto.
Qed.

Lemma Cut_mult_situation1 :
  forall C : Q -> Prop,C 0 \/ Cut_opp C 0 \/ (~ C 0/\~ Cut_opp C 0).
Proof.
  intros.
  assert(C 0 \/ ~ C 0). apply classic.
  assert(Cut_opp C 0 \/ ~ Cut_opp C 0). apply classic.
  destruct H, H0.
  - left;auto.
  - left;auto.
  - right;left;auto.
  - right;right. split. auto. auto.
Qed.

Lemma PPmult : forall A B : Q -> Prop, Dedekind A -> Dedekind B -> A 0 -> B 0 -> Cut_mult A B 0.
Proof.
  intros. left. repeat split;auto.
  apply (Dedekind_properties3 _) in H1.
  apply (Dedekind_properties3 _) in H2.
  - destruct H1, H1, H2, H2. exists x, x0.
    repeat split;auto.
    rewrite <- (Qmult_0_l 0).
    apply Qlt_le_weak.
    repeat apply (Qmult_lt_compat 0 x 0 x0);auto;apply Qle_refl.
  - auto.
  - auto.
Qed.

Lemma and_or_not5 : forall A B C D E : Prop,
~(A\/B\/C\/D\/E) <-> ~ A/\~B/\~C/\~D/\~E.
Proof.
  intros. split.
  - intros. unfold not in *. repeat split;intros;apply H;auto.
  - intros. destruct H as [?[?[?[]]]].
    unfold not in *. intros.
    destruct H4. apply H, H4.
    destruct H4. apply H0, H4.
    destruct H4. apply H1, H4.
    destruct H4. apply H2, H4.
    apply H3, H4.
Qed.

Lemma Cut_mult_opp' : forall A B : Q -> Prop, forall x : Q, Dedekind A -> Dedekind B ->
 Cut_opp (Cut_mult A B) x -> Cut_mult A (Cut_opp B) x.
Proof.
  intros. unfold Cut_mult in *. destruct H1, H1.
  assert(
  (A 0/\B 0)\/
  (Cut_opp A 0 /\ B 0)\/
  (A 0 /\Cut_opp B 0)\/
  (Cut_opp A 0 /\ Cut_opp B 0)\/
  (~ A 0 /\ ~ Cut_opp A 0) \/( ~ B 0 /\ ~ Cut_opp B 0)).
      { apply Rmult_situation. auto. auto. }
    rewrite and_or_not5 in H2.
    destruct H2 as [?[?[?[]]]].
  destruct H3 as [?|[?|[?|[?|[]]]]].
  - right. right. left. destruct H3. repeat split. auto.
    rewrite <- Cut_opp_opp. auto. auto.
    exists x0. split;auto. apply not_and_or in H2.
    destruct H2.
    { destruct H2. repeat split; auto. }
    { unfold not in *. intros. destruct H9, H9. rewrite <- Cut_opp_opp in H9.
      apply H2. exists x1, x2. auto. auto. }
  - right;right;right;left. destruct H3. repeat split. auto.
    rewrite <- Cut_opp_opp. auto. auto. apply not_and_or in H4.
    destruct H4.
    { destruct H4. repeat split; auto. }
    { unfold Cut_multNP in *. unfold Cut_opp in *.
      rewrite exists_dist in H4. apply NNPP in H4.
      assert(~0 < x0 \/
      ~ ~
      (exists x2 x3 : Q,
         0 < x2 /\
         0 < x3 /\
         (exists r : Q, 0 < r /\ ~ A (- x2 + - r)) /\ B x3 /\ - (- x + - x0) + - x0 <= x2 * x3)).
    { apply not_and_or. apply (H4 x0). } destruct H9. destruct H9. auto.
      apply NNPP in H9. destruct H9, H9. rewrite (Cut_opp_opp B) in H9.
      exists x1, x2. rewrite Qplus_opp_assoc in H9.
      rewrite <- Qplus_assoc in H9. rewrite (Qplus_comm (--x0) (-x0)) in H9.
      rewrite Qplus_opp_r in H9. rewrite Qplus_0_r in H9.
      rewrite Qopp_involutive in H9. auto. auto. }
  - left. destruct H3. repeat split; auto. apply not_and_or in H5.
    destruct H5.
    { destruct H5. repeat split; auto. }
    { unfold Cut_multPN in *. unfold Cut_opp in *.
      rewrite exists_dist in H5. apply NNPP in H5.
      assert(~0 < x0 \/
      ~ ~
      (exists x2 x3 : Q,
         0 < x2 /\
         0 < x3 /\
         A x2 /\ (exists r : Q, 0 < r /\ ~ B (- x3 + - r)) /\ - (- x + - x0) + - x0 <= x2 * x3)).
    { apply not_and_or. apply (H5 x0). } destruct H9. destruct H9. auto.
      apply NNPP in H9. destruct H9, H9. rewrite (Cut_opp_opp A) in H9.
      exists x1, x2. rewrite Qplus_opp_assoc in H9.
      rewrite <- Qplus_assoc in H9. rewrite (Qplus_comm (--x0) (-x0)) in H9.
      rewrite Qplus_opp_r in H9. rewrite Qplus_0_r in H9.
      rewrite Qopp_involutive in H9. rewrite <- (Cut_opp_opp A) in H9. auto. auto. auto. }
  - right. left. destruct H3. repeat split; auto.
    exists x0. split;auto. apply not_and_or in H6.
    destruct H6.
    { destruct H6. repeat split; auto. }
    { unfold not in *. intros. destruct H9, H9. apply H6.
      exists x1, x2. auto. }
  - repeat right. split. left. auto.
    apply not_and_or in H7. destruct H7.
    { destruct H7. left. auto. }
    { unfold Cut_mult0 in *. rewrite <- Qplus_lt_r with (z:=x) in H7.
      rewrite Qplus_assoc in H7. rewrite Qplus_0_r in H7.
      rewrite Qplus_opp_r in H7. rewrite Qplus_0_l in H7.
      apply Qnot_lt_le in H7. apply Qle_lt_trans with (y:=-x0).
      auto. apply Qopp_lt_compat in H1. auto. }
  - repeat right. split. right. rewrite <- Cut_opp_opp.
    destruct H3. repeat split; auto. auto.
    apply not_and_or in H7. destruct H7.
    { destruct H7. right. auto. }
    { unfold Cut_mult0 in *. rewrite <- Qplus_lt_r with (z:=x) in H7.
      rewrite Qplus_assoc in H7. rewrite Qplus_0_r in H7.
      rewrite Qplus_opp_r in H7. rewrite Qplus_0_l in H7.
      apply Qnot_lt_le in H7. apply Qle_lt_trans with (y:=-x0).
      auto. apply Qopp_lt_compat in H1. auto. }
Qed.


Lemma Cut_mult_opp_r : forall A B : Q -> Prop, forall x : Q, Dedekind A -> Dedekind B ->
 Cut_opp (Cut_mult A B) x <-> Cut_mult A (Cut_opp B) x.
Proof.
  intros. split.
  - apply Cut_mult_opp'. auto. auto.
  - intros. destruct H1 as [?|[?|[?|[]]]].
    + destruct H1, H1, H2, H2, H3, H3.
      destruct H2 as [?[?[?[?]]]].
      apply (Dedekind_properties3 _ H) in H6.
      assert(H':Dedekind B). auto.
      apply Dedekind_opp in H0.
      apply (Dedekind_properties3 _ H0) in H7.
      destruct H6, H6, H7, H7.
      exists (-x+x3*x4)%Q. split.
      { rewrite <- Qplus_lt_r with (z:=x). rewrite Qplus_assoc.
        rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite Qplus_0_r.
        apply Qle_lt_trans with (y:=x0*x1). auto.
        repeat apply Qmult_lt_compat;try apply Qlt_le_weak;auto. }
      unfold not. intros.
      destruct H11 as [?|[?|[?|[]]]].
      * destruct H11, H11.
        apply (Cut_cut_opp_not B 0) in H'. destruct H'.
        exists x2. repeat split;auto. auto.
      * destruct H11, H11.
        apply (Cut_cut_opp_not A 0) in H. destruct H.
        auto. auto.
      * destruct H11, H12, H12, H13. exists x3, x4.
        repeat split;auto.
        apply Qlt_trans with (y:= x0). auto. auto.
        apply Qlt_trans with (y:= x1). auto. auto. rewrite Qplus_opp_assoc.
        repeat try rewrite Qopp_involutive.
        rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
        rewrite Qplus_assoc. rewrite Qplus_assoc.
        rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite <- (Qplus_0_r (x3*x4)).
        rewrite <- Qplus_assoc. rewrite Qplus_le_r with (z:=x3*x4).
        apply Qlt_le_weak. rewrite Qplus_0_l.
        apply Qopp_lt_compat in H12. auto.
      * destruct H11, H11.
        apply (Cut_cut_opp_not A 0) in H. destruct H.
        auto. auto.
      * destruct H11, H11, H11, H11. auto.
        destruct H13. exists x2. repeat split;auto.
    + destruct H1, H1, H2, H2.
      exists (x0)%Q. split. auto. 
      unfold not. intros. apply H4.
      destruct H5 as [?|[?|[?|[]]]].
      * destruct H5, H5.
        apply (Cut_cut_opp_not B 0) in H0. destruct H0.
        auto. auto.
      * destruct H5, H5.
        apply (Cut_cut_opp_not B 0) in H0. destruct H0.
        auto. auto.
      * destruct H5, H5.
        apply (Cut_cut_opp_not A 0) in H. destruct H.
        auto. auto.
      * destruct H5, H6, H6. exists x1, x2.
        auto.
      * destruct H5, H5, H5. destruct H7. auto.
        destruct H7. auto.
    + destruct H1, H1, H2, H2.
      exists (x0)%Q. split. auto. 
      unfold not. intros. apply H4.
      destruct H5 as [?|[?|[?|[]]]].
      * destruct H5, H5, H6, H6. exists x1, x2.
        rewrite <- (Cut_opp_opp B). auto. auto.
      * destruct H5, H5.
        apply (Cut_cut_opp_not A 0) in H. destruct H.
        auto. auto.
      * destruct H5, H5.
        apply (Cut_cut_opp_not B 0) in H0. destruct H0.
        auto. rewrite <- (Cut_opp_opp B) in H3. auto. auto.
      * destruct H5, H5.
        apply (Cut_cut_opp_not A 0) in H. destruct H.
        auto. auto.
      * destruct H5, H5, H5. destruct H5. auto.
        destruct H5. rewrite <- (Cut_opp_opp B) in H3. auto. auto.
    + destruct H1, H1, H2, H2. rewrite <- (Cut_opp_opp B) in *.
    { destruct H2 as [?[?[?[?]]]].
      apply (Dedekind_properties3 _ H0) in H6.
      assert(H':Dedekind A). auto.
      apply Dedekind_opp in H.
      apply (Dedekind_properties3 _ H) in H5.
      destruct H6, H6, H5, H5.
      exists (-x+x3*x2)%Q. split.
      { rewrite <- Qplus_lt_r with (z:=x). rewrite Qplus_assoc.
        rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite Qplus_0_r.
        apply Qle_lt_trans with (y:=x0*x1). auto.
        repeat apply Qmult_lt_compat;try apply Qlt_le_weak;auto. }
      unfold not. intros.
      destruct H10 as [?|[?|[?|[]]]].
      * destruct H10, H10.
        apply (Cut_cut_opp_not A 0) in H'. destruct H'.
        auto. auto.
      * destruct H10, H11, H11, H12. exists x3, x2.
        repeat split;auto.
        apply Qlt_trans with (y:= x0). auto. auto.
        apply Qlt_trans with (y:= x1). auto. auto. rewrite Qplus_opp_assoc.
        repeat try rewrite Qopp_involutive.
        rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
        rewrite Qplus_assoc. rewrite Qplus_assoc.
        rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite <- (Qplus_0_r (x3*x2)).
        rewrite <- Qplus_assoc. rewrite Qplus_le_r with (z:=x3*x2).
        apply Qlt_le_weak. rewrite Qplus_0_l.
        apply Qopp_lt_compat in H11. auto.
      * destruct H10, H10.
        apply (Cut_cut_opp_not A 0) in H'. destruct H'.
        auto. auto.
      * destruct H10, H10.
        apply (Cut_cut_opp_not B 0) in H0. destruct H0.
        auto. auto.
      * destruct H10, H10, H10.
        destruct H12. auto. destruct H10. auto. } auto. auto.
    + destruct H1, H1.
      { exists (-x)%Q. split.
        apply Qopp_lt_compat in H2. auto. destruct H1.
        unfold not. intros. destruct H4 as [?|[?|[?|[]]]].
      * destruct H4, H4, H1. auto.
      * destruct H4, H4, H3. auto.
      * destruct H4, H4, H1. auto.
      * destruct H4, H4, H3. auto.
      * destruct H4, H4. unfold Cut_mult0 in H5.
        rewrite (Qplus_opp_r (-x)) in H5. inversion H5.
        destruct H4, H4. unfold Cut_mult0 in H5.
        rewrite (Qplus_opp_r (-x)) in H5. inversion H5. }
      { exists (-x)%Q. split.
        apply Qopp_lt_compat in H2. auto. destruct H1.
        unfold not. intros. destruct H4 as [?|[?|[?|[]]]].
      * destruct H4, H4, H3. rewrite <- Cut_opp_opp. auto. auto.
      * destruct H4, H4, H3. rewrite <- Cut_opp_opp. auto. auto.
      * destruct H4, H4, H1. auto.
      * destruct H4, H4, H1. auto.
      * destruct H4, H4. unfold Cut_mult0 in H5.
        rewrite (Qplus_opp_r (-x)) in H5. inversion H5.
        destruct H4, H4. unfold Cut_mult0 in H5.
        rewrite (Qplus_opp_r (-x)) in H5. inversion H5. }
Qed.

Lemma Cut_mult_opp_l : forall A B : Q -> Prop, forall x : Q, Dedekind A -> Dedekind B ->
 Cut_opp (Cut_mult A B) x <-> Cut_mult (Cut_opp A) B x.
Proof.
  intros. rewrite Cut_mult_comm.
assert(forall x : Q, Cut_opp (Cut_mult A B) x <-> Cut_opp (Cut_mult B A) x).
   { rewrite <- (Cut_opp_eq (Cut_mult A B) (Cut_mult B A)).
   split; rewrite Cut_mult_comm;auto. 
    apply Dedekind_mult. auto. auto.
    apply Dedekind_mult. auto. auto. }
  split.
  - intros. apply H1 in H2. apply Cut_mult_opp_r. auto. auto. auto.
  - intros. apply H1. apply Cut_mult_opp_r. auto. auto. auto.
Qed.

Lemma Cut_mult0_trans : forall B C : Q -> Prop, 
 Dedekind B -> Dedekind C -> O B C -> ~ Cut_mult B C 0 /\ ~ Cut_opp (Cut_mult B C) 0.
Proof.
  intros. rename H into DB. rename H0 into DC. unfold not. destruct H1, H. { split. { intros.
  destruct H1 as [?|[?|[?|[?|[]]]]].
  { destruct H1, H1, H. auto. }
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. auto. }
  { destruct H1, H1, H0. auto. }
  { inversion H2. } } rewrite Cut_mult_opp_l by auto. intros.
  destruct H1 as [?|[?|[?|[?|[]]]]].
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. apply Cut_opp_opp. auto. auto. }
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. apply Cut_opp_opp. auto. auto. }
  { inversion H2. } }
  { rewrite Cut_mult_comm. split. { intros.
  destruct H1 as [?|[?|[?|[?|[]]]]].
  { destruct H1, H1, H. auto. }
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. auto. }
  { destruct H1, H1, H0. auto. }
  { inversion H2. } } rewrite Cut_mult_opp_r by auto. rewrite Cut_mult_comm. intros.
  destruct H1 as [?|[?|[?|[?|[]]]]].
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. apply Cut_opp_opp. auto. auto. }
  { destruct H1, H1, H0. auto. }
  { destruct H1, H1, H. apply Cut_opp_opp. auto. auto. }
  { inversion H2. } }
Qed.

Lemma Cut_mult_eq : forall (A B C : Q -> Prop), Dedekind A -> Dedekind B -> Dedekind C ->
  (forall x : Q, B x <-> C x) -> (forall x : Q, Cut_mult A B x <-> Cut_mult A C x).
Proof.
  intros.
  assert(forall (A B C : Q -> Prop), Dedekind A -> Dedekind B -> Dedekind C ->
  (forall x : Q, B x <-> C x) -> (forall x : Q, Cut_mult A B x -> Cut_mult A C x)).
  { clear A B C H H0 H1 H2 x. intros. destruct H3 as [?|[?|[?|[]]]].
    + left. destruct H3, H3. split.
      * split;auto. apply H2. auto.
      * destruct H4, H4. exists x0, x1. rewrite <- H2. auto.
    + right; left. destruct H3, H3. split.
      * split;auto. apply H2. auto.
      * destruct H4, H4. exists x0. split;auto. unfold not. intros.
        destruct H6, H7, H6. exists x1, x2. rewrite H2. auto.
    + right;right;left. destruct H3, H3. apply Cut_opp_eq in H2;auto. split.
      * split;auto. apply H2. auto.
      * destruct H4, H4. exists x0. split;auto. unfold not. intros.
        destruct H6, H7, H6. exists x1, x2. rewrite (H2 x2). auto.
    + right;right;right;left. destruct H3, H3. apply Cut_opp_eq in H2;auto. split.
      * split;auto. apply H2. auto.
      * destruct H4, H4. exists x0, x1. rewrite <- (H2 x1). auto.
    + repeat right. destruct H3, H3, H3.
      * split. left;auto. auto.
      * split. right. unfold not; split;intros.
        destruct H3. apply H2;auto.
        apply Cut_opp_eq in H2;auto.
        destruct H5. apply H2;auto. auto. }
  split;apply H3;auto. intros. split;apply H2;auto.
Qed.

Lemma Cut_mult_opp_opp_l : forall (A B : Q -> Prop) (x : Q),
Dedekind A -> Dedekind B ->
 Cut_opp (Cut_opp (Cut_mult A B)) x <->
        Cut_opp (Cut_mult (Cut_opp A) B) x.
Proof.
  intros. generalize dependent x.
  rewrite <- (Cut_opp_eq (Cut_opp (Cut_mult A B)) (Cut_mult (Cut_opp A) B)).
  { hnf. intros. rewrite Cut_mult_opp_l by auto. reflexivity. }
  { apply Dedekind_opp;apply Dedekind_mult;auto. }
  { apply Dedekind_mult;try apply Dedekind_opp;auto. }
Qed.

Lemma Cut_mult_opp_opp_r : forall (A B : Q -> Prop) (x : Q),
Dedekind A -> Dedekind B ->
 Cut_opp (Cut_opp (Cut_mult A B)) x <->
        Cut_opp (Cut_mult A (Cut_opp B)) x.
Proof.
  intros. generalize dependent x.
  rewrite <- (Cut_opp_eq (Cut_opp (Cut_mult A B)) (Cut_mult A (Cut_opp B))).
  { hnf. intros. rewrite Cut_mult_opp_r by auto. reflexivity. }
  { apply Dedekind_opp;apply Dedekind_mult;auto. }
  { apply Dedekind_mult;try apply Dedekind_opp;auto. }
Qed.

Lemma Cut_mult_assoc_lemma1 : forall (A B C : Q -> Prop) (x : Q),
  Dedekind A -> Dedekind B -> Dedekind C -> A 0 -> B 0 -> C 0 ->
 Cut_mult (Cut_mult A B) C x -> Cut_mult A (Cut_mult B C) x.
Proof.
  intros.
  assert(HAB:Dedekind (Cut_mult A B)).
  { apply Dedekind_mult. auto. auto. }
  assert(HBC:Dedekind (Cut_mult B C)).
  { apply Dedekind_mult. auto. auto. }
unfold Cut_mult in *.
    assert(H':Cut_mult A B 0).
    { apply PPmult. auto. auto. auto. auto. }
  destruct H5 as [?|[?|[?|[?|[]]]]].
  - destruct H5, H5. destruct H6, H6, H6, H8, H9, H10. destruct H9 as [?|[?|[?|[?|[]]]]].
    + left. split.
      * destruct H9, H9. split; auto. left. repeat split; auto.
        apply (Dedekind_properties3 _) in H13.
        apply (Dedekind_properties3 _) in H7.
        { destruct H13, H13, H7, H7. exists x2, x3.
          repeat split;auto. rewrite <- (Qmult_0_l 0).
          apply Qlt_le_weak.
          repeat apply (Qmult_lt_compat 0 x2 0 x3);auto;apply Qle_refl. }
        auto. auto.
      * destruct H9, H9. destruct H12, H12, H12, H14, H15, H16.
          exists x2, (x3*x1). repeat split;auto.
          { rewrite <- (Qmult_0_l 0).
            apply (Qmult_lt_compat 0 x3 0 x1);auto;apply Qle_refl. }
          { left. repeat split;auto. exists x3, x1.
            repeat split;auto;apply Qle_refl. }
          { apply Qle_trans with (y:=x0*x1). auto.
            rewrite Qmult_assoc. rewrite Qmult_le_r. auto. auto. }
    + destruct H9, H9. apply (Cut_cut_opp_not A 0) in H.
            destruct H. auto. auto.
    + destruct H9, H9. apply (Cut_cut_opp_not B 0) in H0.
            destruct H0. auto. auto.
    + destruct H9, H9. apply (Cut_cut_opp_not A 0) in H.
            destruct H. auto. auto.
    + destruct H9, H9, H9. auto. auto.
  - destruct H5, H5.
    apply (Cut_cut_opp_not (Cut_mult A B) 0) in HAB.
    destruct HAB. auto. auto.
  - destruct H5, H5.
    apply (Cut_cut_opp_not C 0) in H1.
    destruct H1. auto. auto.
  - destruct H5, H5.
    apply (Cut_cut_opp_not C 0) in H1.
    destruct H1. auto. auto.
  - destruct H5, H5, H5. auto. auto.
Qed.

Lemma Cut_mult_assoc_lemma2 : forall (A B C : Q -> Prop) (x : Q),
  Dedekind A -> Dedekind B -> Dedekind C -> A 0 -> Cut_opp B 0 -> C 0 ->
 Cut_mult (Cut_mult A B) C x -> Cut_mult A (Cut_mult B C) x.
Proof.
  intros.
  assert(HAB:Dedekind (Cut_mult A B)).
  { apply Dedekind_mult. auto. auto. }
  assert(HBC:Dedekind (Cut_mult B C)).
  { apply Dedekind_mult. auto. auto. }
unfold Cut_mult. right; right; left. rename H2 into AP.
  rename H3 into BN. rename H4 into CP.
  assert(H':Cut_opp (Cut_mult B C) 0).
  { rewrite Cut_mult_opp_l. assert(H':C 0). auto.
        assert(H'':Cut_opp B 0). auto.
        apply (Dedekind_properties3 _) in CP.
        apply (Dedekind_properties3 _) in BN.
        { destruct CP, H2, BN, H4. left.
          repeat split;auto.
          exists x1, x0. repeat split;auto.
          apply Qlt_le_weak.
          repeat apply (Qmult_lt_compat 0 x1 0 x0);auto;apply Qle_refl. }
  apply Dedekind_opp. auto. auto. auto. auto.  }
  assert(H'':Cut_opp (Cut_mult A B) 0).
  { rewrite Cut_mult_opp_r. assert(H''':A 0). auto.
        assert(H'':Cut_opp B 0). auto.
        apply (Dedekind_properties3 _) in AP.
        apply (Dedekind_properties3 _) in BN.
        { destruct AP, H2, BN, H4. left.
          repeat split;auto.
          exists x0, x1. repeat split;auto.
          apply Qlt_le_weak.
          repeat apply (Qmult_lt_compat 0 x0 0 x1);auto;apply Qle_refl. }
  apply Dedekind_opp. auto. auto. auto. auto.  }
  destruct H5 as [?|[?|[?|[?|[]]]]].
  - destruct H2, H2.
    apply (Cut_cut_opp_not (Cut_mult A B) 0) in H2.
    destruct H2. auto. apply Dedekind_mult. auto. auto.
  - destruct H2, H3, H3. split.
    * split. auto. auto.
    * exists x0. split;auto. unfold not. intros. destruct H4, H5, H4.
      destruct H4 as [?[?[?[]]]]. apply Cut_mult_opp_l in H7.
      { destruct H7 as [?|[?|[?|[]]]].
      { destruct H7, H9, H9. destruct H9 as [?[?[?[]]]].
        exists (x1*x3), x4. rewrite Cut_mult_opp_r by (apply (H0, H)).
        repeat split;auto.
        { apply Qlt_mult0. auto. auto. }
        { left. repeat split;auto. exists x1, x3. repeat split;auto.
          apply Qle_refl. }
        { apply Qle_trans with (y:=x1*x2). auto. rewrite <- Qmult_assoc.
          apply Qmult_le_compat_l. auto. apply Qlt_le_weak. auto. } }
      { destruct H7, H7. apply (Cut_cut_opp_not (Cut_opp B) 0) in BN.
        destruct BN. auto. apply Dedekind_opp. auto. }
      { destruct H7, H7. apply (Cut_cut_opp_not C 0) in CP.
        destruct CP. auto. auto. }
      { destruct H7, H7. apply (Cut_cut_opp_not C 0) in CP.
        destruct CP. auto. auto. }
      { destruct H7, H7, H7. destruct H7. auto. destruct H7. auto. } }
      auto. auto.
  - destruct H2, H2.
    apply (Cut_cut_opp_not (Cut_mult A B) 0) in H2.
    destruct H2. auto. apply Dedekind_mult. auto. auto.
  - destruct H2, H2.
    apply (Cut_cut_opp_not C 0) in CP.
    destruct CP. auto. auto.
  - destruct H2, H2. destruct H4. auto. destruct H2. auto.
Qed.

Lemma Cut_mult_assoc_lemma3 : forall (A B C : Q -> Prop) (x : Q),
  Dedekind A -> Dedekind B -> Dedekind C -> A 0 -> Cut_opp C 0 -> B 0 ->
 Cut_mult (Cut_mult A B) C x -> Cut_mult A (Cut_mult B C) x.
Proof.
  intros. 
  assert(HAB:Dedekind (Cut_mult A B)).
  { apply Dedekind_mult. auto. auto. }
  assert(HBC:Dedekind (Cut_mult B C)).
  { apply Dedekind_mult. auto. auto. }
  assert(HA:Dedekind (Cut_opp A)).
  { apply Dedekind_opp. auto. }
  assert(HB:Dedekind (Cut_opp B)).
  { apply Dedekind_opp. auto. }
  assert(HC:Dedekind (Cut_opp C)).
  { apply Dedekind_opp. auto. }
  apply Cut_opp_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_r;auto.
  rewrite Cut_mult_opp_r;try apply Dedekind_opp;auto.
    apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp B) (Cut_opp C)));
    auto;try apply Dedekind_mult;try apply Dedekind_opp;
    try apply Dedekind_opp;auto.
    intros. rewrite <- Cut_mult_opp_l;auto.
    rewrite Cut_mult_opp_opp_r;try reflexivity;auto.
  rewrite Cut_opp_opp in H4 by auto.
  apply Cut_opp_opp in H5;try apply Dedekind_mult;auto.
    apply Cut_mult_opp_opp_l with (x:=x) in H5;auto.
    rewrite Cut_mult_opp_r in H5;try apply Dedekind_opp;auto.
    rewrite Cut_mult_comm in H5.
    apply Cut_mult_eq with (B:=(Cut_mult A (Cut_opp B))) in H5;
    auto;try apply Dedekind_mult;try apply Dedekind_opp;
    try apply Dedekind_opp;auto.
    { rewrite Cut_mult_comm in H5.
    apply Cut_mult_assoc_lemma2;auto. }
    intros. rewrite <- Cut_mult_opp_r;auto;reflexivity.
Qed.

Lemma Cut_mult_assoc : forall (A B C : Q -> Prop) (x : Q),
  Dedekind A -> Dedekind B -> Dedekind C ->
 Cut_mult (Cut_mult A B) C x -> Cut_mult A (Cut_mult B C) x.
Proof.
  intros.
  assert(HAB:Dedekind (Cut_mult A B)).
  { apply Dedekind_mult. auto. auto. }
  assert(HBC:Dedekind (Cut_mult B C)).
  { apply Dedekind_mult. auto. auto. }
  assert(HC:C 0 \/ Cut_opp C 0 \/ (~ C 0/\~ Cut_opp C 0)).
  { apply Cut_mult_situation1. }
  assert(HA:A 0 \/ Cut_opp A 0 \/ (~ A 0/\~ Cut_opp A 0)).
  { apply Cut_mult_situation1. }
  assert(HB:B 0 \/ Cut_opp B 0 \/ (~ B 0/\~ Cut_opp B 0)).
  { apply Cut_mult_situation1. }
  destruct HC as [CP|[CN|[C0]]].
{ destruct HA as [AP|[AN|[A0]]].
{ destruct HB as [BP|[BN|[B0]]].
{ apply Cut_mult_assoc_lemma1;auto. }
{ apply Cut_mult_assoc_lemma2;auto. }
{ repeat right. split. { right. apply Cut_mult0_trans; auto;left;split;auto. }
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;right;split;auto. } destruct H4.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H4. auto. }
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H4. auto. }
  { destruct H2, H2, H5. auto. }
  { apply H6. } } }
{ destruct HB as [?|[]].
{ apply Cut_opp_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_l;auto. rewrite Cut_mult_opp_r.
  { apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp B) C));try apply Dedekind_opp;
    try apply Dedekind_mult;try apply Dedekind_opp;auto.
    intros. rewrite Cut_mult_opp_l. reflexivity. auto. auto.
    rewrite Cut_opp_opp in H3 by auto.
    apply Cut_opp_opp in H2;try apply Dedekind_mult;auto.
    apply Cut_mult_opp_opp_l with (x:=x) in H2;auto.
    rewrite Cut_mult_opp_l in H2. { rewrite Cut_mult_comm in H2.
    apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp A) (Cut_opp B))) in H2;
    auto;try apply Dedekind_mult;try apply Dedekind_opp;
    try apply Dedekind_opp;auto.
    { rename H3 into BN. rename AN into AP. rewrite Cut_mult_comm in H2.
    apply Dedekind_opp in H0. apply Dedekind_opp in H.
    apply Cut_mult_assoc_lemma2;auto. }
    intros. rewrite <- Cut_mult_opp_l.
    rewrite Cut_mult_opp_opp_r;try reflexivity;auto. auto.
    apply Dedekind_opp;auto. }
    apply Dedekind_opp;apply Dedekind_mult;auto. auto. }
    apply Dedekind_opp;auto. apply Dedekind_mult;auto. }
{ apply Cut_opp_opp;try apply Dedekind_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_l;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_r;try apply Dedekind_opp;auto.
  apply Cut_mult_eq with (B:=((Cut_mult (Cut_opp B) C)));
  try auto;try apply Dedekind_mult;try apply Dedekind_opp;auto;
  try apply Dedekind_mult;try apply Dedekind_opp;auto.
 { intros;rewrite Cut_mult_opp_l;auto;reflexivity. }
   rewrite Cut_mult_comm in H2.
   apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp A) (Cut_opp B))) in H2;
   auto;try apply Dedekind_mult;try apply Dedekind_opp;
   try apply Dedekind_opp;auto. rewrite Cut_mult_comm in H2. {
   rename AN into AP. rename H3 into BP. clear HAB HBC.
   apply Dedekind_opp in H0. apply Dedekind_opp in H.
  assert(HAB:Dedekind (Cut_mult (Cut_opp A) (Cut_opp B))).
  { apply Dedekind_mult. auto. auto. }
  assert(HBC:Dedekind (Cut_mult (Cut_opp B) C)).
  { apply Dedekind_mult. auto. auto. }
  apply Cut_mult_assoc_lemma1;auto. }
    intros. rewrite <- Cut_mult_opp_l;try rewrite <- Cut_mult_opp_opp_r;
    try rewrite <- Cut_opp_opp;try apply Dedekind_opp;auto.
    reflexivity. }
{ destruct H3. repeat right. split. { right. apply Cut_mult0_trans; auto;left;split;auto. }
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;right;split;auto. } destruct H5.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H6. auto. }
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H6. auto. }
  { apply H7. } } }
repeat right. split. { left. split;auto. }
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;left;split;auto. } destruct H4.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H4. auto. }
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H4. auto. }
  { destruct H2, H2, H5. auto. }
  { apply H6. } }
{ destruct HA as [?|[]].
{ destruct HB as [?|[]].
{ apply Cut_mult_assoc_lemma3;auto. }
{ assert(HB:Dedekind (Cut_opp B)).
  { apply Dedekind_opp. auto. }
  assert(HC:Dedekind (Cut_opp C)).
  { apply Dedekind_opp. auto. }
  apply Cut_opp_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_r;auto.
  apply Cut_mult_opp_r;try apply Dedekind_opp;auto.
  apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp B) (Cut_opp C)));
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { intros. rewrite <- Cut_mult_opp_r;auto.
    rewrite <- Cut_mult_opp_opp_l;auto. reflexivity. }
  apply Cut_opp_opp in H2;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_l in H2;auto.
  apply Cut_mult_opp_r in H2;try apply Dedekind_opp;auto.
  apply Cut_mult_comm in H2.
  apply Cut_mult_eq with (B:=(Cut_mult A (Cut_opp B))) in H2;
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { apply Cut_mult_assoc_lemma1;try apply Cut_mult_comm;auto. }
  { intros. rewrite <- Cut_mult_opp_r;auto. reflexivity. } }
{ clear H3. destruct H4. repeat right. split. { right. apply Cut_mult0_trans; auto;left;split;auto. }
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;right;split;auto. } destruct H5.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H6. auto. }
  { destruct H2, H2, H5. auto. }
  { destruct H2, H2, H6. auto. }
  { apply H7. } } }
{ destruct HB as [?|[]].
{ assert(HA:Dedekind (Cut_opp A)).
  { apply Dedekind_opp. auto. }
  assert(HC:Dedekind (Cut_opp C)).
  { apply Dedekind_opp. auto. }
  apply Cut_opp_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_r;auto.
  apply Cut_mult_opp_l;try apply Dedekind_opp;auto.
  apply Cut_mult_eq with (B:=(Cut_mult B (Cut_opp C)));
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { intros. rewrite <- Cut_mult_opp_r;auto. reflexivity. }
  apply Cut_opp_opp in H2;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_l in H2;auto.
  apply Cut_mult_opp_r in H2;try apply Dedekind_opp;auto.
  apply Cut_mult_comm in H2.
  apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp A) B)) in H2;
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { apply Cut_mult_assoc_lemma1;try apply Cut_mult_comm;auto. }
  { intros. rewrite Cut_mult_opp_l;auto. reflexivity. } }
{ assert(HA:Dedekind (Cut_opp A)).
  { apply Dedekind_opp. auto. }
  assert(HC:Dedekind (Cut_opp C)).
  { apply Dedekind_opp. auto. }
  assert(HB:Dedekind (Cut_opp B)).
  { apply Dedekind_opp. auto. }
  apply Cut_opp_opp;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_r;auto.
  apply Cut_mult_opp_l;try apply Dedekind_opp;auto.
  apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp B) C));
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { intros. rewrite <- Cut_mult_opp_l;auto. reflexivity. }
  apply Cut_opp_opp in H2;try apply Dedekind_mult;auto.
  apply Cut_mult_opp_opp_l in H2;auto.
  apply Cut_mult_opp_l in H2;try apply Dedekind_opp;auto.
  apply Cut_mult_comm in H2.
  apply Cut_mult_eq with (B:=(Cut_mult (Cut_opp A) (Cut_opp B))) in H2;
  try apply Dedekind_mult;try repeat apply Dedekind_opp;auto.
  { apply Cut_mult_assoc_lemma3;try apply Cut_mult_comm;auto. }
  { intros. rewrite <- Cut_mult_opp_r;auto.
    rewrite <- Cut_mult_opp_opp_l;auto. reflexivity. } }
{ repeat right. split. right. apply Cut_mult0_trans;try left;auto.
  destruct H4.
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;right;split;auto. } destruct H6.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H6;auto. }
  { destruct H2, H2, H7;auto. }
  { destruct H2, H2, H6;auto. }
  { destruct H2, H2, H7;auto. }
  { apply H8. } } }
{ repeat right. split. left. auto.
  destruct H3.
  assert(~ Cut_mult A B 0 /\ ~ Cut_opp (Cut_mult A B) 0).
  { apply Cut_mult0_trans; auto;left;split;auto. } destruct H5.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, H5;auto. }
  { destruct H2, H2, H6;auto. }
  { destruct H2, H2, H5;auto. }
  { destruct H2, H2, H6;auto. }
  { apply H7. } } }
{ repeat right. split. right. apply Cut_mult0_trans;try right;auto.
  assert(~ Cut_mult B C 0 /\ ~ Cut_opp (Cut_mult B C) 0).
  { apply Cut_mult0_trans; auto;right;split;auto. } destruct H4.
  destruct H2 as [?|[?|[?|[?|[]]]]].
  { destruct H2, H2, C0;auto. }
  { destruct H2, H2, C0;auto. }
  { destruct H2, H2, H3;auto. }
  { destruct H2, H2, H3;auto. }
  { apply H6. } }
Qed.

Lemma R_mult_comp1 : forall x x0 y y0 : Real, (x==y -> x0==y0 -> x*x0<=y*y0)%R.
Proof.
  intros.
    unfold Rmult, Rle. destruct x, y, x0, y0. intros.
    unfold Cut_mult in *.
    assert(forall x : Q, Cut_opp A x <-> Cut_opp A0 x).
    { rewrite <- (Cut_opp_eq A A0). split. apply H. apply H. auto. auto. }
    assert(forall x : Q, Cut_opp A1 x <-> Cut_opp A2 x).
    { rewrite <- (Cut_opp_eq A1 A2). split. apply H0. apply H0. auto. auto. }
   destruct H5 as [?|[?|[?|[?|[]]]]].
    + left. destruct H5. repeat split.
      * unfold Req, Rle in H. apply H, H5.
      * unfold Req, Rle in H0. apply H0, H5.
      * destruct H8, H8. destruct H8 as [?[?[?[?]]]].
        exists x0, x1. repeat split;auto.
        { apply H. auto. }
        { apply H0. auto. }
    + right; left. destruct H5, H5. repeat split.
      * unfold Req, Rle in H. apply H6, H5.
      * apply H0, H9.
      * destruct H8, H8. exists x0. split;auto. unfold not in *.
        intros. apply H10. destruct H11, H11. destruct H11 as [?[?[?[?]]]].
        exists x1, x2. repeat split;auto.
        { apply H6, H13. }
        { apply H0. auto. }
    + right; right; left. destruct H5, H5. repeat split.
      * apply H, H5.
      * apply H7, H9.
      * destruct H8, H8. exists x0. split;auto. unfold not in *.
        intros. apply H10. destruct H11, H11. destruct H11 as [?[?[?[?]]]].
        exists x1, x2. repeat split;auto.
        { apply H. auto. }
        { apply H7, H14. }
    + right; right; right; left. destruct H5, H5. repeat split.
      * apply H6; auto.
      * apply H7; auto.
      * destruct H8, H8. destruct H8 as [?[?[?[?]]]].
        exists x0, x1. repeat split;auto.
        { apply H6; auto. }
        { apply H7; auto. }
    + repeat right. destruct H5.
      { destruct H5. split.
        { left. unfold not in *. split.
          { intros. apply H5, H. auto. }
          { intros. apply H9, H6. auto. } }
          auto. }
      { destruct H5. split.
        { right. unfold not in *. split.
          { intros. apply H5, H0. auto. }
          { intros. apply H9, H7. auto. } }
          auto. }
Qed.

Instance R_mult_comp : Proper(Req ==> Req ==> Req) Rmult.
Proof.
  split.
  - apply R_mult_comp1. auto. auto.
  - apply R_mult_comp1. rewrite H. reflexivity.
    rewrite H0. reflexivity.
Qed.

Lemma Ropp_opp : forall a : Real, (a == - - a)%R.
Proof.
  intros. unfold Req, Ropp, Rle. destruct a. split.
  - apply Cut_opp_opp. auto.
  - intros. apply Cut_opp_opp. auto. auto.
Qed.

Lemma Rmult_opp_r : forall a b : Real, (- (a * b) == a * (-b))%R.
Proof.
  intros. assert(forall a b : Real, (- (a * b) <= a * - b)%R).
  { intros. unfold Rle, Rmult, Ropp. destruct a0, b0. intros. apply Cut_mult_opp'. auto. auto. auto. }
   split.
  - unfold Rle, Rmult, Ropp. destruct a, b. intros. apply Cut_mult_opp'. auto. auto. auto.
  - assert((a * (- - b) == (a * b))%R).
    { intros. rewrite <- (Ropp_opp b). reflexivity. }
    rewrite Ropp_opp. rewrite <- H0. unfold Rle, Rmult, Ropp.
    destruct a, b. intros. destruct H3, H3. exists x0.
    split;auto. unfold not. intros. apply H4.
    apply Cut_mult_opp_r;auto. apply Dedekind_opp;auto.
Qed.

(** Third , we will define the plus operation of Set and Real
    and proof some theorem about it. *)
Theorem Rmult_0_r : forall a : Real, (a * Rzero == Rzero)%R.
Proof.
  intros. unfold Rmult. destruct a. unfold Rzero.
  unfold Cut_mult, Req. split.
  - unfold Rle. intros.
    destruct H0.
  * destruct H0, H0. inversion H2.
  * destruct H0. ** destruct H0, H0. inversion H2.
 ** destruct H0. *** destruct H0, H0, H2, H2.
    rewrite Qlt_minus_iff in H3.
    rewrite Qplus_0_l in H3. rewrite Qplus_0_l in H3.
    rewrite Qopp_involutive in H3.
    exfalso. apply H3, H2.
*** destruct H0. **** destruct H0, H0, H2, H2.
    rewrite Qlt_minus_iff in H3.
    rewrite Qplus_0_l in H3. rewrite Qplus_0_l in H3.
    rewrite Qopp_involutive in H3.
    exfalso. apply H3, H2.
**** destruct H0. unfold Cut_mult0 in H1. apply H1.
  - unfold Rle. intros. repeat right. split.
  + right. split.
  * unfold not. intros. inversion H1.
  * unfold not. intros. destruct H1, H1.
    rewrite Qlt_minus_iff in H2.
    rewrite Qplus_0_l in H2. rewrite Qplus_0_l in H2.
    rewrite Qopp_involutive in H2.
    exfalso. apply H2, H1.
  + apply H0.
Qed.

Lemma Cut_Cut_opp : forall (A : Q -> Prop) (x : Q),
  Dedekind A -> ~ A x -> (forall x0, x0 > 0 -> Cut_opp A (-x-x0)).
Proof.
  intros. hnf. exists x0. split. auto.
  assert(- (- x - x0) + - x0 == x)%Q.
  { rewrite (Qmult_plus_distr_r (-1%Q) (-x) (-x0)).
    assert(-(1)*(-x0)==--x0)%Q.
    { reflexivity. } rewrite H2. rewrite Qopp_involutive.
    rewrite <- Qplus_assoc.
    rewrite Qplus_opp_r. rewrite Qplus_0_r. rewrite Qopp_involutive. reflexivity. }
    rewrite H2. auto.
Qed.


Lemma Rzero_opp : (Rzero == - Rzero)%R.
Proof.
  apply (Rplus_compat_l Rzero). rewrite Rplus_opp.
  rewrite Rplus_0_r. reflexivity.
Qed.

Theorem Rmult_1_r : forall a : Real, (a * Rone == a)%R.
Proof.
  intros. unfold Rmult, Req, Rone. destruct a.
  unfold Cut_mult. split.
  - unfold Rle. intros.
    destruct H0.
    * unfold Cut_multPP in H0.
      destruct H0, H0, H1, H1, H1, H3, H4, H5.
      apply (Dedekind_properties2 _ H x0). split. auto.
      apply (Qle_trans x (x0*x1) x0). auto.
      rewrite <- (Qmult_1_r x0). rewrite <- Qmult_assoc.
      rewrite Qmult_1_l. rewrite Qmult_comm. rewrite (Qmult_comm x0 1).
      apply Qmult_le_compat_r.
      apply Qlt_le_weak. auto.
      apply Qlt_le_weak. auto.
    * destruct H0. ** destruct H0, H0, H1, H1.
      assert(A x \/ ~ A x). { apply classic. }
      destruct H4. auto.
      exfalso. apply H3. assert (H':Dedekind A). auto.
      apply Dedekind_opp in H.
      apply (Dedekind_properties3 _ H 0) in H0.
      destruct H0. destruct H0.
      assert(- x + - x0 > 0).
      { apply Qnot_le_lt. unfold not in *. intros. apply H3.
        exists x1, (1#2). repeat split; auto.
        apply Qle_trans with (y:= 0). auto.
        rewrite <- (Qmult_0_r 0). apply Qlt_le_weak.
        apply Qmult_lt_compat. apply Qle_refl.
        apply Qle_refl. auto. reflexivity.  }
      exists (- x + - (x0/(2#1))%Q), ((- x + - x0)/(- x + - (x0/(2#1))%Q)).
      assert(0< - x + - (x0 / (2 # 1))).
      { apply Qplus_lt_l with (z:=- (x0 / (2 # 1))).
        apply Qplus_lt_l with (z:=(x0 / (2 # 1))).
        rewrite <- (Qplus_assoc (-x) (- (x0 / (2 # 1))) (- (x0 / (2 # 1))) ).
        rewrite <- (Qdiv2_opp x0).
        rewrite <- Qplus_assoc.
        rewrite (Qplus_comm (- (x0 / (2 # 1))) (x0 / (2 # 1)) ).
        rewrite Qplus_opp_r.
        apply Qplus_lt_le_compat. auto.
        apply Qmult_le_0_compat. apply Qlt_le_weak, H1.
        apply Qlt_le_weak. reflexivity. }
      repeat split.
      + auto.
      + rewrite <- (Qmult_0_r 0). apply Qmult_lt_compat.
        apply Qle_refl. apply Qle_refl. auto.
        apply Qlt_shift_inv_l. auto.
        rewrite Qmult_0_l. reflexivity.
      + apply Cut_Cut_opp. auto. auto.
        apply Qlt_shift_div_l. auto. apply H1.
      + apply Qlt_shift_div_r. auto.
        rewrite (Qdiv2_opp x0). rewrite Qplus_assoc.
        rewrite Qplus_comm. rewrite Qmult_1_l.
        rewrite <- (Qplus_0_l (- x + - (x0 / (2 # 1)))).
        rewrite Qplus_lt_l. rewrite Qlt_minus_iff.
        rewrite Qopp_involutive. rewrite Qplus_0_l.
        apply Qlt_shift_div_l. auto. apply H1.
      + assert((- x + - (x0 / (2 # 1))) * ((- x + - x0) / (- x + - (x0 / (2 # 1))))==(- x + - x0))%Q.
        { rewrite Qmult_comm.
          rewrite <- (Qmult_assoc ((- x + - x0)) (/ (- x + - (x0 / (2 # 1)))) ((- x + - (x0 / (2 # 1))))).
          rewrite (Qmult_comm (/ (- x + - (x0 / (2 # 1)))) ).
          rewrite Qmult_assoc. apply Qdiv_mult_l.
          hnf. intros. apply Qlt_not_eq in H7. apply H7. rewrite H8.
          reflexivity. }
        rewrite H8. apply Qle_refl.
     ** destruct H0. *** destruct H0, H0, H1, H1, H2, H2, H4.
        rewrite Qplus_0_l. apply Qlt_trans with (y:=0).
        + rewrite Qlt_minus_iff. rewrite Qopp_involutive.
          rewrite Qplus_0_l. auto.
        + reflexivity.
    *** destruct H0. **** destruct H0, H0, H2, H2, H3.
        rewrite Qplus_0_l. apply Qlt_trans with (y:=0).
        + rewrite Qlt_minus_iff. rewrite Qopp_involutive.
          rewrite Qplus_0_l. auto.
        + reflexivity.
   **** destruct H0. destruct H0, H0.
        + unfold Cut_mult0 in H1. unfold Cut_opp in H2.
          rewrite exists_dist in H2. apply NNPP in H2.
          assert(~ (0 < - x /\ ~ A (- 0 + - - x))). apply (H2 (-x)).
          apply not_and_or in H3. destruct H3.
          { destruct H3. rewrite <- (Qplus_0_l (-x)).
            rewrite <- Qlt_minus_iff. auto. }
          { apply NNPP in H3. rewrite Qopp_involutive in H3.
            rewrite <- Qplus_0_l. auto. }
        + destruct H0. reflexivity.
  - unfold Rle. intros.
    assert(  (A 0/\(fun x0 : Q => x0 < 1) 0)\/
  (Cut_opp A 0 /\ (fun x0 : Q => x0 < 1) 0)\/
  (A 0 /\Cut_opp (fun x0 : Q => x0 < 1) 0)\/
  (Cut_opp A 0 /\ Cut_opp (fun x0 : Q => x0 < 1) 0)\/
  (~ A 0 /\ ~ Cut_opp A 0) \/( ~ (fun x0 : Q => x0 < 1) 0 /\ ~ Cut_opp (fun x0 : Q => x0 < 1) 0)).
    { apply Rmult_situation with (B:=(fun x0 : Q => x0 < 1)).
      auto. apply (Dedekind_Q 1). }
    destruct H1. * left. split.
    + auto.
    + unfold Cut_multPP. apply (Dedekind_properties3 _ H) in H0.
      assert(0 < x\/~0 < x). apply classic.
      destruct H0, H0, H2. assert (0 < x0).
      { apply Qlt_trans with (y:=x). auto. auto. }
      { exists x0, (x/x0). split. auto. split.
      { apply Qlt_shift_div_l. auto.
        { rewrite Qmult_0_l. auto. } } split.
      { auto. } split.
      { apply Qlt_shift_div_r. auto. rewrite Qmult_1_l. auto. }
        rewrite Qmult_div_r. apply Qle_refl. unfold not.
        intros. rewrite H5 in H4. inversion H4. }
      { destruct H1. apply (Dedekind_properties3 _ H) in H1.
        destruct H1, H1. exists x1, (1#2).
        repeat split;auto.
        apply Qnot_lt_le in H2. apply Qle_trans with (y:=0).
        auto. apply Qmult_le_0_compat. apply Qlt_le_weak. auto.
        rewrite (Qmake_Qdiv 1 2).
        apply Qle_shift_div_l. reflexivity.
        rewrite Qmult_0_l. apply Qlt_le_weak. reflexivity. }
    * destruct H1. ** right. left. split.
      + auto.
      + unfold Cut_multNP, Cut_opp.
        assert(0 <= x\/~0 <= x). apply classic.
        destruct H1, H2.
        { destruct H1, H1, H4. apply (Dedekind_properties2 _ H x).
          split. auto. rewrite Qplus_0_l.
          apply Qle_trans with (y:=0).
          rewrite <- (Qopp_involutive 0). apply Qopp_le_compat.
          apply Qlt_le_weak. auto.
          auto. }
        { apply Qnot_le_lt in H2. destruct H1.
          assert(exists x1 : Q, A x1 /\ x < x1).
          { apply (Dedekind_properties3 _ H). auto. }
          destruct H4, H4.
          exists (x1 - x). split. { unfold Qminus.
          rewrite <- (Qlt_minus_iff x x1). auto. }
          unfold not. intros.
          destruct H6, H6, H6, H7, H8, H8, H8, H9.
          unfold Qminus in *. rewrite Qplus_opp_assoc in H11.
          rewrite Qplus_assoc in H11. rewrite Qplus_comm in H11.
          rewrite Qplus_assoc in H11. rewrite Qopp_involutive in H11.
          rewrite Qplus_opp_r in H11. rewrite Qplus_0_l in H11.
          apply Qle_not_lt in H11. apply H11.
          apply Qlt_trans with (y:=(x2)).
          { rewrite <- (Qmult_1_r x2).
            rewrite <- Qmult_assoc. rewrite Qmult_lt_l with (z:=x2).
            { rewrite Qmult_1_l. auto. } auto. }
          assert(Cut_opp A x2). { exists x4. repeat split; auto. }
          assert(~ Cut_opp A (-x1)). { apply Cut_cut_opp_not. auto. auto. }
          apply (Dedekind_le (Cut_opp A)). apply Dedekind_opp. auto. auto. auto. }
   ** destruct H1. *** destruct H1. right. right. left.
        repeat split; auto. destruct H2, H2, H3.
        rewrite Qplus_0_l. apply Qlt_trans with (y:=0).
        + rewrite Qlt_minus_iff. rewrite Qopp_involutive.
          rewrite Qplus_0_l. auto.
        + reflexivity.
  *** destruct H1. **** destruct H1. right. right. right. left.
        repeat split; auto. destruct H2, H2, H3.
        rewrite Qplus_0_l. apply Qlt_trans with (y:=0).
        + rewrite Qlt_minus_iff. rewrite Qopp_involutive.
          rewrite Qplus_0_l. auto.
        + reflexivity.
 **** destruct H1.
      + repeat right. split. { left. auto. }
        unfold Cut_mult0. destruct H1. apply (Dedekind_le A).
        auto. auto. auto.
      + destruct H1. destruct H1. reflexivity.
Qed.

Theorem Rmult_comm : forall a b : Real, (a * b == b * a)%R.
Proof.
  intros. destruct a, b. unfold Req, Rle, Rmult. split.
  - intros. apply Cut_mult_comm. auto.
  - intros. apply Cut_mult_comm. auto.
Qed.

Lemma Rmult_opp_l : forall a b : Real, (- (a * b) == - a * b)%R.
Proof.
  intros. rewrite -> Rmult_comm. rewrite -> (Rmult_comm (-a)%R).
  apply Rmult_opp_r.
Qed.

Theorem Rmult_0_l : forall a : Real, (Rzero * a == Rzero)%R.
Proof.
  intros. rewrite Rmult_comm. apply Rmult_0_r.
Qed.

Theorem Rmult_1_l : forall a : Real, (Rone * a == a)%R.
Proof.
  intros. rewrite Rmult_comm. apply Rmult_1_r.
Qed.

Theorem Rmult_assoc_lemma : forall a b c : Real, (a * b * c <= a * (b * c))%R.
Proof.
  intros. unfold Req, Rmult, Rle. destruct a, b, c.
    intros. apply Cut_mult_assoc;auto.
Qed.

Theorem Rmult_assoc : forall a b c : Real, (a * b * c == a * (b * c))%R.
Proof.
  intros. split.
  - apply Rmult_assoc_lemma.
  - intros. rewrite Rmult_comm.
    apply Rle_trans with (y:=(b*(c*a))%R);try apply Rmult_assoc_lemma.
    rewrite (Rmult_comm (a*b)%R c). rewrite Rmult_comm.
    apply Rle_trans with (y:=(c*(a*b))%R);try apply Rmult_assoc_lemma.
    apply Rle_refl.
Qed.

Lemma Dedekind_up : forall (A : Q -> Prop)(x1 x2:Q), Dedekind A ->
  A x1 -> A x2 -> exists x : Q, A x /\ x1<x /\ x2<x.
Proof.
  intros. apply (Dedekind_properties3 _ H) in H0.
  apply (Dedekind_properties3 _ H) in H1. destruct H0, H0, H1, H1.
  assert (x0 > x\/~x0 > x). apply classic. destruct H4.
  - exists x0. repeat split;auto.
    apply Qlt_trans with (y:=x);auto.
  - apply Qnot_lt_le in H4. exists x. repeat split;auto.
    apply Qlt_le_trans with (y:=x0);auto.
Qed.

(* Lemma distr_lemma1 : forall (A B : Q -> Prop), Dedekind A -> Dedekind B -> 
 forall x2, (B x2 -> exists x1 : Q, A x1/\
  Cut_mult A B (x1*x2)).
Proof.
Admitted. (*wrong*) *)

Lemma Cut_mult_distr_PP :
  forall (A B C : Q -> Prop)(x : Q)(DA : Dedekind A)(DB: Dedekind B)(DC:Dedekind C),
   A 0 -> B 0 -> C 0 ->
  Cut_mult A (Cut_plus_Cut B C) x <-> Cut_plus_Cut (Cut_mult A B) (Cut_mult A C) x
.
Proof.
  intros. split.
  - intros.
  destruct H2 as [?|[?|[?|[]]]].
  + destruct H2, H2, H4, H4, H3, H3.
    destruct H4 as [?[]]. destruct H3 as [?[?[?[]]]].
    destruct H9, H9. destruct H9 as [?[]].
  assert(H':Dedekind (Cut_plus_Cut (Cut_mult A B) (Cut_mult A C))).
  { apply Dedekind_plus; apply Dedekind_mult;auto. }
    pose proof (Dedekind_up B 0 x4). destruct H13;auto. destruct H13 as [?[]].
    pose proof (Dedekind_up C 0 x5). destruct H16;auto. destruct H16 as [?[]].
    apply (Dedekind_properties2 _ H' (x2*(x6+x7)));split;
    try apply Qle_trans with (y:=x2*x3);auto;try apply Qlt_le_weak;
    try apply Qmult_lt_l;auto;try rewrite <- H12;try apply Qplus_lt_le_compat;
    try apply Qlt_le_weak;auto.
    exists (x2*x6), (x2*x7).
    repeat split;try rewrite <- H12;try rewrite Qmult_plus_distr_r;try reflexivity;
    left;repeat split;auto.
    * exists x2, x6. repeat split;auto;apply Qle_refl.
    * exists x2, x7. repeat split;auto;apply Qle_refl.
  + destruct H2, H2. apply (Cut_cut_opp_not A 0) in H;auto;
    destruct H;auto.
  + destruct H2, H2, H4, H4, H5. exists 0, (-x0). repeat split;auto.
    apply (Dedekind_properties2 _ DC 0);split;auto.
    rewrite Qopp_le_compat_iff. rewrite Qopp_involutive;apply Qlt_le_weak;auto.
  + destruct H2, H2. apply (Cut_cut_opp_not A 0) in H;auto;
    destruct H;auto.
  + destruct H2, H2, H2, H2;auto. exists 0, 0. repeat split;auto.
  - intros. destruct H2, H2. destruct H2 as [?[]].
    pose proof (Cut_cut_opp_not A 0 DA H). rename H5 into AN.
    pose proof (Cut_cut_opp_not C 0 DC H1). rename H5 into CN.
    pose proof (Cut_cut_opp_not B 0 DB H0). rename H5 into BN.
    destruct H2 as [?|[?|[?|[]]]].
  + destruct H2, H5, H5. destruct H5 as [?[?[?[]]]].
    destruct H3 as [?|[?|[?|[]]]].
  { destruct H3, H10, H10.
    destruct H10 as [?[?[?[]]]].
    left. pose proof (Dedekind_plus B C DB DC). repeat split;auto.
    { apply (Dedekind_properties2 _ H15 (x3+x5)). split.
    { exists x3, x5. repeat split;auto. } 
    { apply Qlt_le_weak. rewrite <- Qplus_0_r.
      apply Qplus_lt_le_compat;auto;apply Qlt_le_weak;auto. } }
    pose proof (Dedekind_up A x2 x4 DA H7 H12). destruct H16 as [?[?[]]].
    exists x6, (x3+x5). repeat split.
  * apply Qlt_trans with (y:=x2);auto.
  * rewrite <- Qplus_0_r.
    apply Qplus_lt_le_compat;auto;apply Qlt_le_weak;auto.
  * auto.
  * exists x3,x5. repeat split;auto.
  * rewrite <- H4. rewrite Qmult_plus_distr_r. apply Qplus_le_compat.
    { apply Qle_trans with (y:=x2*x3);auto;apply Qmult_le_compat_r;
      apply Qlt_le_weak;auto. }
    { apply Qle_trans with (y:=x4*x5);auto;apply Qmult_le_compat_r;
      apply Qlt_le_weak;auto. } }
  { destruct H3, H3, AN;auto. }
  { destruct H3, H3, CN;auto. }
  { destruct H3, H3, AN;auto. }
  { destruct H3, H3, H3, H3;auto. }
  + destruct H2, H2, AN;auto.
  + destruct H2, H2, BN;auto.
  + destruct H2, H2, AN;auto.
  + destruct H2, H2, H2, H2;auto.
Qed.

Lemma Rover0 : forall (A : Q -> Prop) (H:Dedekind A),
  (Rzero < Real_cons A H)%R -> A 0.
Proof.
  intros. destruct H0, H1, H1.
  apply ( Dedekind_properties2 _ H x). split;auto.
  apply Qnot_lt_le;auto.
Qed.

Lemma not_imply_to_or : forall P Q : Prop, ~(P->Q)->P/\~Q.
Proof.
  intros. split.
  - pose proof classic P. destruct H0.
    + auto.
    + destruct H. intros. destruct H0. auto.
  - hnf. intros. auto.
Qed.

Theorem Dedekind_lt_bin : forall (A B : Q -> Prop)(x : Q),Dedekind A ->
Dedekind B -> A x -> ~ B x -> (forall x1 : Q, B x1 -> A x1).
Proof.
  intros. apply (Dedekind_properties2 _ _ x).
  pose proof Dedekind_le B x x1 H0 H2 H3. apply Qlt_le_weak in H4. auto.
Qed.

Theorem Rplus_lt_r: forall x y z : Real, (z + x < z + y <-> x < y)%R.
Proof.
  intros.
  destruct x, y, z. hnf. split.
  - intros. hnf in *. destruct H2, H3, H3. split.
    + rewrite <- (not_exists_not_dist Q) in *. hnf.
      intros. destruct H4, H5. destruct H3 as [?[?[?[]]]].
      apply not_imply_to_or in H4. destruct H4.
      exists x1, x2. repeat split;auto.
      apply (Dedekind_lt_bin A A0 x0);auto.
    + apply not_all_not_ex. hnf in *. intros. destruct H4.
      destruct H3 as [?[?[?[]]]].
      pose proof H5 x1. apply not_and_or in H7. destruct H7.
      * destruct H7;auto.
      * apply NNPP in H7. exists x0, x1. auto.
  - intros. hnf in *. destruct H2, H3, H3. split.
    + intros. destruct H5 as [?[?[?[]]]]. exists x1, x2;auto.
    + destruct (Dedekind_properties1 _ H1), H5.
      apply (Dedekind_properties3 _ H0) in H3. destruct H3, H3.
      pose proof Dedekind1_strong A1 H1 (x1 - x). destruct H8.
      { unfold Qminus. rewrite <- Qlt_minus_iff. auto. }
      destruct H8. exists (x2+x1). split.
      * exists x2, x1. repeat split;auto.
      * hnf. intros. destruct H10 as [?[?[?[]]]].
        pose proof Dedekind_le A1 (x2+(x1-x)) x3 H1 H9 H10.
        unfold Qminus in *. rewrite Qplus_assoc in H13. rewrite <- H12 in H13.
        rewrite <- Qplus_lt_l with (z:=x) in H13. rewrite <- Qplus_assoc in H13.
        rewrite (Qplus_comm (-x) x) in H13. rewrite Qplus_opp_r in H13.
        rewrite Qplus_0_r in H13. rewrite Qplus_lt_r with (z:=x3) in H13.
        pose proof Dedekind_le A x x4 H H4 H11.
        apply Qlt_not_le in H13. destruct H13. apply Qlt_le_weak;auto.
Qed.

Theorem Rplus_lt_l: forall x y z : Real, (x + z < y + z <-> x < y)%R.
Proof.
  intros. rewrite Rplus_comm. rewrite (Rplus_comm y z). apply Rplus_lt_r.
Qed.

Theorem Rplus_0_l : forall a : Real, (Rzero + a == a)%R.
Proof.
  intros. rewrite Rplus_comm. apply Rplus_0_r.
Qed.

Theorem Ropp_lt_compat: forall p q : Real, (p < q -> - q < - p)%R.
Proof.
  intros. rewrite <- Rplus_lt_r with (z:=p). rewrite Rplus_opp.
  rewrite <- Rplus_lt_l with (z:=q). rewrite Rplus_assoc.
  rewrite (Rplus_comm (-q) q)%R. rewrite Rplus_opp.
  rewrite Rplus_0_r. rewrite Rplus_0_l. auto.
Qed.

Theorem Rle_lt_eq : forall x y : Real, (x <= y <-> (x == y\/x<y))%R.
Proof.
  intros. assert(x<y\/~x<y)%R. apply classic. split.
  - destruct H.
    + auto.
    + apply Rnot_lt_le in H.
      left. apply Rle_antisym;auto.
  - intros. destruct H0.
    + rewrite H0. apply Rle_refl.
    + apply Rlt_le_weak;auto.
Qed.

Theorem Rplus_le_r: forall x y z : Real, (z + x <= z + y <-> x <= y)%R.
Proof.
  intros. rewrite Rle_lt_eq. rewrite Rle_lt_eq. split.
  - intros. destruct H.
    + left. apply (Rplus_compat_l z);auto.
    + right. rewrite <- Rplus_lt_r. apply H.
  - intros. destruct H.
    + rewrite H. left. reflexivity.
    + right. rewrite Rplus_lt_r. auto.
Qed.

Theorem Rplus_inj_r: forall x y z : Real, (x + z == y + z <-> x == y)%R.
Proof.
  intros. split.
  - rewrite Rplus_comm. rewrite (Rplus_comm y z). apply Rplus_compat_l.
  - intros. rewrite H. reflexivity.
Qed.

Theorem Rplus_inj_l: forall x y z : Real, (z + x == z + y <-> x == y)%R.
Proof.
  intros. rewrite Rplus_comm. rewrite (Rplus_comm z y).
  apply Rplus_inj_r.
Qed.

Theorem Rplus_le_l: forall x y z : Real, (x + z <= y + z <-> x <= y)%R.
Proof.
  intros. rewrite Rplus_comm. rewrite (Rplus_comm y z).
  apply Rplus_le_r.
Qed.

Theorem R_three_dis : forall x y : Real, (x<y\/x==y\/y<x)%R.
Proof.
  intros. pose proof classic (x<y)%R. destruct H.
  - auto.
  - pose proof classic (y<x)%R. destruct H0.
    + auto.
    + apply Rnot_lt_le in H. apply Rnot_lt_le in H0.
      right. left. split;auto.
Qed.

Lemma Rplus_opp_bin : forall b c : Real, (Rzero == b + c -> (-b) == c)%R.
Proof.
  intros. rewrite <- Rplus_inj_l with (z:=b). rewrite Rplus_opp. auto.
Qed.

Lemma Rmult_distr_l_PPP : forall a b c : Real, (Rzero < a)%R -> (Rzero < b)%R -> 
  (Rzero < c)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros.
  destruct a, b, c.
  pose proof (Rover0 A H2 H).
  pose proof (Rover0 A0 H3 H0).
  pose proof (Rover0 A1 H4 H1).
  hnf;split;hnf;intros.
  - apply Cut_mult_distr_PP;auto.
  - apply Cut_mult_distr_PP;auto.
Qed.

Lemma Rmult_distr_l_PPE : forall a b c : Real, (Rzero < a)%R -> (Rzero < b)%R -> 
  (Rzero == c)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros. rewrite <- H1. rewrite Rmult_0_r. rewrite Rplus_0_r.
  rewrite Rplus_0_r. reflexivity.
Qed.

Lemma Rmult_distr_l_PNP : forall a b c : Real, (Rzero < a)%R -> (b < Rzero)%R -> 
 (Rzero < b + c)%R -> (Rzero < c)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros. assert(c == b + c - b)%R. { unfold Rminus.
  rewrite Rplus_comm. rewrite <- Rplus_assoc.
  rewrite (Rplus_comm (-b)%R b). rewrite Rplus_opp.
  rewrite Rplus_comm. rewrite Rplus_0_r. reflexivity. }
  rewrite H3. rewrite (Rmult_distr_l_PPP a (b+c)(-b))%R;auto.
  - rewrite <- Rmult_opp_r.
    rewrite (Rplus_comm (a*b) (a * (b + c) + - (a * b)))%R.
    rewrite Rplus_assoc. rewrite (Rplus_comm (-(a*b)) (a*b))%R.
    rewrite Rplus_opp. rewrite Rplus_0_r. rewrite <- H3. reflexivity.
  - rewrite <- Rplus_lt_r with (z:=b). rewrite Rplus_0_r.
    rewrite Rplus_opp. auto.
Qed.

Lemma Rmult_distr_l_PPN : forall a b c : Real, (Rzero < a)%R -> (Rzero < b)%R -> 
 (Rzero < b + c)%R -> (c < Rzero)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros. assert(b == b + c - c)%R. { unfold Rminus.
  rewrite -> Rplus_assoc. rewrite Rplus_opp.
  rewrite Rplus_0_r. reflexivity. }
  rewrite H3. rewrite (Rmult_distr_l_PPP a (b+c)(-c))%R;auto.
  - rewrite <- Rmult_opp_r.
    rewrite Rplus_assoc. rewrite (Rplus_comm (-(a*c)) (a*c))%R.
    rewrite Rplus_opp. rewrite Rplus_0_r. rewrite <- H3. reflexivity.
  - rewrite <- Rplus_lt_r with (z:=c). rewrite Rplus_0_r.
    rewrite Rplus_opp. auto.
Qed.

Lemma Rmult_distr_l_PNN : forall a b c : Real, (Rzero < a)%R -> (b < Rzero)%R -> 
 (c < Rzero)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros.
  apply Ropp_lt_compat in H0. rewrite <- Rzero_opp in H0.
  apply Ropp_lt_compat in H1. rewrite <- Rzero_opp in H1.
  rewrite (Ropp_opp b). rewrite (Ropp_opp c).
  rewrite <- Rmult_opp_r. rewrite <- (Rmult_opp_r a (- c))%R.
  rewrite <- Rplus_inj_l with (z:=(a*-b)%R).
  rewrite <- Rplus_assoc. rewrite Rplus_opp. rewrite Rplus_0_l.
  rewrite <- Rplus_inj_l with (z:=(a*-c)%R).
  rewrite <- Rplus_assoc. rewrite Rplus_opp.
  rewrite <- Rmult_distr_l_PPP;auto.
  assert(--b+--c==-(-b+-c))%R.
  { rewrite <- Rplus_inj_l with (z:=(-b+-c)%R). rewrite Rplus_opp.
    rewrite Rplus_assoc. rewrite (Rplus_comm (--b)%R).
    rewrite <- (Rplus_assoc (-c)%R). rewrite Rplus_opp.
    rewrite Rplus_0_l. rewrite Rplus_opp. reflexivity. }
  rewrite H2. rewrite <- Rmult_opp_r. rewrite (Rplus_comm (-c)%R).
  rewrite Rplus_opp. reflexivity.
Qed.

Lemma Rplus_opp_plus : forall a b : Real, (-(a+b)==-a+-b)%R.
Proof.
  intros. rewrite <- Rplus_inj_l with (z:=(a+b)%R). rewrite Rplus_opp.
    rewrite Rplus_assoc. rewrite (Rplus_comm (b)%R).
    rewrite (Rplus_assoc (-a)%R). rewrite (Rplus_comm (-b))%R.
    rewrite Rplus_opp. rewrite Rplus_0_r. rewrite Rplus_opp. reflexivity.
Qed.

Lemma Rmult_distr_l_NPP : forall a b c : Real, (a < Rzero)%R -> (Rzero < b)%R -> 
  (Rzero < c)%R -> (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros. apply Ropp_lt_compat in H. rewrite <- Rzero_opp in H.
  rewrite (Ropp_opp a). rewrite <- (Rmult_opp_l (-a)%R).
  rewrite <- (Rmult_opp_l (-a)%R). rewrite <- (Rmult_opp_l (-a)%R).
  rewrite Rmult_distr_l_PPP;auto. rewrite Rplus_opp_plus.
  reflexivity.
Qed.

Theorem Rmult_distr_l :
  forall a b c : Real, (a * (b + c) == (a * b) + (a * c))%R.
Proof.
  intros.
  pose proof R_three_dis Rzero a.
  pose proof R_three_dis Rzero b.
  pose proof R_three_dis Rzero c.
  destruct H as [?|[]];destruct H0 as [?|[]];destruct H1 as [?|[]];
  try rewrite <- H;try rewrite Rmult_0_l;try rewrite Rmult_0_l;
    try rewrite Rmult_0_l;try rewrite Rplus_0_r;try reflexivity;
 try rewrite <- H0;try rewrite Rmult_0_r;try rewrite Rplus_0_l;
   try rewrite Rplus_0_l;try reflexivity;
 try rewrite <- H1;try rewrite Rmult_0_r;try rewrite Rplus_0_r;
   try rewrite Rplus_0_r;try reflexivity.
  - apply Rmult_distr_l_PPP;auto.
  - pose proof R_three_dis Rzero (b+c)%R. destruct H2 as [?|[]].
    + apply Rmult_distr_l_PPN;auto.
    + rewrite <- H2. apply Rplus_opp_bin in H2.
      rewrite <- H2. rewrite <- Rmult_opp_r. rewrite Rplus_opp.
      apply Rmult_0_r.
    + assert(c == b + c - b)%R. { unfold Rminus.
      rewrite Rplus_comm. rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-b)%R b). rewrite Rplus_opp.
      rewrite Rplus_comm. rewrite Rplus_0_r. reflexivity. }
      rewrite H3. unfold Rminus.
      apply Ropp_lt_compat in H0. rewrite <- Rzero_opp in H0.
      rewrite (Rmult_distr_l_PNN a (b+c))%R;auto.
      rewrite Rplus_comm with (b:=(a*-b)%R).
      rewrite <- Rmult_opp_r. rewrite <- Rplus_assoc with (a:=(a*b)%R).
      rewrite Rplus_opp. rewrite Rplus_0_l.
      rewrite <- H3. reflexivity.
  - pose proof R_three_dis Rzero (b+c)%R. destruct H2 as [?|[]].
    + apply Rmult_distr_l_PNP;auto.
    + rewrite <- H2. apply Rplus_opp_bin in H2.
      rewrite <- H2. rewrite <- Rmult_opp_r. rewrite Rplus_opp.
      apply Rmult_0_r.
    + rewrite Rplus_comm in *. rewrite (Rplus_comm (a*b)%R).
      assert(b == c + b - c)%R. { unfold Rminus.
      rewrite Rplus_comm. rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-c)%R c). rewrite Rplus_opp.
      rewrite Rplus_comm. rewrite Rplus_0_r. reflexivity. }
      rewrite H3. unfold Rminus.
      apply Ropp_lt_compat in H1. rewrite <- Rzero_opp in H1.
      rewrite (Rmult_distr_l_PNN a (c+b))%R;auto.
      rewrite Rplus_comm with (b:=(a*-c)%R).
      rewrite <- Rmult_opp_r. rewrite <- Rplus_assoc with (a:=(a*c)%R).
      rewrite Rplus_opp. rewrite Rplus_0_l.
      rewrite <- H3. reflexivity.
  - apply Rmult_distr_l_PNN;auto.
  - apply Rmult_distr_l_NPP;auto.
  - apply Ropp_lt_compat in H. rewrite <- Rzero_opp in H.
    rewrite Rplus_comm in *. rewrite (Rplus_comm (a*b)%R).
    rewrite (Ropp_opp a). rewrite <- (Rmult_opp_l (-a)%R).
    rewrite <- (Rmult_opp_l (-a)%R). rewrite <- (Rmult_opp_l (-a)%R).
    pose proof R_three_dis Rzero (c+b)%R. destruct H2 as [?|[]].
    + rewrite Rmult_distr_l_PNP;auto.
      rewrite Rplus_opp_plus. reflexivity.
    + rewrite <- H2. apply Rplus_opp_bin in H2.
      rewrite <- H2. rewrite <- Rmult_opp_r. rewrite Rplus_opp.
      rewrite Rmult_0_r. rewrite <- Rzero_opp. reflexivity.
    + rewrite (Rplus_comm (-(-a*c))%R).
      assert(b == c + b - c)%R. { unfold Rminus.
      rewrite Rplus_comm. rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-c)%R c). rewrite Rplus_opp.
      rewrite Rplus_comm. rewrite Rplus_0_r. reflexivity. }
      rewrite H3. unfold Rminus.
      apply Ropp_lt_compat in H1. rewrite <- Rzero_opp in H1.
      rewrite (Rmult_distr_l_PNP (-a) (c+b))%R;auto.
      rewrite Rplus_opp_plus. rewrite (Rmult_opp_r (-a) (-c))%R.
      rewrite <- Ropp_opp.
      rewrite Rplus_assoc with (b:=(-a*c)%R). rewrite Rplus_opp.
      rewrite Rplus_0_r.
      rewrite <- H3. reflexivity.
      rewrite <- H3. auto.
  - apply Ropp_lt_compat in H. rewrite <- Rzero_opp in H.
    rewrite (Ropp_opp a). rewrite <- (Rmult_opp_l (-a)%R).
    rewrite <- (Rmult_opp_l (-a)%R). rewrite <- (Rmult_opp_l (-a)%R).
    pose proof R_three_dis Rzero (b+c)%R. destruct H2 as [?|[]].
    + rewrite Rmult_distr_l_PNP;auto.
      rewrite Rplus_opp_plus. reflexivity.
    + rewrite <- H2. apply Rplus_opp_bin in H2.
      rewrite <- H2. rewrite <- Rmult_opp_r. rewrite Rplus_opp.
      rewrite Rmult_0_r. rewrite <- Rzero_opp. reflexivity.
    + rewrite (Rplus_comm (-(-a*b))%R).
      assert(c == b + c - b)%R. { unfold Rminus.
      rewrite Rplus_comm. rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-b)%R b). rewrite Rplus_opp.
      rewrite Rplus_comm. rewrite Rplus_0_r. reflexivity. }
      rewrite H3. unfold Rminus.
      apply Ropp_lt_compat in H0. rewrite <- Rzero_opp in H0.
      rewrite (Rmult_distr_l_PNP (-a) (b+c))%R;auto.
      rewrite Rplus_opp_plus. rewrite (Rmult_opp_r (-a) (-b))%R.
      rewrite <- Ropp_opp.
      rewrite Rplus_assoc with (b:=(-a*b)%R). rewrite Rplus_opp.
      rewrite Rplus_0_r.
      rewrite <- H3. reflexivity.
      rewrite <- H3. auto.
  - apply Ropp_lt_compat in H. rewrite <- Rzero_opp in H.
    apply Ropp_lt_compat in H0. rewrite <- Rzero_opp in H0.
    apply Ropp_lt_compat in H1. rewrite <- Rzero_opp in H1.
    rewrite (Ropp_opp a). rewrite <- (Rmult_opp_l (-a)%R).
    rewrite <- (Rmult_opp_l (-a)%R). rewrite <- (Rmult_opp_l (-a)%R).
    rewrite Rmult_opp_r. rewrite Rmult_opp_r. rewrite Rmult_opp_r.
    rewrite Rplus_opp_plus. apply Rmult_distr_l_PPP;auto.
Qed.

Theorem Rmult_distr_r :
  forall a b c : Real, ((b + c) * a == (b * a) + (c * a))%R.
Proof.
  intros. rewrite Rmult_comm. rewrite (Rmult_comm b).
  rewrite (Rmult_comm c). apply Rmult_distr_l.
Qed.

Definition Cut_inv (A : Q -> Prop) : Q -> Prop :=
  (fun x => (A 0 /\ (x <= 0 \/ exists r : Q, (r > 0 /\ ~ (A (/x + -r)))))
           \/ (Cut_opp A 0 /\ x < 0 /\ exists r : Q, (r > 0 /\ ~ (A (/x + -r))))
           \/ (~ A 0 /\ ~ Cut_opp A 0/\ False ))
.

Theorem Dedekind_inv : forall A : Q -> Prop , Dedekind A -> Dedekind (Cut_inv A).
Proof.
  intros.
  assert(HA:A 0 \/ Cut_opp A 0 \/ (~ A 0/\~ Cut_opp A 0)).
  { apply Cut_mult_situation1. }
  destruct HA as [?|[]].
{ split.
  - split.
    + destruct (Dedekind_properties1 _ H), H2.
      exists (/x). left;split;auto.
Search Qinv. hnf.
Admitted.

Definition Rinv (a : Real) : Real :=
  match a with
    | Real_cons A HA => Real_cons (Cut_inv A) (Dedekind_inv A HA)
  end.

Theorem Rmult_inv :
  forall a : Real, (a <> Rzero) -> (a * Rinv a == Rone)%R.
Proof.
Admitted.

