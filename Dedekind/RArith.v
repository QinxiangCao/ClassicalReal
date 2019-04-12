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

Instance Rplus_comp : Proper (Req ==> Req ==> Req) Rplus.
Proof.
  split ; destruct H; destruct H0; 
  destruct x ; destruct y;destruct x0;destruct y0;
  unfold Rle in * ; simpl in *;
  unfold Cut_plus_Cut in * ; simpl in *; intros ;
  repeat destruct H7 ; destruct H8; exists x0;exists x1; split; auto.
Qed.

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
  repeat rewrite Rplus_O_r in H.
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

Lemma Cut_multPP_spec: forall A B: Q -> Prop,
  A 0 -> B 0 ->
  (forall x, Cut_multPP A B x <-> Cut_mult A B x).
Proof.
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

Lemma Cut_mult_comm' : forall (A B : Q -> Prop) (x : Q),
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

Lemma Cut_mult_comm : forall (A B : Q -> Prop) (x : Q),
 Cut_mult A B x <-> Cut_mult B A x.
Proof.
  intros. split.
  - apply Cut_mult_comm'.
  - apply Cut_mult_comm'.
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

(** Third , we will define the plus operation of Set and Real
    and proof some theorem about it. *)
Theorem Rmult_0 : forall a : Real, (a * Rzero == Rzero)%R.
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

Theorem Rmult_1 : forall a : Real, (a * Rone == a)%R.
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

Theorem Rmult_assoc : forall a b c : Real, (a * b * c == a * (b * c))%R.
Proof.
Admitted.

Theorem Rmult_distr_l :
  forall a b c : Real, (a * (b + c) == (a * b) + (a * c))%R.
Proof.
Admitted.

Definition Cut_inv (A : Q -> Prop) : Q -> Prop :=
  (fun x => exists r : Q, (r > 0 /\ ~ (A (/x + -r))))
.

Theorem Dedekind_inv : forall A : Q -> Prop , Dedekind A -> Dedekind (Cut_inv A).
Proof.
Admitted.

Definition Rinv (a : Real) : Real :=
  match a with
    | Real_cons A HA => Real_cons (Cut_inv A) (Dedekind_inv A HA)
  end.

Theorem Rmult_inv :
  forall a : Real, (a <> Rzero) -> exists b, (a * b == Rone)%R.
Proof.
Admitted.

