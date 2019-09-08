Set Warnings "-notation-overridden,-parsing".
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.omega.Omega.

Section Def1.

Context {A B: Type}.
Context (eqA: relation A).
Context (eqB: relation B).

Definition image_defined (R: A -> B -> Prop): Prop :=
  forall a, exists b, R a b.

Definition partial_functional (R: A -> B -> Prop): Prop :=
  forall a b1 b2, R a b1 -> R a b2 -> eqB b1 b2.

Definition injective (R: A -> B -> Prop): Prop :=
  forall a1 a2 b, R a1 b -> R a2 b -> eqA a1 a2.

Definition surjective (R: A -> B -> Prop): Prop :=
  forall b, exists a, R a b.

Definition function_injective (f: A -> B): Prop :=
  forall a1 a2, eqB (f a1) (f a2) -> eqA a1 a2.

Definition function_surjective (f: A -> B): Prop :=
  forall b, exists a, eqB (f a) b.

Definition is_function (f: A -> B -> Prop) : Prop :=
  image_defined f /\ partial_functional f /\ Proper (eqA ==> eqB ==> iff) f.
  
End Def1.

Section Def2.

Context {A B: Type}.

Record injection (eqA: relation A) (eqB: relation B): Type := {
  inj_R:> A -> B -> Prop;
  wd_inj: Proper (eqA ==> eqB ==> iff) inj_R;
  im_inj: image_defined inj_R;
  pf_inj: partial_functional eqB inj_R;
  in_inj: injective eqA inj_R
}.

Record surjection (eqA: relation A) (eqB: relation B): Type := {
  surj_R:> A -> B -> Prop;
  wd_surj: Proper (eqA ==> eqB ==> iff) surj_R;
  im_surj: image_defined surj_R;
  pf_surj: partial_functional eqB surj_R;
  su_surj: surjective surj_R
}.

Record bijection (eqA: relation A) (eqB: relation B): Type := {
  bij_R:> A -> B -> Prop;
  wd_bij: Proper (eqA ==> eqB ==> iff) bij_R;
  im_bij: image_defined bij_R;
  pf_bij: partial_functional eqB bij_R;
  in_bij: injective eqA bij_R;
  su_bij: surjective bij_R
}.

Existing Instances wd_inj wd_surj wd_bij.

End Def2.

Section Construction.

Context {A B: Type}.
Context {eqA: relation A}.
Context {eqB: relation B}.
Context {equA: Equivalence eqA}.
Context {equB: Equivalence eqB}.

Program Definition FBuild_injection
        (f: A -> B)
        (H: function_injective eqA eqB f)
        (H0: Proper (eqA ==> eqB) f): injection eqA eqB :=
  Build_injection _ _ (fun a b => eqB (f a) b) _ _ _ _.
Next Obligation.
  hnf ; red ; intros.
  rewrite H1. rewrite H2. reflexivity.
Defined.
Next Obligation.
  hnf ; intros.
  exists (f a). reflexivity.
Defined.
Next Obligation.
  hnf ; intros.
  rewrite <- H1. auto.
Defined.
Next Obligation.
  hnf ; intros.
  apply H. rewrite H2. auto. 
Defined.

Program Definition FBuild_surjection
        (f: A -> B)
        (H: function_surjective eqB f)
        (H0: Proper (eqA ==> eqB) f): surjection eqA eqB :=
  Build_surjection _ _ (fun a b => eqB (f a) b) _ _ _ _.
Next Obligation.
  hnf ; red ; intros.
  rewrite H1. rewrite H2. reflexivity.
Defined.
Next Obligation.
  intro.
  exists (f a). reflexivity.
Defined.
Next Obligation.
  hnf. intros.
  rewrite <- H1. auto.
Defined.

Program Definition FBuild_bijection
           (f: A -> B)
           (H: function_injective eqA eqB f)
           (H0: function_surjective eqB f)
           (H1: Proper (eqA ==> eqB) f): bijection eqA eqB :=
  Build_bijection _ _ (fun a b => eqB (f a) b) _ _ _ _ _.
Next Obligation.
  hnf ; red ; intros.
  rewrite H2. rewrite H3.
  reflexivity.
Defined.
Next Obligation.
  intro.
  exists (f a). reflexivity.
Defined.
Next Obligation.
  hnf ; intros.
  rewrite <- H2. auto.
Defined.
Next Obligation.
  hnf ; intros.
  apply H. rewrite H3. auto. 
Defined.

Program Definition bijection_refl: bijection eqA eqA :=
  Build_bijection _ _ eqA _ _ _ _ _.
Next Obligation.
  intro.
  exists a. reflexivity.
Defined.
Next Obligation.
  hnf ; intros.
  rewrite <- H. auto.
Defined.
Next Obligation.
  hnf ; intros.
  rewrite H0. auto.
Defined.
Next Obligation.
  hnf ; intros.
  exists b. reflexivity.
Defined.

Program Definition bijection_sym (R: bijection eqA eqB): bijection eqB eqA :=
  Build_bijection _ _ (fun a b => R b a) _ _ _ _ _.
Next Obligation.
  hnf ; red ; intros.
  apply R ;  auto.
Defined.
Next Obligation.
  apply R.
Defined.
Next Obligation.
  hnf.  intros.
  destruct R. simpl in *.
  apply (in_bij0 _ _ a) ; auto.
Defined.
Next Obligation.
  hnf. intros.
  destruct R. simpl in *.
  apply (pf_bij0 b) ; auto.
Defined.

Definition bijection_injection (R: bijection eqA eqB): injection eqA eqB :=
  Build_injection _ _ R (wd_bij _ _ R) (im_bij _ _ R) (pf_bij _ _ R) (in_bij _ _ R).

Context {C: Type}.
Context (eqC: relation C).
Context {equC: Equivalence eqC}.

Program Definition injection_trans (R1: injection eqA eqB) (R2: injection eqB eqC): injection eqA eqC :=
  Build_injection _ _ (fun a c => exists b, R1 a b /\ R2 b c) _ _ _ _.
Next Obligation.
  apply R.
Defined.
Next Obligation.
  hnf ; red; intros.
  destruct R1 , R2 ; simpl in *.
  split ; intros ; destruct H1 ; exists x1 ; 
  rewrite H in * ; rewrite H0 in * ; auto.
Defined.
Next Obligation.
  intro.
  destruct R1 , R2 ; simpl in *.
  destruct (im_inj0 a).
  destruct (im_inj1 x).
  exists x0 , x. auto.
Defined.
Next Obligation.
  hnf ; intros.
  destruct H , H0.
  destruct R1 , R2 ; simpl in *.
  assert (eqB x x0). { apply (pf_inj0 a). apply H. apply H0. }
  rewrite H1 in *.
  apply (pf_inj1 x0). apply H. apply H0.
Defined.
Next Obligation.
  hnf ; intros.
  destruct H , H0.
  destruct R1 , R2 ; simpl in *.
  assert (eqB x x0). { apply (in_inj1 _ _ b). apply H. apply H0. }
  rewrite H1 in *.
  apply (in_inj0 _ _ x0). apply H. apply H0.
Defined.
End Construction.

Definition Countable (A: Type)(eqA : relation A) : Type := injection eqA (eq(A := nat)).

Lemma sur_inj : forall (A : Type)(eqA : relation A) , surjection (eq(A:=nat)) eqA -> injection eqA (eq(A:=nat)).
Proof.
  intros.
  set(fun (a : A)(n : nat) => X n a /\ (forall m : nat , X m a -> m >= n)).
  exists P ; subst P ; hnf in *; intros.
  - hnf. intros. repeat split ; intros ; destruct H1 ; subst.
    + destruct X.
      simpl in *. 
      assert (y0 = y0). { auto. }
      specialize (wd_surj0 y0 y0 H0).
      specialize (wd_surj0 x y H).
      apply wd_surj0. auto.
    + apply H3. destruct X.
      simpl in *.
      specialize (wd_surj0 m m).
      apply wd_surj0 with y; auto.
    + destruct X. simpl in *.
      specialize (wd_surj0 y0 y0).
      apply wd_surj0 with y; auto.
    + apply H3. destruct X.
      simpl in *.
      assert (m = m). { auto. }
      specialize (wd_surj0 m m H0).
      specialize (wd_surj0 x y H).
      apply wd_surj0. auto.
  - destruct (su_surj _ _ X a).
    set (fun (n : nat) => X n a).
    assert (forall n : nat , P n \/ ~ P n).
    { intros. apply classic. }
    assert (exists n : nat , P n). { exists x. auto. }
    pose proof (dec_inh_nat_subset_has_unique_least_element P H0 H1).
    repeat destruct H2.
    exists x0  ; auto. 
  - destruct H, H0.
    pose proof (H1 b2 H0).
    pose proof (H2 b1 H).
    omega.
  - destruct H, H0.
    destruct X.
    apply (pf_surj0 b) ; auto.
Qed.