From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.RelationClasses.
(** def of preorder-field and metric space **)


Class preOrderField (X : Type) :={
    le : X -> X -> Prop;
    reflexivie : forall (x : X), le x x;
    HOF3 : forall (x y z : X), le x y -> le y z -> le x z;
}.
(** Maybe using notation to make code more readable. -- Qinxiang *)
Class Field  (X : Type)  :={
    x0 : X;
    plus : X -> X -> X;
    HF1 : forall (x y : X), plus x y = plus y x;
    HF2 : forall (x y z : X), plus (plus x y) z = plus x (plus y z);
    HF3 : forall (x : X), plus x0 x = x;
    HF4 : forall (x : X), (exists ix, plus x ix = x0);
}.

Class dense (X : Type) :={
    D_pO : preOrderField X;
    D : forall (x1 x2 : X), le x1 x2 -> (exists x3, le x1 x3 /\ le x3 x2);
}.

Class Metric (A : Type) (X : Type):={
    dist : A -> A -> X;
    HM_F :> Field X;
    HM_OF :> preOrderField X;
    HM1 : forall (p1 p2 : A), le x0 (dist p1 p2);
    HM2 : forall (p1 p2 : A), dist p1 p2 = dist p2 p1;
    HM3 : forall (p : A), dist p p = x0;
    HM4 : forall (p1 p2 p3 : A), le (dist p1 p3) (plus (dist p1 p2) (dist p2 p2));
}.
(** def of notations with clear meanings **)
Notation "x <= y" := (le x y): metric.
Notation " ( x , y ) " := (dist x y) : metric.
Local Open Scope metric.
Notation "x + y" := (plus x y) : Field.
(** Putting Type definitions in to type class arguments
are probably better. -- Qinxiang *)
Definition seq {A : Type} :=nat -> A -> Prop.

(** Quote from Litao Zhou's well definition. **)
Class CauchySeq (A : Type) (X : Type) (M : Metric A X) (Cseq : seq):={
    HCseq1 : forall(n : nat), (exists (a : A), Cseq n a);
    HCseq2 : forall(m : nat) (a1 a2 : A), (a1 = a2) -> (Cseq m a1 <-> Cseq m a2);
    HCseq3 : forall(m : nat) (a1 a2 : A), Cseq m a1 -> Cseq m a2 -> (a1 = a2);
    HCA : forall (eps : X), le x0 eps
      -> (exists (N : nat), forall (m n:nat), (N < m)%nat /\ (N < n)%nat
            -> forall (a b : A), Cseq m a /\ Cseq n b
         -> (dist a b) <= eps);
}.

Class Converge (A : Type) (X : Type)  (M : Metric A X) (Seq : seq):={
    HC1 : forall(n : nat), (exists (a : A), Seq n a);
    HC2 : forall(m : nat) (a1 a2 : A), (a1 = a2) -> (Seq m a1 <-> Seq m a2);
    HC3 : forall(m : nat) (a1 a2 : A), Seq m a1 -> Seq m a2 -> (a1 = a2);
    HC : forall (eps : X), (exists (N : nat) (lim : A) , forall (n : nat) (a : A), (N < n)%nat -> Seq n a
      -> (dist a lim) <= eps);
}.

Inductive Cauchilize {A X : Type}  {M : Metric A X}  : Type :=
  | con_intro (Cseq : seq)(H : CauchySeq A X M Cseq) .

Definition refl {A : Type} (reflseq : seq) (a : A) : Prop :=
  (forall (n : nat), reflseq n a) /\ (forall (a' : A) (n : nat) , a <> a' -> ~(reflseq n a')).


Theorem c_trans :
    forall {A X : Type} (M : Metric A X) (reflseq : seq) (a : A),refl reflseq a
      -> CauchySeq A X M reflseq.
Proof.
    intros. unfold refl in H. split. + intros. exists a. apply H.
  +split. intros. rewrite H0 in H1. apply H1. intros. rewrite H0. apply H1.
  +intros. assert(~(a <> a1)). {destruct H. unfold not in H2. unfold not.
    intros. assert(reflseq m a1 -> False). apply H2.  apply H3. apply H4, H0. }
    apply NNPP in H2.
    assert(~(a <> a2)). {destruct H. unfold not in H3. unfold not.
    intros. assert(reflseq m a2 -> False). apply H3.  apply H4. apply H5, H1. }
    apply NNPP in H3. rewrite  <-H2, H3. reflexivity.
  +intros. exists 0. intros. destruct H2, H. assert(~(a <> a0)). {
    unfold not in H4. unfold not. intros. apply H4 with (n := m) in H5.
    apply H5. apply H2. }
    apply NNPP in H5.
    assert(~(a <> b)). unfold not in H4. unfold not. intros. apply H4 with (n := n) in H6.
   apply H6. apply H3.     apply NNPP in H6.
    rewrite <-H6, <-H5. assert(dist a a  = x0). apply HM3. rewrite H7.
    apply H0.
Qed.

Definition A_ := Type.
Definition X_ := Type.

Definition ctr {A X : Type}  (M : Metric A X)  (a : A) (reflseq : seq) (H : refl reflseq a) : Cauchilize :=
    con_intro reflseq (c_trans M reflseq a H).

Definition equC {A X : Type} {M : Metric A X} (x1 x2 : @Cauchilize A X M):  Prop  :=
  match x1,   x2 with
    | con_intro cseq1 C1, con_intro cseq2 C2 =>
        (forall (eps : X), x0 <= eps
             -> (exists (N : nat), forall (n :nat), (N < n)%nat
             -> forall (a1 a2 : A), cseq1 n a1  -> cseq2 n a2
             -> (dist a1 a2) <= eps))
  end.
Notation "a == b" := (equC a b)
    (at level 70, no associativity) : equC.
Definition leC {X : Type} {M : Metric X X} (x1 x2 : @Cauchilize X X M) : Prop :=
    match x1,   x2 with
    | con_intro cseq1 C1, con_intro cseq2 C2 =>
        (exists (N: nat), forall (n : nat), (N < n)%nat
            ->  forall (a1 a2 : X), cseq1 n a1  -> cseq2 n a2
             -> a1 <= a2) \/ (equC x1 x2)
    end.

Notation " x1 <= x2" := (leC x1 x2).
(**
Definition siCauchilize : Type :=(@Cauchilize A_ X_ ).
Definition xsiCauchilize : Type :=(@Cauchilize X_ X_) .
Definition biCauchilize: Type := @Cauchilize (@Cauchilize A_ X_) (@Cauchilize X_ X_). **)

Lemma refl_equC : forall {A X : Type} {M : Metric A X} (x : @Cauchilize A X M), equC x x.
Proof.
  intros. unfold equC. destruct x. intros. inversion H. apply HCA0 in H0.
  destruct H0. exists x. intros. assert(x < n /\  x < n). split. apply H1. apply H1.
  apply H0 with (a := a1) (b := a2) in H4 . apply H4. split. apply H2. apply H3.
Qed.

Lemma le_one : forall (m n : nat), (m <= n)%nat \/ (n <= m)%nat.
Proof.
  intro m. induction m.
  -intros. left. induction n. apply le_n. apply le_S. apply IHn.
  -intros. destruct n. +right. apply le_0_n. +destruct IHm with (n := n).
  {left. apply le_n_S. auto. } {right. apply le_n_S. auto. }
Qed.

Lemma le_equ : forall (m n : nat), (m <= n)%nat -> (n <= m)%nat -> m = n.
Proof.
  intro m. induction m as [| m' IH]. -intros. destruct n. auto. inversion H0.
  -intros. destruct n. +inversion H. +apply le_S_n in H. apply le_S_n in H0.
    assert (m' = n). apply IH. apply H. apply H0. auto.
Qed.

Theorem preOrder_trans : forall {X : Type} {M : Metric X X}, preOrderField X ->
   preOrderField (@Cauchilize X X M).
Proof.
  intros. split with (le := leC). -intros. unfold leC. destruct x. right. apply refl_equC.
  -intros. unfold leC. destruct x. destruct y. destruct z. unfold leC in H, H0.
    destruct H. destruct H0. +left. destruct H. destruct H0. assert( (x1 <= x)%nat\/ (x <= x1)%nat ).
    apply le_one. destruct H4. exists x. intros. inversion H2. destruct HCseq4 with (n := n). apply H with (a2 := x2) in H6.
    apply H0 with (a1 := x2) in H7. {apply (HOF3 a1 x2 a2). apply H6. apply H7. }
    {assert(forall x y : nat, (x <= y)%nat -> x < y \/ x = y). intros. apply le_lt_or_eq. auto.
    -apply H9 in H4. destruct H4. + apply (lt_trans x1 x n).
    apply H4. apply H5. +rewrite H4. auto. }
    apply H8. apply H5. apply H8.
    exists x1. intros. inversion H2. destruct HCseq4 with (n := n). apply H with (a2 := x2) in H6.
    apply H0 with (a1 := x2) in H7. {apply (HOF3 a1 x2 a2). apply H6. apply H7. }
    apply H5. apply H8. assert(forall x y : nat, (x <= y)%nat -> x < y \/ x = y). intros. apply le_lt_or_eq. auto.
    apply H9 in H4. destruct H4. apply (lt_trans x x1 n).
    auto. auto. rewrite <-H4 in H5. auto. auto.

(** warning : stop running !**)

Theorem metric_trans : Metric A X -> Metric (Cauchilize A X) (Cauchilize X X) .
Proof.
  Admitted.




Theorem Cauchilized_x_can_be_divided_by_2 :
    forall (X : Type) (x : Cauchilize X X), (exists x1, leC (x1 + x1) x) .
Proof.
    Admitted.


Theorem Cauchy_seq_converge :
    forall (A X : Type) (seq : nat -> Cauchilize A X -> Prop) (M : Metric (Cauchilize A X) (Cauchilize X X)),
      Converge (Cauchilize A X) (Cauchilize X X) M seq
      <-> CauchySeq (Cauchilize A X) (Cauchilize X X) M seq.
Proof.
  split. -intros. inversion H0. split. +apply HC4.
    +apply HC5. +apply HC6.  +intros. destruct HC0 with (eps := eps ).
    exists x. intros. destruct H3. destruct H4. destruct H2.

