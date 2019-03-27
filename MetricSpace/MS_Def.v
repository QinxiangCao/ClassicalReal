From Coq Require Import Init.Nat.
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

Class Metric (A : Type) (X : Type):={
    dist : A -> A -> X;
    HM_F :> Field X;
    HM_OF :> preOrderField X;
    HM1 : forall (p1 p2 : A), le x0 (dist p1 p2);
    HM2 : forall (p1 p2 : A), dist p1 p2 = dist p2 p1;
    HM3 : forall (p : A), dist p p = x0;
    HM4 : forall (p1 p2 p3 : A), le (dist p1 p3) (plus (dist p1 p2) (dist p2 p2));
}.
(** def of notations with clear meanings - B **)
Notation "x <= y" := (le x y): metric.
Local Open Scope metric.
Notation "| x , y |" := (dist x y) : metric.
Local Open Scope metric.
Notation "x + y" := (plus x y) : Field.
Local Open Scope Field.
(** Putting Type definitions in to type class arguments
are probably better. -- Qinxiang *)

(** Quote from Litao Zhou's well definition. - B **)
Class CauchySeq (A : Type) (X : Type) (M : Metric A X) (Cseq : nat -> A -> Prop):={
    HCseq1 : forall(n : nat), (exists (a : A), Cseq n a);
    HCseq2 : forall(m : nat) (a1 a2 : A), (a1 = a2) -> (Cseq m a1 <-> Cseq m a2);
    HCseq3 : forall(m : nat) (a1 a2 : A), Cseq m a1 -> Cseq m a2 -> (a1 = a2);
    HCA : forall (eps : X), le x0 eps
      -> (exists (N : nat), forall (m n:nat), (m > N)%nat /\ (n > N)%nat
            -> forall (a b : A), Cseq m a /\ Cseq n b
         -> (dist a b) <= eps);
}.

Class Converge (A : Type) (X : Type)  (M : Metric A X) (Seq : nat -> A -> Prop):={
    HC1 : forall(n : nat), (exists (a : A), Seq n a);
    HC2 : forall(m : nat) (a1 a2 : A), (a1 = a2) -> (Seq m a1 <-> Seq m a2);
    HC3 : forall(m : nat) (a1 a2 : A), Seq m a1 -> Seq m a2 -> (a1 = a2);
    HC : forall (eps : X), (exists (N : nat) (lim : A) , forall (n : nat) (a : A), (n > N)%nat -> Seq n a
      -> (dist a lim) <= eps);
}.

Inductive Cauchilize (A : Type) (X : Type) : Type :=
  | con_intro (Cseq : nat -> A  -> Prop) (M : Metric A X) (H : CauchySeq A X M Cseq) .

Definition A := Type.
Definition X := Type.
Definition H := Metric A X.

Definition equC {A X : Type} (x1 : Cauchilize A X) (x2 : Cauchilize A X) :  Prop  :=
  match x1,   x2 with
    | con_intro _ _ cseq1 M1 H1, con_intro _ _ cseq2 M2 H2 =>
        (forall (eps : X), x0 <= eps
             -> (exists (N : nat), forall (n :nat), (n > N)%nat
             -> forall (a1 a2 : A), cseq1 n a1  -> cseq2 n a2
             -> (dist a1 a2) <= eps))
  end.
Notation "a == b" := (equC a b)
    (at level 70, no associativity) : equC.
Definition leC {X : Type} (x1 : Cauchilize X X) (x2 : Cauchilize X X)  : Prop :=
    match x1,   x2 with
    | con_intro _ _ cseq1 _ _, con_intro _ _ cseq2 _ _ =>
        (exists (N  : nat), forall (n : nat), (n > N)%nat
            ->  forall (a1 a2 : X), cseq1 n a1  -> cseq2 n a2
             -> a1 <= a2)
    end.

Notation " x1 <= x2" := (leC x1 x2).
(** This notation seems fail to reload - B  **)

Definition siCauchilize : Type :=(Cauchilize A X).
Definition xsiCauchilize : Type :=(Cauchilize X X) .
Definition biCauchilize: Type := Cauchilize (Cauchilize A X) (Cauchilize X X).

Theorem preOrder_trans : forall (X : Type), preOrderField X ->
   preOrderField (Cauchilize X X).
Proof.
  Admitted.

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

