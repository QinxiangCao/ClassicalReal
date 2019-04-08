From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Classical.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Classes.Equivalence.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Setoids.Setoid.

(** fund theorem**)
Theorem PNP : forall p : Prop, ~(p /\ ~p) .
Proof.
  unfold not. intros. destruct H. apply H0 in H. apply H.
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
(******************************************************************)
(** def of metric space**)
Parameter X : Type.
Parameter eq : relation X.
Parameter E : Equivalence eq.
Existing Instance E.

Class Pre_Order_Field {X : Type} (eq : relation X) :={
    le : relation X;
    pofr : forall(a b : X), eq a b -> le a b;
    poft : forall(a b c : X), le a b -> le b c -> le a c;
    poeq : forall (a b c d : X), eq a b -> eq c d -> le a c -> le b d;
}.
Notation "a <= b" := (le a b)
    (at level 70, no associativity).
Class Plus_Field {X : Type} (eq : relation X) :={
    plus : X -> X -> X; 
    x0 : X;
    pfc : forall (x y : X), eq (plus x y) (plus y x);
    pfa : forall (x y z : X), eq (plus (plus x y) z) (plus x (plus y z));
    pfz : forall (x : X), eq (plus x0 x) x;
    pfi : forall (x : X), (exists ix, eq (plus x ix) x0);
    pfeq : forall (a b c d : X), eq a b -> eq c d -> eq (plus a c) (plus b d);
}.
Notation "a + b" := (plus a b)
    (at level 50, left associativity).

Notation " x == y " := (eq x y)
  (at level 70 ,no associativity).
Notation " x != y " := (~eq x y)
  (at level 70, no associativity).
Inductive lt {H : Pre_Order_Field eq} (x y : X) : Prop :=
    | lt_intro (ltle : le x y) (lteq : ~eq x y) : lt x y.
Notation "x < y" := (lt x y)
    (at level 70, no associativity).

Theorem noteq : forall (a b c : X), a == b -> a != c -> b != c.
Proof.
  unfold not. intros. apply H0. rewrite H. apply H1.
Qed.

Theorem pOtq : forall {H : Pre_Order_Field eq} (a b c d : X), eq a b -> eq c d -> lt a c -> lt b d.
Proof.
    intros. inversion H2. unfold not in lteq. assert(b != c). apply (noteq a _ _).
    auto. auto. apply lt_intro. apply (poeq a _ c _). auto. auto. auto. rewrite H1 in H3.
    auto. 
Qed.

(** Class preOrderField (X : Type) :={
    le : X -> X -> Prop;
    pOE :> EquR X;
    ppO : PreOrder le;
    pOe : forall (x y : X), le x y -> le y x -> eq x y;
    pOo : forall (x y : X), le x y \/ le y x;
    pOeq : forall (a b c d : X), eq a b -> eq c d -> le a c -> le b d;
}.
Notation "x <= y" := (le x y)
  (at level 70, no associativity) : preOrderField. **)








Notation "x < y" := (lt x y)
  (at level 70, no associativity).

Module Test.

Class Field  (X : Type) (eq: relation X)  :={
    x0 : X;
    plus : X -> X -> X;
    HF1 : forall (x y : X), eq (plus x y) (plus y x);
    HF2 : forall (x y z : X), eq (plus (plus x y) z) (plus x (plus y z));
    HF3 : forall (x : X), eq (plus x0 x) x;
    HF4 : forall (x : X), (exists ix, eq (plus x ix) x0);
    HFeq : forall (a b c d : X), eq a b -> eq c d -> eq (plus a c) (plus b d);
}.

Class OrderedField (X : Type) (eq: relation X)  :={
    is_Field :> Field X eq;
    le: relation X;
    is_PO :> True; (* About le and eq *)
    HpO : forall (x y z : X), le x y -> le (plus x z) (plus y z);
    (*D : forall (x1 x2 : X), lt x1 x2 -> (exists x3, lt x1 x3 /\ lt x3 x2);*)
}.

End Test.
Class Field  (X : Type)  :={
    x0 : X;
    plus : X -> X -> X;
    FoF :> preOrderField X;
    HF1 : forall (x y : X), eq (plus x y) (plus y x);
    HF2 : forall (x y z : X), eq (plus (plus x y) z) (plus x (plus y z));
    HF3 : forall (x : X), eq (plus x0 x) x;
    HF4 : forall (x : X), (exists ix, eq (plus x ix) x0);
    HFeq : forall (a b c d : X), a -- b -> c -- d -> (plus a c) -- (plus b d);
    HpO : forall (x y z : X), le x y -> le (plus x z) (plus y z);
    D : forall (x1 x2 : X), lt x1 x2 -> (exists x3, lt x1 x3 /\ lt x3 x2);
}.

Notation "x + y" := (plus x y)
    (at level 50, left associativity) : Field.

Lemma HpOt : forall {X : Type} {H : Field X} (x y z : X), lt x y -> lt (plus x z) (plus y z).
Proof.
  intros.
(** require rewrite tatic to make a neat proof**)

Theorem division_of_eps : forall {X : Type} {H : Field X} (eps : X ), lt x0 eps
    -> (exists (d1 d2 : X), lt x0 d1 /\ lt x0 d2 /\ eq (plus d1 d2) eps) .
Proof.
    intros. destruct D with (x1 := x0) (x2 := eps). auto. destruct H1.
    assert(exists x', plus x x' -- x0). apply HF4. destruct H3.
    exists x. exists (plus eps x1). intros. assert(plus x (plus eps x1) -- plus (plus x x1) eps ).
    assert(plus x (plus eps x1) -- plus x (plus x1 eps)). assert((plus eps x1) -- (plus x1 eps)).
    apply HF1. apply (HFeq x x (plus eps x1) (plus x1 eps)). apply eqr. auto.
    assert(plus (plus x x1) eps -- plus x (plus x1 eps)). apply HF2. apply eqs in H5.
   apply (eqt (plus x (plus eps x1)) (plus x (plus x1 eps)) (plus (plus x x1) eps)).
   auto. auto. assert(plus (plus x x1) eps -- plus x0 eps). apply HFeq. auto. apply eqr.
    assert(plus x0 eps -- eps). apply HF3. apply eqt with (z := plus x0 eps) in H6.
    apply eqt with (z := eps) in H6. split. auto. split. assert(plus x x1 < plus eps x1).
    apply (HpOt x eps x1). auto. assert(plus x x1 -- x0). auto.
    apply (pOtq (plus x x1) x0 (plus eps x1) (plus eps x1)). auto. apply eqr.
    auto. assert(plus x (plus eps x1) -- plus x0 eps). apply eqt with (y := plus (plus x x1) eps).
    auto. auto. apply eqt with (y := plus x0 eps). auto. auto. apply HF3. apply eqs. auto.
Qed.

Class Metric (A : Type) (X : Type):={
    dist : A -> A -> X;
    M_EA :> EquR A;
    M_OF :> Field X;
    M1 : forall (p1 p2 : A), le x0 (dist p1 p2);
    M2 : forall (p1 p2 : A), eq (dist p1 p2) (dist p2 p1);
    M3 : forall (p1 p2 : A), eq p1 p2 -> eq (dist p1 p2) x0;
    M4 : forall (p1 p2 p3 : A), le (dist p1 p3) (plus (dist p1 p2) (dist p2 p2));
}.
Notation "[ x , y ]" := (dist x y)
    (at level 50, no associativity) : Metric.



Definition seq {A : Type} :=nat -> A -> Prop.

(** Quote from Litao Zhou's well definition. **)
Class CauchySeq (A : Type) (X : Type) (M : Metric A X) (Cseq : seq):={
    HCseq1 : forall(n : nat), (exists (a : A), Cseq n a);
    HCseq2 : forall(m : nat) (a1 a2 : A), (eq a1 a2) -> (Cseq m a1 <-> Cseq m a2);
    HCseq3 : forall(m : nat) (a1 a2 : A), Cseq m a1 -> Cseq m a2 -> (eq a1 a2);
    HCA : forall (eps : X), x0 < eps
      -> (exists (N : nat), forall (m n:nat), (N < m)%nat /\ (N < n)%nat
            -> forall (a b : A), Cseq m a /\ Cseq n b
         -> (dist a b) < eps);
}.

Class Converge (A : Type) (X : Type)  (M : Metric A X) (Seq : seq):={
    HC1 : forall(n : nat), (exists (a : A), Seq n a);
    HC2 : forall(m : nat) (a1 a2 : A), (eq a1 a2) -> (Seq m a1 <-> Seq m a2);
    HC3 : forall(m : nat) (a1 a2 : A), Seq m a1 -> Seq m a2 -> (eq a1 a2);
    HC : forall (eps : X), (exists (N : nat) (lim : A) , forall (n : nat) (a : A), (N < n)%nat -> Seq n a
      -> (dist a lim) < eps);
}.

Inductive Cauchilize {A X : Type}  {M : Metric A X}  : Type :=
  | con_intro (Cseq : seq)(H : CauchySeq A X M Cseq) .

Definition refl {A : Type} {H : EquR A} (reflseq : seq) (a : A) : Prop :=
  (forall (n : nat), reflseq n a) /\ (forall (a a': A) (n : nat) ,~eq a a' -> reflseq n a -> ~(reflseq n a')) /\
    (forall (a a' : A) (n : nat) , eq a a' -> reflseq n a -> reflseq n a').


Theorem c_trans :
    forall {A X : Type} (M : Metric A X) (reflseq : seq) (a : A),refl reflseq a
      -> CauchySeq A X M reflseq.
Proof.
    intros. unfold refl in H. split.
  +intros. exists a. destruct H. apply H.
  +split. *intros. destruct H. destruct H2.
              apply H3 with (a := a1). auto. auto.
              *intros. destruct H. destruct H2. apply H3 with (a := a2).
                apply eqs. auto. auto.
  +intros. assert (~(~eq a1 a2)).
             *destruct H. destruct H2. unfold not. intros.
               apply H2 with (n := m) in H4. apply H4. auto. auto.
            *apply NNPP in H2. auto.
  +intros. exists 0. intros.
          assert(~(a !- b)). *unfold not. intros. apply H3.
         destruct H2. destruct H. destruct H5. assert(reflseq n a). apply H.
         apply H5 with (n := n) in H3. unfold not in H3. apply H3 in H4. destruct H4. auto.
         *assert(~(a !- a0)). { unfold not. intros. apply H4. destruct H2. destruct H. destruct H6.
            assert(reflseq m a). apply H. apply H6 with (n := m) in H4. unfold not in H4. apply H4 in H2.
            destruct H2. auto. }
        apply NNPP in H3. apply NNPP in H4. apply eqs in H3. assert(b -- a0). apply (eqt b a a0).
        auto. auto. assert(dist a0 b -- x0). apply M3. apply eqs. auto. apply (pOtq x0 (dist a0 b) eps eps).
        apply eqs. auto. apply eqr. apply H0.
Qed.

Definition A_ := Type.
Definition X_ := Type.

Definition ctr {A X : Type}  (M : Metric A X)  (a : A) (reflseq : seq) (H : refl reflseq a) : Cauchilize :=
    con_intro reflseq (c_trans M reflseq a H).

Definition equC {A X : Type} {M : Metric A X} (x1 x2 : @Cauchilize A X M):  Prop  :=
  match x1,   x2 with
    | con_intro cseq1 C1, con_intro cseq2 C2 =>
        (forall (eps : X), x0 < eps
             -> (exists (N : nat), forall (n :nat), (N < n)%nat
             -> forall (a1 a2 : A), cseq1 n a1  -> cseq2 n a2
             -> (dist a1 a2) < eps))
  end.
Notation "a == b" := (equC a b)
    (at level 70, no associativity) : equC.
Lemma refl_equC : forall {A X : Type} {M : Metric A X} (x : @Cauchilize A X M), equC x x.
Proof.
  intros. unfold equC. destruct x. intros. inversion H. apply HCA0 in H0.
  destruct H0. exists x. intros. assert( (x < n) %nat /\  (x < n)%nat). split. auto. auto.
  apply H0 with (a := a1) (b := a2) in H4 . apply H4. split. apply H2. apply H3.
Qed.

Theorem EquR_trans : forall {X : Type} {M : Metric X X}, EquR X ->
   EquR (@Cauchilize X X M).
Proof.
  intros. split with (eq := equC).
  -split. +unfold Reflexive. apply refl_equC.
             +unfold Symmetric. unfold equC. destruct x. destruct y.
               intros. destruct H1 with (eps := eps). auto.
               exists x. intros. apply  apply H3 with (n := n). auto.





 -unfold equC. intros. destruct x. destruct y. destruct z. intros.
   apply division_of_eps in H4. destruct H4 as [d1]. destruct H4 as [d2].
  destruct H with (eps := d1). 
  auto. destruct H0 with (eps := d2). auto.
  

  assert((x <= x1)%nat \/ (x1 <= x)%nat). apply le_one.
  destruct H7. exists x1.
    +intros. assert(exists am, Cseq0 n am). apply HCseq1.
      destruct H11. destruct H5 with (n := n) (a1 := a1) (a2 := x2).
      apply le_lt_or_eq in H7. destruct H7. apply (lt_trans x x1 n).
      auto. auto. rewrite H7. auto. auto. auto.
      destruct H6 with (n := n) (a1 :=x2) (a2 := a2). auto. auto. auto.
      assert
   

Qed.



Definition leC {X : Type} {M : Metric X X} (x1 x2 : @Cauchilize X X M) : Prop :=
    match x1,   x2 with
    | con_intro cseq1 C1, con_intro cseq2 C2 =>
        (exists (N: nat), forall (n : nat), (N < n)%nat
            ->  forall (a1 a2 : X), cseq1 n a1  -> cseq2 n a2
             -> a1 < a2) \/ (equC x1 x2)
    end.


Notation " x1 <= x2" := (leC x1 x2) : leC.
(**
Definition siCauchilize : Type :=(@Cauchilize A_ X_ ).
Definition xsiCauchilize : Type :=(@Cauchilize X_ X_) .
Definition biCauchilize: Type := @Cauchilize (@Cauchilize A_ X_) (@Cauchilize X_ X_). **)




Theorem preOrder_trans : forall {X : Type} {M : Metric X X}, preOrderField X ->
   preOrderField (@Cauchilize X X M).
Proof.
  intros. . -intros. unfold leC. destruct x. right. apply refl_equC.
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
    auto. auto. rewrite <-H4 in H5. auto. auto. +unfold equC in H0. left.

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

