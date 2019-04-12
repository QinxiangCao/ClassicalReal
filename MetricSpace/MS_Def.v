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

(** useful theorem**)
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
Class Pre_Order_Field {X : Type} (eq : relation X) :={
    le : relation X;
    pofr : forall(a b : X), eq a b -> le a b;
    poft : forall(a b c : X), le a b -> le b c -> le a c;
    poeq : forall (a b c d : X), eq a b -> eq c d -> le a c -> le b d;
    (** poor : forall (a b : X), le a b \/ le b a; **)
    pore : forall (a b : X), le a b -> le b a -> eq a b;
}.

Instance le_rewrite : forall (X : Type) (eq : relation X) (H : Equivalence eq) (Hpoe : Pre_Order_Field eq),
    Proper (eq ==> eq ==> iff) le.
Proof.
    intros. hnf. intros. split. -apply poeq. auto. auto.
        -apply poeq. symmetry. auto. symmetry. auto.
Defined.
Notation "a <= b" := (le a b)
    (at level 70, no associativity).
Inductive lt {X : Type} {eq : relation X} {H : Pre_Order_Field eq} (x y : X) : Prop :=
    | lt_intro (ltle : le x y) (lteq : ~eq x y) : lt x y.
Notation "x < y" := (lt x y)
    (at level 70, no associativity).
Instance  lt_rewrite : forall (X : Type) (eq : relation X) (H : Equivalence eq) (Hpoe : Pre_Order_Field eq),
    Proper (eq ==> eq ==> iff) lt.
Proof.
    intros. hnf. intros. hnf. intros. split.
    -intros. inversion H2. rewrite H0 in ltle. rewrite H1 in ltle.
      rewrite H1 in lteq. rewrite H0 in lteq. apply lt_intro. auto. auto.
    -intros. inversion H2. rewrite <-H0 in ltle. rewrite <-H1 in ltle.
      rewrite <-H1 in lteq. rewrite <-H0 in lteq. apply lt_intro. auto. auto.
Defined.

Class Plus_Field {X : Type} (eq : relation X):={
    plus : X -> X -> X; 
    p_pof :> Pre_Order_Field eq;
    x0 : X;
    pfc : forall (x y : X), eq (plus x y) (plus y x);
    pfa : forall (x y z : X), eq (plus (plus x y) z) (plus x (plus y z));
    pfz : forall (x : X), eq (plus x0 x) x;
    pfi : forall (x : X), (exists ix, eq (plus x ix) x0);
    pfeq : forall (a b c d : X), eq a b -> eq c d -> eq (plus a c) (plus b d);
    ppof : forall (x y z : X), le x y -> le (plus x z) (plus y z);
    pd : forall (x1 x2 : X), lt x1 x2 -> (exists x3 : X, lt x1 x3 /\ lt x3 x2);
}.
Notation "a + b" := (plus a b)
    (at level 50, left associativity).
Instance plus_rewrite : forall (X : Type) (eq : relation X) (H : Equivalence eq) (Hpf : Plus_Field eq),
    Proper (eq ==> eq ==> eq) plus.
Proof.
    intros. hnf. intros. hnf. intros. apply pfeq. auto. auto.
Defined.
Definition plus_le  {X : Type} {eq : relation X} {Hpf : Plus_Field eq} : X -> X -> X -> X -> Prop  :=
    fun a b c d => (a + b) <= (c + d).
Instance plus_le_rewrite : forall (X : Type) (eq : relation X) (H : Equivalence eq) (Hpf : Plus_Field eq),
    Proper (eq ==> eq ==> eq ==> eq ==> iff) plus_le.
Proof.
    intros. hnf. intros. hnf. intros. hnf. intros. hnf. intros. split.
    -unfold plus_le. intros. assert(eq (x + x1) (y + y0)). apply pfeq.
      auto. auto. assert(eq (x2 + x3) (y1 + y2)). apply pfeq. auto. auto.
      apply (poeq (x + x1) (y + y0) (x2 + x3) (y1 + y2)). auto. auto. auto.
    -unfold plus_le. intros. assert(eq (x + x1) (y + y0)). apply pfeq.
      auto. auto. assert(eq (x2 + x3) (y1 + y2)). apply pfeq. auto. auto.
      apply (poeq (y + y0) (x + x1) (y1 + y2) (x2 + x3)). symmetry. auto. symmetry. auto. auto.
Defined.
Section ProofModule.

Variables X : Type.
Variables eq : relation X.
Variables HE : Equivalence eq.

Notation "a == b" := (eq a b)
    (at level 70, no associativity).
Notation "a != b" := (~eq a b)
    (at level 70, no associativity).

(** Theorem ltor : forall {H : Pre_Order_Field eq} (x y : X) , x != y <-> x < y \/ y < x .
Proof.
    intros. split. { assert(x <= y \/ y <= x). apply poor. destruct H0. 
    -left. apply lt_intro. auto. auto.
    -right. apply lt_intro. auto. unfold not. intros. unfold not in H1. apply H1.
      symmetry. auto. }
                        { intros. destruct H0. inversion H0. auto. inversion H0. unfold not in lteq.
                           unfold not. intros. apply lteq. symmetry. auto. }
Qed. **)
Theorem le_two_plus_two : forall  {H : Plus_Field eq} (a b c d : X),
    a <= c -> b <= d -> a + b <= c + d.
Proof.
    intros. assert(a + b <= c + b). apply ppof. auto. assert(c + b <= c + d). rewrite pfc. rewrite (pfc c d).
    apply ppof. auto. apply (poft _ (c + b) _). auto. auto.
Qed.

Lemma ppot : forall {H : Plus_Field eq}  (x y z : X), lt x y -> lt (plus x z) (plus y z).
Proof.
    intros. apply lt_intro. inversion H0. apply ppof. auto. unfold not. intros. assert(exists iz , z + iz == x0).
    apply pfi. destruct H2 as [iz].
    assert(x + z + iz == y + z + iz). apply (pfeq (x + z) (y + z) iz iz).
    auto. reflexivity. rewrite pfa in H3. rewrite pfa in H3. rewrite H2 in H3.
    rewrite pfc, pfz in H3. rewrite pfc, pfz in H3. inversion H0.
    assert(x == y /\ x != y). split. auto. auto. apply PNP in H4. destruct H4.
Qed.

Theorem ltre : forall {H : Pre_Order_Field eq} (x : X), ~(x < x) .
Proof.
    intros. unfold not. intros. inversion H0. unfold not in lteq. apply lteq.
    reflexivity.
Qed.

Theorem le_lt_eq : forall {H : Pre_Order_Field eq} (x y : X), x <= y <-> (x  < y) \/ (x == y)  .
Proof.
    intros. split. { assert(x == y \/ ~(x == y)). apply classic.  destruct H0. right. auto. left. apply lt_intro.
    auto. auto. }
                      { intros. destruct H0. inversion H0. auto. apply pofr. auto. }
Qed.

(** Theorem lt_not : forall {H : Pre_Order_Field eq} (x y : X), ~(x < y) <-> y <= x.
Proof.
    intros. split. { intros. unfold not in H0. assert(x <= y \/ y <= x). apply poor.
    destruct H1. assert(x == y \/ x != y). apply classic. destruct H2.
    symmetry in H2. apply pofr. auto. assert(x < y). apply lt_intro.
    auto. auto. apply H0 in H3. destruct H3. auto. }
                         { intros. unfold not. assert(x == y \/ x != y). apply classic.
                           destruct H1. -intros. inversion H2. assert(x == y /\ ~(x == y)).
                           split. auto. auto. apply PNP in H3. apply H3.
                           -intros. apply H1. inversion H2. apply pore. auto. auto. } 
Qed. **)

Theorem lttr : forall {H : Pre_Order_Field eq} (x y z : X),
   x < y -> y < z -> x < z.
Proof.
    intros. inversion H0. inversion H1. apply lt_intro. apply (poft _ y _).
    auto. auto. unfold not. intros. rewrite <-H2 in ltle0. assert(x == y).
    apply pore. auto. auto. assert(~(x == y /\ x != y)). apply PNP.
    unfold not in H4. apply H4. split. auto. auto.
Qed.

Theorem lt_two_plus_two : forall  {H : Plus_Field eq} (a b c d : X),
    a < c -> b < d -> a + b < c + d.
Proof.
    intros. assert(a + b < c + b).
    -apply ppot. auto.
    -assert(c + b < c + d). +rewrite pfc. rewrite (pfc c d). apply ppot. auto.
                                          +apply (lttr _ (c + b) _). auto. auto.
Qed.

Theorem noteq : forall (a b c : X), a == b -> a != c -> b != c.
Proof.
  unfold not. intros. apply H0. rewrite H. apply H1.
Qed.

Lemma HpOt : forall {H : Plus_Field eq} (x y z : X), lt x y -> lt (plus x z) (plus y z).
Proof.
  intros. inversion H0. apply (ppof _ _ z) in ltle. assert(x + z != y  + z).
  unfold not. intros. unfold not in lteq. apply lteq. assert(exists z', z + z' == x0).
  apply pfi. destruct H2 as[z']. assert(x + z + z' == y + z + z'). rewrite H1. reflexivity.
  rewrite pfa in H3. rewrite H2 in H3. rewrite pfa in H3. rewrite H2 in H3. rewrite pfc in H3.
   rewrite pfz in H3. rewrite pfc in H3. rewrite pfz in H3. auto. apply lt_intro. auto. auto.
Qed.

Theorem division_of_eps : forall {H : Plus_Field eq} (eps : X ), lt x0 eps
    -> (exists (d1 d2 : X), lt x0 d1 /\ lt x0 d2 /\ eq (plus d1 d2) eps) .
Proof.
    intros. destruct (pd x0 eps). auto. destruct H1. exists x.
    destruct (pfi x) as [x']. exists (eps + x'). split. auto. split.
    apply (HpOt x eps x') in H2. rewrite H3 in H2. auto. rewrite (pfc eps x').
    rewrite <-pfa. rewrite H3. rewrite pfz. reflexivity.
Qed. 
End ProofModule.

Class Metric {A : Type} {X : Type} (eq : relation X) (eqA : relation A):={
    dist : A -> A -> X;
    mof :> Plus_Field eq;
    mle : forall (p1 p2 : A), le x0 (dist p1 p2);
    msy : forall (p1 p2 : A), eq (dist p1 p2) (dist p2 p1);
    mre : forall (p1 p2 : A), eqA p1 p2 -> eq (dist p1 p2) x0;
    mtr : forall (p1 p2 p3 : A), le (dist p1 p3) (plus (dist p1 p2) (dist p2 p3));
    meq : forall (p1 p2 p3 p4 : A), eqA p1 p2 -> eqA p3 p4 -> eq (dist p1 p3) (dist p2 p4);
}.
Notation "[ x , y ]" := (dist x y)
    (at level 50, no associativity) : Metric.
Instance dist_rewrite : forall (X A : Type) (eq : relation X) (eqA : relation A) (Heq : Equivalence eq) (HeqA : Equivalence eqA)
      (Hm : Metric eq eqA), Proper (eqA ==> eqA ==> eq) dist.
Proof.
    intros. hnf. intros. hnf. intros. apply meq. auto. auto.
Defined.

Definition seq {A : Type} :=nat -> A -> Prop.

(** Quote from Litao Zhou's well definition. **)
Class CauchySeq {A : Type} {X : Type} (eq : relation X) (eqA : relation A) {M : Metric eq eqA} (Cseq : seq):={
    HCseq1 : forall(n : nat), (exists (a : A), Cseq n a);
    HCseq2 : forall(m : nat) (a1 a2 : A), (eqA a1 a2) -> (Cseq m a1 <-> Cseq m a2);
    HCseq3 : forall(m : nat) (a1 a2 : A), Cseq m a1 -> Cseq m a2 -> (eqA a1 a2);
    HCA : forall (eps : X), x0 < eps
      -> (exists (N : nat), forall (m n:nat), (N < m)%nat /\ (N < n)%nat
            -> forall (a b : A), Cseq m a /\ Cseq n b
         -> (dist a b) < eps);
}.

Class Converge {A : Type} {X : Type} (eq : relation X) (eqA : relation A)  {M : Metric eq eqA} (Seq : seq):={
    HC1 : forall(n : nat), (exists (a : A), Seq n a);
    HC2 : forall(m : nat) (a1 a2 : A), (eqA a1 a2) -> (Seq m a1 <-> Seq m a2);
    HC3 : forall(m : nat) (a1 a2 : A), Seq m a1 -> Seq m a2 -> (eqA a1 a2);
    HC : forall (eps : X), (exists (N : nat) (lim : A) , forall (n : nat) (a : A), (N < n)%nat -> Seq n a
      -> (dist a lim) < eps);
}.

Inductive Cauchilize {A X : Type} (eq : relation X) (eqA : relation A)  {M : Metric eq eqA}  : Type :=
  | con_intro (Cseq : seq)(H : CauchySeq eq eqA Cseq) .

Definition refl {A : Type} (eqA : relation A) (reflseq : seq) (a : A) : Prop :=
  (forall (n : nat), reflseq n a) /\ (forall (a a': A) (n : nat) ,~eqA a a' -> reflseq n a -> ~(reflseq n a')) /\
    (forall (a a' : A) (n : nat) , eqA a a' -> reflseq n a -> reflseq n a').

Section ProofModule.
Variables X : Type.
Variables eq : relation X.
Variables HE : Equivalence eq.
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.

Notation "a == b" := (eq a b)
    (at level 70, no associativity).
Notation "a != b" := (~eq a b)
    (at level 70, no associativity).

Theorem c_trans :
    forall {M : Metric eq eqA} (reflseq : seq) (a : A),refl eqA reflseq a
      -> CauchySeq eq eqA reflseq.
Proof.
    intros. unfold refl in H. split.
  +intros. exists a. destruct H. apply H.
  +split. *intros. destruct H. destruct H2.
              apply H3 with (a := a1). auto. auto.
              *intros. destruct H. destruct H2. apply H3 with (a := a2).
                symmetry. auto. auto.
  +intros. assert (~(~eqA a1 a2)).
             *destruct H. destruct H2. unfold not. intros.
               apply H2 with (n := m) in H4. apply H4. auto. auto.
            *apply NNPP in H2. auto.
  +intros. exists 0. intros.
          assert(~(~eqA a  b)). *unfold not. intros. apply H3.
         destruct H2. destruct H. destruct H5. assert(reflseq n a). apply H.
         apply H5 with (n := n) in H3. unfold not in H3. apply H3 in H4. destruct H4. auto.
         *assert(~(~eqA a a0)). { unfold not. intros. apply H4. destruct H2. destruct H. destruct H6.
            assert(reflseq m a). apply H. apply H6 with (n := m) in H4. unfold not in H4. apply H4 in H2.
            destruct H2. auto. }
        apply NNPP in H3. apply NNPP in H4. symmetry in H3. assert(eqA b a0). transitivity a.
        auto. auto. assert(dist a0 b == x0). apply (mre a0 b). symmetry. auto. rewrite H6.
        auto.
Qed.

Definition ctr {M : Metric eq eqA}  (a : A) (reflseq : seq)
      (H : refl eqA reflseq a) : Cauchilize eq eqA :=
    con_intro eq eqA reflseq (c_trans reflseq a H).

End ProofModule.

Definition equC {A X : Type} (eq : relation X) (eqA : relation A) {M : Metric eq eqA} (x1 x2 : Cauchilize eq eqA):  Prop  :=
  match x1,   x2 with
    | con_intro _ _ cseq1 C1, con_intro _ _ cseq2 C2 =>
        (forall (eps : X), x0 < eps
             -> (exists (N : nat), forall (n :nat), (N < n)%nat
             -> forall (a1 a2 : A), cseq1 n a1  -> cseq2 n a2
             -> (dist a1 a2) < eps))
  end.
Notation "a == b" := (equC a b)
    (at level 70, no associativity) : equC.

Lemma refl_equC : forall {A X : Type} {eq : relation X} {eqA : relation A} {HE : Equivalence eq} {HEA : Equivalence eqA}
      {M : Metric eq eqA} (x : @Cauchilize A X eq eqA M), equC  eq eqA x x.
Proof.
  intros. unfold equC. destruct x. intros. inversion H. apply HCA0 in H0.
  destruct H0. exists x. intros. assert( (x < n) %nat /\  (x < n)%nat). split. auto. auto.
  apply H0 with (a := a1) (b := a2) in H4 . apply H4. split. apply H2. apply H3.
Qed.

Section ProofModule.
Variables X : Type.
Variables eq : relation X.
Variables HE : Equivalence eq.
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.

Notation "a == b" := (eq a b)
    (at level 70, no associativity).
Notation "a != b" := (~eq a b)
    (at level 70, no associativity).

Theorem EquR_trans : forall {M : Metric eq eq}, Equivalence (equC eq eq).
Proof.
  intros. split.
  -unfold Reflexive. apply refl_equC.
  -unfold Symmetric. unfold equC. destruct x. destruct y.
    intros. destruct H1 with (eps := eps). auto.
    exists x. intros. rewrite msy. apply H3 with (n := n). auto.
    auto. auto.
 -unfold Transitive. unfold equC. destruct x. destruct y. destruct z.
  intros. apply division_of_eps in H4. destruct H4 as [d1].
  destruct H4 as [d2]. destruct H4. destruct H5. destruct H2 with (eps := d1).
  auto. destruct H3 with (eps := d2). auto. assert((x <= x1) %nat \/ (x1 <= x)%nat). apply le_one.
  destruct H9. exists x1. intros. assert(exists a, Cseq0 n a). apply HCseq1. destruct H13 as [a].
  destruct H7 with (n := n) (a1 := a1) (a2 := a). apply le_lt_or_eq in H9. destruct H9. apply (lt_trans _ x1 _).
  auto. auto. rewrite H9. auto. auto. auto. destruct H8 with (n := n) (a1 := a) (a2 := a2). auto. auto. auto.
  assert(dist a1 a2 <= ((dist a1 a) + (dist a a2)) -> ((dist a1 a) + (dist a a2)) < eps -> dist a1 a2 < eps).
  intros. apply le_lt_eq in H14. destruct H14. apply lttr with (y := (dist a1 a + dist a a2)). auto.
  auto. auto. rewrite H14. auto. apply H14. apply mtr. apply lt_intro. rewrite <- H6. apply le_two_plus_two.
  auto. auto. auto. rewrite <- H6. unfold not. intros. assert(dist a1 a + dist a a2 < d1 + d2).
  apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro. auto. auto. inversion H16.
  assert(dist a1 a + dist a a2 == d1 + d2 /\ dist a1 a + dist a a2 != d1 + d2). split. auto. auto.
  apply PNP in H17. destruct H17.
  +exists x. intros. assert(exists a, Cseq0 n a). apply HCseq1. destruct H13 as [a].
    destruct H8 with (n := n) (a1 := a) (a2 := a2).
         *apply le_lt_or_eq in H9. destruct H9. apply (lt_trans _ x _). auto. auto. rewrite <-H9 in H10.
           auto.
         *auto. *auto.
          *destruct H7 with(n := n) (a1 := a1) (a2 := a). auto. auto. auto.
            rewrite <- H6. assert(dist a1 a2 <= dist a1 a + dist a a2). apply mtr. 
           
  
  

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

