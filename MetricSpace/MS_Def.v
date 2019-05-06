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


Lemma always_greater : forall (m n : nat), exists N, (m < N)%nat /\ (n < N)%nat.
Proof.
    intro m. induction m. -intros. exists (S n).
    split. apply neq_0_lt. unfold not. intros. inversion H. unfold lt. apply le_n.
    -intros. destruct IHm with (n :=n) as [N']. destruct H. exists (S N').
    split. apply lt_n_S. auto. unfold lt. unfold lt in H0. apply (le_trans (S n) N' (S N')).
    auto. apply le_S. apply le_n.
Qed. 

(******************************************************************)
(** def of metric space**)
Class Pre_Order_Field {X : Type} (eq : relation X) :={
    le : relation X;
    pofr : forall(a b : X), eq a b -> le a b;
    poft : forall(a b c : X), le a b -> le b c -> le a c;
    poeq : forall (a b c d : X), eq a b -> eq c d -> le a c -> le b d;
    poor : forall (a b : X), le a b \/ le b a;
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
Notation "b >= a" := (le a b)
    (at level 70, no associativity).
Inductive lt {X : Type} {eq : relation X} {H : Pre_Order_Field eq} (x y : X) : Prop :=
    | lt_intro (ltle : le x y) (lteq : ~eq x y) : lt x y.
Notation "x < y" := (lt x y)
    (at level 70, no associativity).
Notation "y > x" := (lt x y)
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
(** Definition plus_inverse {X : Type} {eq : relation X} {Hpf : Plus_Field eq} (x : X) {ix : X} 
    (H : eq (x + ix) x0)  : X :=ix.
Notation "! x" := (plus_inverse x)
    (at level 35, no associativity).
Notation "a - b" := (plus a (!b))
    (at level 50, left associativity). **)
Section ProofModule.

Variables X : Type.
Variables eq : relation X.
Variables HE : Equivalence eq.

Notation "a == b" := (eq a b)
    (at level 70, no associativity).
Notation "a != b" := (~eq a b)
    (at level 70, no associativity).

Theorem ltor : forall {H : Pre_Order_Field eq} (x y : X) , x != y <-> x < y \/ y < x .
Proof.
    intros. split. { assert(x <= y \/ y <= x). apply poor. destruct H0. 
    -left. apply lt_intro. auto. auto.
    -right. apply lt_intro. auto. unfold not. intros. unfold not in H1. apply H1.
      symmetry. auto. }
                        { intros. destruct H0. inversion H0. auto. inversion H0. unfold not in lteq.
                           unfold not. intros. apply lteq. symmetry. auto. }
Qed.
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

Theorem lt_not : forall {H : Pre_Order_Field eq} (x y : X), ~(x < y) <-> y <= x.
Proof.
    intros. split. { intros. unfold not in H0. assert(x <= y \/ y <= x). apply poor.
    destruct H1. assert(x == y \/ x != y). apply classic. destruct H2.
    symmetry in H2. apply pofr. auto. assert(x < y). apply lt_intro.
    auto. auto. apply H0 in H3. destruct H3. auto. }
                         { intros. unfold not. assert(x == y \/ x != y). apply classic.
                           destruct H1. -intros. inversion H2. assert(x == y /\ ~(x == y)).
                           split. auto. auto. apply PNP in H3. apply H3.
                           -intros. apply H1. inversion H2. apply pore. auto. auto. } 
Qed.

Theorem lt_not_and :  forall {H : Pre_Order_Field eq} (x y : X), ~(x < y /\ y < x).
Proof.
    intros. unfold not. intros. destruct H0. inversion H0. inversion H1. assert(x == y).
    apply pore. auto. auto. unfold not in lteq. apply lteq. auto.
Qed.

Lemma le_not : forall {H : Pre_Order_Field eq} (x y : X), x < y <-> ~(y <= x).
Proof.
    intros. split. intros. unfold not. intros. inversion H0. assert(x == y). apply pore.
    auto. auto. unfold not in lteq. apply lteq. auto.
    intros. unfold not in H0. assert(~(~y>x)). +unfold not. intros. apply lt_not in H1.
    apply H0 in H1. destruct H1. +apply NNPP in H1. auto. 
 Qed.
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

Theorem lt_inv :forall {H : Plus_Field eq} (x y ix iy: X) ,x + ix == x0 -> y + iy == x0 ->
   x < y -> ix > iy.
Proof.
    intros. assert(x + ix < y + ix). apply HpOt. auto. rewrite H0 in H3.
    assert(iy + y + ix >iy + x0). rewrite pfa. rewrite pfc. rewrite (pfc iy _).
    apply HpOt. auto. rewrite pfc in H1. rewrite H1 in H4. rewrite pfc in H4. rewrite pfz in H4.
    rewrite pfz in H4. auto.
Qed.

Theorem division_of_eps : forall {H : Plus_Field eq} (eps : X ), lt x0 eps
    -> (exists (d1 d2 : X), lt x0 d1 /\ lt x0 d2 /\ eq (plus d1 d2) eps) .
Proof.
    intros. destruct (pd x0 eps). auto. destruct H1. exists x.
    destruct (pfi x) as [x']. exists (eps + x'). split. auto. split.
    apply (HpOt x eps x') in H2. rewrite H3 in H2. auto. rewrite (pfc eps x').
    rewrite <-pfa. rewrite H3. rewrite pfz. reflexivity.
Qed. 

Theorem lt_div :  forall {H : Plus_Field eq} (a b c : X), eq (plus a b) c -> a > x0 -> b > x0 ->  
    c  > a.
Proof.
    intros. assert(c <= a -> False). intros. rewrite <-H0 in H3. assert(exists ia, a + ia == x0).
    apply pfi. destruct H4 as [ia]. assert(a + ia >= a + b + ia). apply ppof. auto. rewrite H4 in H5.
    rewrite pfc in H5. rewrite <- pfa in H5. rewrite (pfc ia a) in H5. rewrite H4 in H5. rewrite pfz in H5.
    apply lt_not in H5. unfold not in H5. apply H5. auto. apply le_not in H3. auto.  
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

Definition equC {A X : Type} {eq : relation X} {eqA : relation A} {M : Metric eq eqA} (x1 x2 : Cauchilize eq eqA):  Prop  :=
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
      {M : Metric eq eqA} (x : @Cauchilize A X eq eqA M), equC x x.
Proof.
  intros. unfold equC. destruct x. intros. inversion H. apply HCA0 in H0.
  destruct H0. exists x. intros. assert( (x < n) %nat /\  (x < n)%nat). split. auto. auto.
  apply H0 with (a := a1) (b := a2) in H4 . apply H4. split. apply H2. apply H3.
Qed.

Instance EquR_trans : forall {X A : Type} {eq : relation X} {eqA : relation A} {HE : Equivalence eq} {HEA : Equivalence eqA}
{M : Metric eq eqA}, Equivalence (equC).
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
  assert(eq (dist a1 a + dist a a2) (d1 + d2) /\ ~eq (dist a1 a + dist a a2) (d1 + d2)). split. auto. auto.
  apply PNP in H17. destruct H17.
  +exists x. intros. assert(exists a, Cseq0 n a). apply HCseq1. destruct H13 as [a].
    destruct H8 with (n := n) (a1 := a) (a2 := a2).
         *apply le_lt_or_eq in H9. destruct H9. apply (lt_trans _ x _). auto. auto. rewrite <-H9 in H10.
           auto.
         *auto. *auto.
          *destruct H7 with(n := n) (a1 := a1) (a2 := a). auto. auto. auto.
            rewrite <- H6. assert(dist a1 a2 <= dist a1 a + dist a a2). apply mtr. assert(dist a1 a + dist a a2 < d1 + d2).
            apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro. auto. auto.
            apply le_lt_eq in H14. destruct H14. apply lttr with (y := dist a1 a + dist a a2).
            auto. auto. auto. rewrite <-H14 in H15. auto.
  +auto.
Defined.

Inductive ball {X : Type} {eq : relation X} {M : Metric eq eq} {HE : Equivalence eq} (a : X) (r : X) (x : X): Prop :=
    | ball_intro (L : x0 < r) (H : dist a x < r) : ball a r x.

Definition leC {X : Type} {eq : relation X} {M : Metric eq eq} {HE : Equivalence eq} (x1 x2 : Cauchilize eq eq) : Prop :=
    match x1,   x2 with
    | con_intro _ _ cseq1 _, con_intro _ _ cseq2 _ =>
         equC  x1 x2 \/ (exists (N : nat), forall (n : nat) (a1 a2 : X), (N < n)%nat -> cseq1 n a1
             -> cseq2 n a2 -> a1 < a2)
    end.
Notation " x1 <= x2" := (leC x1 x2) : leC.
Definition ltC {X : Type} {eq : relation X} {M : Metric eq eq} {HE : Equivalence eq} (x1 x2 : Cauchilize eq eq) : Prop := leC x1 x2 /\ ~equC x1 x2 .
Notation "x1 < x2" := (ltC x1 x2) : ltC.
Class PropBucket {X : Type} {eq : relation X} {M : Metric eq eq} {HE : Equivalence eq} :={
          inBall1 :  forall (a x eps y : X), ball a eps x -> ~ball a eps y -> a < y -> x < y ;
          inBall2 : forall (a x eps y : X), ball a eps x -> ~ball a eps y -> y < a -> y < x;
          orderPres1 : forall (a b c : X), a < b -> a < c -> dist a b < dist a c -> b < c;
          orderPres2 : forall (a b c : X), a < b -> a < c -> b < c -> dist a b < dist a c;
}. 
Theorem leC_pre : forall (X : Type) (eq : relation X) (M : Metric eq eq) (HE : Equivalence eq) (a b c d : Cauchilize eq eq) (HP : PropBucket), equC a b -> equC c d -> leC a c -> leC b d .
Proof.
  intros.
  destruct (classic (equC a c)). -unfold leC. destruct b. destruct d. left. rewrite <-H.
   rewrite  <-H0. auto.
    -unfold equC in H2. destruct a as [a ?], c as [c ?]. simpl in H1. destruct H1; [tauto |].
    apply not_all_ex_not in H2. destruct H2 as [eps]. apply not_all_ex_not in H2. destruct H2 as [Heps].
    assert(forall N : nat, (exists n : nat, (N < n)%nat /\ (exists a1 a2 : X, a n a1 /\
        c n a2 /\ eps <= dist a1 a2))).
        intros. apply not_ex_all_not with (n := N) in H2. apply not_all_ex_not in H2. destruct H2.
       exists x. split. apply not_all_ex_not in H2. destruct H2. auto. apply not_all_ex_not in H2.
       destruct H2. apply not_all_ex_not in H2. destruct H2. exists x2. apply not_all_ex_not in H2. 
       destruct H2. exists x3. apply not_all_ex_not in H2. destruct H2. apply not_all_ex_not in H2. 
       destruct H2. split. auto. split. auto. apply lt_not. auto. auto. destruct H1 as [N].
       destruct (division_of_eps _ _ _ eps) as [eps1 [eps2]]. auto. 
       destruct (division_of_eps _ _ _ eps1) as [eps1a [eps1b]]. destruct H6. auto.
        destruct (division_of_eps _ _ _ eps2) as [eps2a [eps2b]].
        destruct H6. 
        destruct H8. auto. 
        assert(exists N : nat, forall m n : nat, (N < m)%nat /\ (N < n)%nat -> forall t1 t2 : X, a m t1 /\ a n t2 -> eps1a > dist t1 t2).
         apply HCA. destruct H7. auto. 
         destruct H9 as [N9]. destruct b. simpl in H.
         destruct H with (eps := eps1b) as [N11]. +destruct H7. destruct H11. auto.
         +destruct H6 as [Heps1 [Heps2 Hepseq]]. destruct H7 as [Heps1a [Heps1b Heps1eq]].
         destruct H8 as [Heps2a [Heps2b Heps2eq]].
         assert(exists N : nat, forall m n : nat,
         (N < m)%nat /\ (N < n)%nat -> forall t1 t2 : X, c m t1 /\ c n t2 -> eps2a > dist t1 t2).
         apply HCA. auto. 
        destruct d. simpl  in H0. destruct H0 with (eps := eps2b) as [N8].
        auto. destruct H6 as [N6]. destruct (always_greater N N9) as [G0 Hfin].
        destruct (always_greater G0 N11) as [G1]. destruct (always_greater N6 N8) as [G2].
        destruct (always_greater G1 G2) as [G3]. destruct H5 with (N := G3) as [N15].
        destruct H12 as [HG1 HG2]. destruct H13 as [HG3 HG4]. destruct H14 as [HG5 HG6].
        destruct H15 as [HG7 H16]. destruct H16 as [apin [cpin H16] ]. destruct H16 as [H16 [H17 H18]]. destruct Hfin as [Hfin1 Hfin2].
        simpl. right. destruct (always_greater G3 N15) as [G]. destruct H12 as [HG8 HG9].
        exists G. intros. assert(exists afloat, a n afloat). apply HCseq1. destruct H15 as [afloat].
        assert(exists cfloat, c n cfloat). apply HCseq1. destruct H19 as [cfloat].
        destruct H9 with (m := N15) (t1 := apin) (n := n) (t2 := afloat).
        split. apply (lt_trans _ G0 _). auto.  apply (lt_trans _ G1 _). auto. apply (lt_trans _ G3 _).
        auto. auto.  apply (lt_trans _ G0 _). auto.  apply (lt_trans _ G1 _). auto.
        apply (lt_trans _ G3 _). auto. apply (lt_trans _ N15 _). auto.
        apply (lt_trans _ G _). auto. auto. split. auto. auto.
        destruct H6 with (m := N15) (t1 := cpin) (n := n) (t2 := cfloat).
        split.
        apply (lt_trans _ G2 _). auto. apply (lt_trans _ G3 _). auto. auto. auto.
        apply (lt_trans _ G2 _). auto. apply (lt_trans _ G3 _). auto. apply (lt_trans _ N15 _). auto.
     apply (lt_trans _ G _). auto. auto. split. auto. auto.
     destruct H8 with (n := n) (a1 := cfloat) (a2 := a2).
        apply (lt_trans _ G2 _). auto. apply (lt_trans _ G3 _). auto.
        apply (lt_trans _ N15 _). auto. apply (lt_trans _ G _). auto. auto.
        auto. auto.
      destruct H11 with (n := n) (a1 := afloat) (a2 := a1).
      apply (lt_trans _ G1 _). auto. apply (lt_trans _ G3 _). auto.
      apply (lt_trans _ N15 _). auto. apply (lt_trans _ G _). auto. auto.
      auto. auto.
      assert(dist apin a1 < eps1). {
          assert(dist apin a1 <= dist apin afloat + dist afloat a1). apply mtr.
          assert(dist apin afloat + dist afloat a1 < eps1a + eps1b).
          apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro.
          auto. auto. rewrite Heps1eq in H21. apply le_lt_eq in H20. destruct H20.
          apply lttr with (y := dist apin afloat + dist afloat a1). auto. auto. auto.
          rewrite <-H20 in H21. auto. }
      assert(dist cpin a2 < eps2). {
          assert(dist cpin a2 <= dist cpin cfloat + dist cfloat a2). apply mtr.
          assert(dist cpin cfloat + dist cfloat a2 < eps2a + eps2b).
          apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro.
          auto. auto. rewrite Heps2eq in H22. apply le_lt_eq in H21. destruct H21.
          apply lttr with (y := dist cpin cfloat + dist cfloat a2). auto. auto. auto.
          rewrite <-H21 in H22. auto. }
      assert(dist a1 cpin > eps2). {
          assert(dist a1 cpin + dist apin a1 >= dist apin cpin). rewrite pfc. 
           apply mtr. assert(exists id_api_a1,eq (dist apin a1 + id_api_a1) x0).
           apply pfi. destruct H23 as [id_api_a1].
           assert(dist a1 cpin + dist apin a1 + id_api_a1 >= dist apin cpin + id_api_a1).
           apply le_two_plus_two. auto. auto. apply pofr. reflexivity.
           rewrite pfa in H24. rewrite H23 in H24. rewrite (pfc _ x0) in H24. rewrite pfz in H24.
           assert(exists ieps1, eq (eps1 + ieps1) x0). apply pfi. destruct H25 as [ieps1].
           assert(id_api_a1 > ieps1). apply lt_inv with (x := dist apin a1) (y := eps1).
           auto. auto. auto. auto.
           assert(dist apin cpin + id_api_a1 > eps + ieps1). apply le_lt_eq in H18. destruct H18.
           apply lt_two_plus_two. auto. auto. auto. rewrite H18. rewrite pfc.
           rewrite (pfc _ id_api_a1). apply HpOt. auto. auto. rewrite <-Hepseq in H27.
           rewrite (pfc eps1 _) in H27. rewrite pfa in H27. rewrite H25 in H27. 
           rewrite pfc in H27. rewrite pfz in H27. apply le_lt_eq in H24.
           destruct H24. apply lttr with (y := dist apin cpin + id_api_a1). auto. auto. auto.
           rewrite H24 in H27. auto. }
       assert(dist a2 apin > eps1). {
           assert(dist a2 apin + dist cpin a2 >= dist apin cpin). rewrite (msy a2 _).
           rewrite (msy cpin _). apply mtr. 
           assert(exists id_cpi_a2, eq (dist cpin a2 + id_cpi_a2) x0).
           apply pfi. destruct H24 as [id_cpi_a2].
           assert(dist a2 apin + dist cpin a2 + id_cpi_a2 >= dist apin cpin + id_cpi_a2).
           apply le_two_plus_two. auto. auto. apply pofr. reflexivity. rewrite pfa in H25.
           rewrite H24 in H25. rewrite (pfc _ x0) in H25. rewrite pfz in H25.
           assert(exists ieps2, eq (eps2 + ieps2) x0). apply pfi. destruct H26 as [ieps2].
           assert(id_cpi_a2 > ieps2). apply lt_inv with (x := dist cpin a2) (y := eps2).
           auto. auto. auto. auto. assert(dist apin cpin + id_cpi_a2 > eps + ieps2).
           apply le_lt_eq in H18. destruct H18. apply lt_two_plus_two. auto. auto. auto. 
           rewrite H18. rewrite pfc. rewrite (pfc _ id_cpi_a2). apply HpOt. auto. auto.
           rewrite <-Hepseq in H28. rewrite pfa in H28. rewrite H26 in H28.
           rewrite pfc in H28. rewrite pfz in H28. apply le_lt_eq in H25. destruct H25.
           apply lttr with (y := dist apin cpin + id_cpi_a2). auto. auto. auto.
           rewrite H25 in H28. auto. }
           assert(ball apin eps1 a1). {apply ball_intro. auto. auto. }
           assert(ball cpin eps2 a2). {apply ball_intro. auto. auto. }
           assert(~ball apin eps1 a2). {unfold not. intros. inversion H26.
               assert(eps1 > dist apin a2 /\ eps1 < dist apin a2). split. auto. rewrite msy. auto.
               apply lt_not_and in H28. destruct H28. }
           assert(~ball cpin eps2 a1). {unfold not. intros. inversion H27.
               assert(eps2 > dist cpin a1 /\ eps2 < dist cpin a1). split. auto. rewrite msy. auto.
               apply lt_not_and in H29. destruct H29. }
            assert(~ball cpin eps2 apin). {unfold not. intros. inversion H28.
                assert(dist apin cpin > eps2). assert(eps > eps2). apply lt_div with (b := eps1). 
                auto. rewrite pfc. auto. auto. auto. apply le_lt_eq in H18. destruct H18.
                apply lttr with (y := eps). auto. auto. auto. rewrite <-H18. auto.
                assert(eps2 > dist cpin apin /\ eps2 < dist cpin apin). split. auto. rewrite msy. 
                auto. apply lt_not_and in H31. destruct H31. }
            assert(a2 > apin). {apply inBall2 with (a0 := cpin) (eps0 := eps2). auto. auto.
                destruct H1 with (n := N15) (a1 := apin) (a2 := cpin). apply (lt_trans _ G0 _).
                auto. apply (lt_trans _ G1 _). auto. apply (lt_trans _ G3 _). auto. auto. auto. auto.
                apply lt_intro. auto. auto. }
            apply inBall1 with (a0  := apin) (eps0 := eps1). auto. auto. auto.
Qed.
        
Instance leC_rewrite : forall (X : Type) (eq : relation X) (M : Metric eq eq) (HE : Equivalence eq) (HP : PropBucket) ,
      Proper (equC ==> equC ==> iff) leC.
Proof.
    intros. hnf. intro x1. intro x2. intro. hnf. intro. intro. intro. split.
    -apply leC_pre. auto. auto. auto.
    -apply leC_pre. auto.  symmetry. auto. symmetry. auto.
Defined.
Section leCModule.
Variables X : Type.
Variables eq : relation X.
Variables HE : Equivalence eq.
Variables M : Metric eq eq.
Variables HP : PropBucket.
Notation "a == b" := (eq a b)
    (at level 70, no associativity).
Notation "a != b" := (~eq a b)
    (at level 70, no associativity).

Theorem preOrder_trans : @Pre_Order_Field (Cauchilize eq eq) equC.
Proof.
     split with (le := leC).
     -intros. destruct a. destruct b. left. auto.
     -destruct a as [cseqa]. destruct b as [cseqb]. destruct c as [cseqc].
       intros. destruct H2. destruct H3.
            +rewrite H2. rewrite H3. left. reflexivity.
            +rewrite H2. right. auto.
            +destruct H3. *rewrite <- H3. right. auto.
                                    *right. destruct H2 as [N1]. destruct H3 as [N2].
                                    assert((N1 <= N2)%nat \/ (N2 <= N1)%nat). apply le_one.
                                    destruct H4. exists N2. {intros. assert(exists a, (cseqb n a)). 
                                    apply HCseq1. destruct H8 as[a]. apply lttr with (y := a).
                                    auto. apply H2 with (n := n) (a1 := a1) (a2 := a). apply le_lt_or_eq in H4.
                                    destruct H4. apply lt_trans with (p := n) in H4. auto.
                                    auto. rewrite H4. auto. auto. auto. apply H3 with (n := n) (a2 := a2) (a1 := a).
                                    apply le_lt_or_eq in H4. destruct H4. apply lt_trans with (p := n) in H4.
                                    auto. auto. auto. auto. auto. }
                                    { exists N1. intros. assert(exists a, cseqb n a).
                                    apply HCseq1. destruct H8 as [a]. apply lttr with (y := a).
                                    auto. apply H2 with (n := n). auto. auto. auto. apply H3 with (n := n). apply le_lt_or_eq in H4. destruct H4. apply lt_trans with (p := n) in H4. auto. auto. rewrite H4. auto. auto. auto. }
     -intros. rewrite <- H. rewrite <- H0. auto.
     -intros. destruct a. destruct b. destruct H. destruct H0.
       +auto.
       +auto.
       +symmetry. destruct H0.
         *auto.
         *intros. destruct H as [n1]. destruct H0 as [n2].
          assert((n1 <= n2)%nat \/ (n2 <= n1)%nat). apply le_one.
          destruct H3. {unfold equC. intros. exists n2. intros. assert (a1 > a2). 
          apply H with (n := n). apply le_lt_or_eq in H3. destruct H3. 
          apply lt_trans with (p := n) in H3. auto. auto. rewrite H3. 
          auto. auto. auto. assert (a1 < a2). apply H0 with (n := n). 
          auto. auto. auto. assert (a1 > a2 -> a2 > a1 -> False). intros. inversion H10.
          inversion H11. assert(a1 == a2). apply pore. auto. auto. assert(a1 == a2 /\ ~(a1 == a2)). split. auto. auto. apply PNP in H13. destruct H13. apply H10 in H8.
           destruct H8. auto. }
           {exists n1. intros. assert(a1 > a2). apply H with (n := n). auto. auto. auto.
            assert(a2 > a1). apply H0 with (n := n). apply le_lt_or_eq in H3. destruct H3.
            apply lt_trans with (p := n) in H3. auto. auto. rewrite H3. auto. auto. auto.
            assert (a1 > a2 -> a2 > a1 -> False). intros. inversion H10.
          inversion H11. assert(a1 == a2). apply pore. auto. auto. assert(a1 == a2 /\ ~(a1 == a2)). split. auto. auto. apply PNP in H13. destruct H13. apply H10 in H8.
           destruct H8. auto. }
Qed.
End leCModule.
Definition plusSeq {X : Type} {eq : relation X} {H : Plus_Field eq}  :=
    forall (seq1 seq2 : seq), (exists (pseq : seq), forall n a b, seq1 n a -> seq2 n b -> pseq n (a + b)) .




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

