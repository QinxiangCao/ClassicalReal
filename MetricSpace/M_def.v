From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_pre.
Class Pre_Order_Field {X : Type} (eqX : relation X) (le : relation X) :={
    pofr : forall(a b : X), eqX a b -> le a b;
    poft : forall(a b c : X), le a b -> le b c -> le a c;
    poeq : forall (a b c d : X), eqX a b -> eqX c d -> le a c -> le b d;
    poor : forall (a b : X), le a b \/ le b a;
    pore : forall (a b : X), le a b -> le b a -> eqX a b;
}.

Inductive lt {X : Type} {eqX : relation X} {le : relation X}
                {H : Pre_Order_Field eqX le} (x y : X) : Prop :=
    | lt_intro (ltle : le x y) (lteq : ~eqX x y) : lt x y.
Notation "x < y" := (lt x y)
    (at level 70, no associativity).
Notation "y > x" := (lt x y)
    (at level 70, no associativity).

Class Plus_Field {X : Type} (eqX : relation X) (le : relation X) (plus : X -> X -> X):={
    p_pof :> Pre_Order_Field eqX le;
    x0 : X;
    pfc : forall (x y : X), eqX (plus x y) (plus y x);
    pfa : forall (x y z : X), eqX (plus (plus x y) z) (plus x (plus y z));
    pfz : forall (x : X), eqX (plus x0 x) x;
    pfi_strong : forall (x : X), {ix | eqX (plus x ix) x0};
    pfeq : forall (a b c d : X), eqX a b -> eqX c d -> eqX (plus a c) (plus b d);
    ppof : forall (x y z : X), le x y -> le (plus x z) (plus y z);
}.
Definition inv {A : Type} {eqA : relation A} {le : relation A} {plus : A -> A -> A}
     {HP : Plus_Field eqA le plus} (a : A) :A.
    destruct pfi_strong with (x := a). apply x.
Defined.

Class Density {X : Type} (eqX :  relation X) {le : relation X} {plus : X -> X -> X}
        (PF : Plus_Field eqX le plus) :={
    pd : forall (x1 x2 : X), lt x1 x2 -> (exists x3 : X, lt x1 x3 /\ lt x3 x2);
}.

Class Metric {A : Type} {X : Type} (eqX : relation X) (eqA : relation A)
    (le : relation X) (plus : X -> X -> X)  (mof : Plus_Field eqX le plus):={
    dist : A -> A -> X;
    mle : forall (p1 p2 : A), le x0 (dist p1 p2);
    msy : forall (p1 p2 : A), eqX (dist p1 p2) (dist p2 p1);
    mre : forall (p1 p2 : A), eqA p1 p2 -> eqX (dist p1 p2) x0;
    mtr : forall (p1 p2 p3 : A), le (dist p1 p3) (plus (dist p1 p2) (dist p2 p3));
    meq : forall (p1 p2 p3 p4 : A), eqA p1 p2 -> eqA p3 p4 -> eqX (dist p1 p3) (dist p2 p4);
}.
Notation "[ x , y ]" := (dist x y)
    (at level 50, no associativity) : Metric.

Definition prj_nat {A : Type} := nat -> A -> Prop. (**relation nRA**)
Class well_seq {A : Type} {eqA : relation A} (s : prj_nat) :={
    HCseq1 : forall(n : nat), (exists (a : A), s n a); (**surjection**)
    HCseq2 : forall(m : nat) (a1 a2 : A), (eqA a1 a2) -> (s m a1 -> s m a2);(**equivalence class**)
    HCseq3 : forall(m : nat) (a1 a2 : A), s m a1 -> s m a2 -> (eqA a1 a2);(**injection**)
}. (**bijection**)
Class CauchySeq {A : Type} {X : Type} (eqX : relation X) (eqA : relation A) 
    {le : relation X} {plus : X -> X -> X} {mof : Plus_Field eqX le plus}
    {M : Metric eqX eqA le plus mof} (Cseq : prj_nat) : Prop :={
    HWS :> @well_seq A eqA Cseq;
    HCA : forall (eps : X), x0 < eps
      -> (exists (N : nat), forall (m n:nat), (N < m)%nat /\ (N < n)%nat
            -> forall (a b : A), Cseq m a /\ Cseq n b
         -> (dist a b) < eps);
}.
Inductive singleton {A : Type} {eqA : relation A} (a : A): nat -> A -> Prop :=
    | sig (n : nat) : singleton a n a
    | sig_eqv (n : nat) (b : A) (H : eqA a b) : singleton a n b.
Inductive dibasic {A :Type} {eqA : relation A} {le : relation A} {plus : A -> A -> A} 
    {HP : Plus_Field eqA le plus} (Pa Pb : @prj_nat A)
    : nat -> A -> Prop :=
    | bin (n :nat) (a b c: A) (Ha : Pa n a) (Hb : Pb n b) (He : eqA c (plus a b)): dibasic Pa Pb n c.
Inductive invseq {A : Type} {eqA : relation A} {le : relation A} {plus : A -> A -> A}
    {HP : Plus_Field eqA le plus} (P : @prj_nat A) 
    : nat -> A -> Prop :=
    | invsig (n : nat) (a : A) (H : P n a) : invseq P n (inv a)
    | inveqv (n : nat) (a b : A) (H : P n a) (He : eqA b (inv a)) : invseq P n b.