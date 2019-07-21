From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_base.
(**This part will define what is a complete space and show that the space with Type
      Cauchilize eqX eqA leX plusX is complete**)
Section complete.
(**Prework**)
Existing Instance EquR_trans.
Existing Instance leC_rewrite.
Variables X : Type.
Variables eqX : relation X.
Variables HE : Equivalence eqX.
Variables leX : relation X.
Variables pofX : Pre_Order_Field eqX leX.
Variables plusX : X -> X -> X.
Variables zeroX : X.
Variables pfX : Plus_Field eqX leX plusX zeroX.
Variables distX : X -> X -> X.
Variables MX : Metric eqX eqX _ _ _ pfX distX.
Definition ltX : X -> X -> Prop :=@lt X eqX leX pofX.
Variables Dp : Density eqX pfX.
Variables HPD : forall a b c : X, eqX (distX (plusX a b) (plusX a c)) (distX b c).
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.
Variables dist : A -> A -> X.
Variables M : Metric eqX eqA leX plusX _ pfX dist.
Definition CX : Type := Cauchilize eqX eqX _ _ _ _.
Definition CA : Type := Cauchilize eqX eqA _ _ _ _.
Definition equCX : CX -> CX -> Prop :=@equC X X eqX eqX leX plusX zeroX distX pfX MX.
Definition leCX :=@leC X eqX leX plusX _ _ pfX MX HE.
Variables PB : PropBucket.
Definition pofCX :Pre_Order_Field equCX leCX :=@preOrder_trans X eqX leX plusX _ HE pfX _ MX Dp PB.
Definition plusCX :CX -> CX -> CX := M_new.plusCX X eqX HE leX plusX zeroX distX pfX MX Dp HPD .
Definition zeroCX :CX := M_new.zeroX X eqX HE leX plusX zeroX distX pfX MX.
Variables HIN : (forall a b : X, eqX (distX a b) (distX (inv a) (inv b))).
Definition pfCX : Plus_Field equCX leCX plusCX zeroCX  :=@pf_trans X eqX HE leX plusX zeroX distX pfX MX Dp HPD PB HIN.
Definition equCA : CA -> CA -> Prop := @equC A X eqX eqA leX plusX zeroX dist pfX M.
Variables HDD : forall (a b c : A), eqX (distX (dist a b) (dist a c)) (dist b c).
Variables HDDX : forall (a b c : X), eqX (distX (distX a b) (distX a c)) (distX b c).
Notation "a + b" := (plusX a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Definition dist_eq : forall (a b : A), eqX (distX zeroX (dist a b)) (dist a b).
  apply dist_eq with (leX := leX) (plusX := plusX) (pfX := pfX) (eqA := eqA);auto.
Defined.
Definition distX_eq : forall (a b : X), eqX (distX zeroX (distX a b)) (distX a b).
  apply distX_eq with (leX := leX) (plusX := plusX) (pfX := pfX);auto.
Defined.
Definition leseq (a b : CX) : Prop.
  destruct a, b. apply(forall (x y : X) (n : nat), Cseq n x -> Cseq0 n y -> leX x y).
Defined.
Definition le_leC : forall (a b : CX), leseq a b -> leCX a b.
  apply le_leC;auto.
Defined.
Definition MC : Metric equCX equCA leCX plusCX zeroCX pfCX
        (@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDD).
  apply ms_trans;auto.
Defined.
Definition MCX : Metric equCX equCX leCX plusCX zeroCX pfCX
        (@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDDX).
  apply ms_trans_X;auto.
Defined.

