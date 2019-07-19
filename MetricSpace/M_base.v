(**This document illustrate the space which we work in and the hypo we 
     have already taken to construct this space**)
From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_new.
Section BaseSpace.
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


End BaseSpace.