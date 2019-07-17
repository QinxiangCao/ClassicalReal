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
Variables pfX : Plus_Field eqX leX plusX.
Variables MX : Metric eqX eqX _ _ pfX.

Variables Dp : Density eqX pfX.
Variables HPD : forall a b c : X, eqX (dist (plusX a b) (plusX a c)) (dist b c).

Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.

Variables M : Metric eqX eqA leX plusX pfX.

Definition CX : Type := Cauchilize eqX eqX _ _.
Definition CA : Type := Cauchilize eqX eqA _ _.

Definition leCX :=@leC X eqX leX plusX pfX MX HE. 
Definition plusCX : CX -> CX -> CX :=
      @plusC X eqX leX plusX HE X eqX leX plusX HE pfX MX pfX Dp HPD.

Variables PB : PropBucket.
Definition pofCX :=@preOrder_trans X eqX leX plusX HE pfX MX Dp PB.

Variables HIN : (forall a b : X, eqX (dist a b) (dist (inv a) (inv b))).
Definition pfCX :=@pf_trans X eqX HE leX plusX pfX MX Dp HPD PB HIN.
End BaseSpace.
(**Note that the leCX and plusCX are the same as the def used in M_new's proof**)