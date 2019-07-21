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
Variables Non_incr : forall (a : X), leX (distX zeroX a) a.
Notation "a + b" := (plusX a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Theorem ms_trans : Metric equCX equCA leCX plusCX zeroCX pfCX
        (@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDD).
Proof.
    split.
    -intros. destruct(classic (equCA p1 p2)).
      +destruct p1. destruct p2. simpl. left. intros. simpl in H.
         destruct H with (eps := eps) as [N];auto. exists N. intros.
         destruct H6. rewrite He. assert(eqX zeroX a1). destruct H5;[reflexivity | auto].
         rewrite <-H6. pose proof orderPres2. pose proof mle.
         destruct (@le_lt_eq X eqX leX pofX zeroX (dist a b)). apply H9 in H8. destruct H8.
         assert(distX zeroX (dist a b) < distX zeroX eps). assert(eps > dist a b).
         destruct H3 with (n := n) (a1 := a) (a2 := b);auto. apply lt_intro;auto.
         destruct H7 with (a := zeroX) (b := dist a b) (c := eps);auto.
         { apply lt_intro;destruct H8;auto. }
         { apply lt_intro;destruct H11;auto. }
         { apply lt_intro;auto. }
         { pose proof Non_incr. assert(distX zeroX eps <= eps). apply H12. 
            destruct (le_lt_eq _ _ _ (distX zeroX eps) eps). apply H14 in H13. destruct H13.
            apply lttr with (y := distX zeroX eps);auto. apply lt_intro;destruct H11;auto.
            apply lt_intro;destruct H13;auto. rewrite H13 in H11. apply lt_intro;destruct H11;auto. }
        rewrite <- H8. pose proof (mre zeroX zeroX) as [Hex1 Hex2];rewrite Hex1.
        auto. reflexivity.
      +destruct p1. destruct p2. simpl. right. simpl in H. apply not_all_ex_not in H.
        destruct H as [eps]. apply not_all_ex_not in H. destruct H as [H2].
        destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1[eps2 [Heps1 [Heps2 Heq]]]];auto.
        destruct(division_of_eps _ _ _ _ _ _ eps1) as [epsex1[epsex2 [Hepsex1 [Hepsex2 Hexeq]]]];auto.
        destruct H0. destruct HCA with (eps := epsex1) as [N1];auto.
        destruct H1. destruct HCA0 with (eps := epsex2) as [N2];auto.
        destruct (always_greater N1 N2) as [G1]. destruct H3. exists G1.
        intros. apply not_ex_all_not with (n := n) in H. apply not_all_ex_not in H.
        destruct H as [N3]. apply not_all_ex_not in H. destruct H as [H8].
        apply not_all_ex_not in H. destruct H7. rewrite He. destruct H as [apin].
        apply not_all_ex_not in H. destruct H as [bpin]. apply not_all_ex_not in H. destruct H as [H7].
        apply not_all_ex_not in H. destruct H as [H9]. apply lt_not in H. assert(eqX a1 zeroX).
        destruct H6. reflexivity. symmetry. auto. rewrite H10. assert(~eqA a b). unfold not. intros.
        destruct H0 with (m := n) (a := a) (n := N3) (b := apin). split;apply (lt_trans _ G1 _);auto.
        apply (lt_trans _ n _);auto. split;auto. destruct H1 with (m := n) (a := b) (n := N3) (b := bpin).
        split;apply(lt_trans _ G1 _);auto. apply (lt_trans _ n _);auto. split;auto.
        assert(epsex1 > dist a apin). apply lt_intro;auto. assert(epsex2 > dist b bpin).
        apply lt_intro;auto. rewrite H11 in H12. rewrite msy in H12.
        assert(dist apin b + dist b bpin >= dist apin bpin). apply mtr.
        assert(dist apin b + dist b bpin < epsex1 + epsex2).
        pose proof (lt_two_plus_two _ eqX _ leX plusX zeroX  (dist apin b) (dist b bpin) (epsex1) (epsex2)) as [H15];auto. apply lt_intro;destruct H12;auto. apply lt_intro;destruct H13;auto.
        apply lt_intro;auto. rewrite Hexeq in H15. assert(eps1 < eps).
        pose proof (lt_div X eqX _ leX plusX zeroX eps1 eps2 eps) as [H16]. auto. auto. auto.
        apply lt_intro;auto. assert(dist apin b + dist b bpin < eps). apply lttr with (y := eps1);auto.
        assert(eps > dist apin bpin).
        destruct (le_lt_eq _ _ _(dist apin bpin)  (dist apin b + dist b bpin) ). apply H18 in H14.
        destruct H14. apply lttr with (y := dist apin b + dist b bpin);auto. rewrite H14;auto.
        assert(~eps > dist apin bpin). apply lt_not;auto. unfold not in H19. apply H19. auto.
        assert(dist a b >= zeroX). apply mle. assert(~(eqX (dist a b) zeroX)). 
        unfold not. intros. apply mre in H13. unfold not in H11. apply H11. auto.
        apply lt_intro; auto. unfold not. intros. unfold not in H13. apply H13. symmetry;auto.
        auto.
     -intros. destruct p1. destruct p2. simpl. intros. exists 0. intros. destruct H3.
      destruct H4. rewrite He. rewrite He0. assert(eqA a b0). destruct H.
      apply HCseq3 with (m:= n);auto. assert(eqA b a0). destruct H0.
      apply HCseq3 with (m:=n);auto. rewrite H3. rewrite H4. rewrite (msy b0 a0). 
      pose proof (mre (dist a0 b0) (dist a0 b0)) as [Hex1 ?];rewrite Hex1;auto;reflexivity.
     -intros. split.
        +intros. destruct p1. destruct p2. simpl. simpl in H. intros.
        destruct H with (eps := eps) as [N];auto. exists N. intros. destruct H5. rewrite He.
        assert(eqX a2 zeroX). destruct H6. reflexivity. symmetry. auto. rewrite H5.
        rewrite msy. assert(distX zeroX (dist a b) <= dist a b). apply Non_incr.
        destruct H3 with (n := n) (a1 := a) (a2 := b);auto. assert(dist a b < eps).
        apply lt_intro;auto. destruct (le_lt_eq _ _ _ (distX zeroX (dist a b)) (dist a b)).
        apply H9 in H7. destruct H7. apply lttr with (y := dist a b);auto.
        apply lt_intro;destruct H7;auto. apply lt_intro;destruct H8;auto. rewrite H7.
        apply lt_intro;destruct H8;auto.
      +intros. destruct p1. destruct p2. simpl. simpl in H. intros. destruct H with (eps := eps) as[N];auto.
         exists N. intros. Admitted.
End BaseSpace.