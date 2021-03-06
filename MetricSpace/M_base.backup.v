(**This document illustrate the space which we work in and the hypo we 
     have already taken to construct this space**)
From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_new.
Section BaseSpace.
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

Variable HDD_pre : forall (x : X), eqX (distX zeroX x) x.
Theorem HDD_l : forall (a b c : A), leX (distX (dist a b) (dist a c)) (dist b c).
Proof.
  intros. Admitted. (**TODO**)

Variables HDD : forall (a b c : A), eqX (distX (dist a b) (dist a c)) (dist b c).
Variables HDDX : forall (a b c : X), eqX (distX (distX a b) (distX a c)) (distX b c).

Notation "a + b" := (plusX a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Theorem dist_eq : forall (a b : A), eqX (distX zeroX (dist a b)) (dist a b).
Proof.
    intros. assert(eqX zeroX (dist a a)). pose proof (mre a a) as [Hex1 ?]. symmetry.
    apply Hex1. reflexivity. rewrite H. rewrite HDD. reflexivity.
Qed.
Theorem distX_eq : forall (a b : X), eqX (distX zeroX (distX a b)) (distX a b).
Proof.
    intros. assert(eqX zeroX (distX a a)). pose proof (mre a a) as [Hex1 ?]. symmetry.
    apply Hex1. reflexivity. rewrite H. rewrite HDDX. reflexivity.
Qed.
Definition leseq (a b : CX) : Prop.
destruct a, b. apply(forall (x y : X) (n : nat), Cseq n x -> Cseq0 n y -> leX x y).
Defined.
Theorem le_leC : forall (a b : CX), leseq a b -> leCX a b.
Proof.
    intros. destruct(classic (equCX a b)).
    -rewrite H0. destruct b. simpl. left. intros. exists 0. intros. assert(eqX a1 a2).
     apply HCseq3 with (m := n);auto. rewrite H6. pose proof (mre a2 a2) as [Hex ?].
     rewrite Hex;auto. reflexivity.
   -destruct a. destruct b. simpl. simpl in H0. simpl in H. right.
    apply not_all_ex_not in H0. destruct H0 as [eps]. apply not_all_ex_not in H0.
    destruct H0 as [H3].
    destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
    destruct (division_of_eps _ _ _ _ _ _ eps1) as [epsex1 [epsex2[Hex1[Hex2 Hexeq]]]];auto.
    destruct H1. destruct H2. destruct HCA with (eps := epsex1) as [N1];auto.
    destruct HCA0 with (eps := epsex2) as [N2];auto. destruct (always_greater N1 N2) as [G].
    destruct H4. exists G. intros. apply not_ex_all_not with (n := n) in H0.
    apply not_all_ex_not in H0 as [N]. apply not_all_ex_not in H0 as [H9].
    apply not_all_ex_not in H0 as [a1pin]. apply not_all_ex_not in H0 as [a2pin].
    apply not_all_ex_not in H0 as [H10]. apply not_all_ex_not in H0 as [H11]. apply lt_not in H0.
    destruct H1 with (m := n) (n := N) (a := a1) (b := a1pin);split;auto.
    apply (lt_trans _ G _);auto. apply (lt_trans _ G _);[auto |apply (lt_trans _ n _);auto].
    apply H with (n := n);auto.
    destruct H2 with (m := n) (n := N) (a := a2) (b := a2pin). split.
    apply (lt_trans _ G _);auto. apply (lt_trans _ G _);[auto|apply (lt_trans _ n _); auto].
    split;auto. assert(epsex1 > distX a1 a1pin). apply lt_intro;auto.
    assert(epsex2 > distX a2 a2pin). apply lt_intro;auto.
    pose proof (lt_two_plus_two X eqX _ _ plusX zeroX).
    assert(epsex1 + epsex2> distX a1 a1pin + distX a2 a2pin).
    destruct (H14 (distX a1 a1pin) (distX a2 a2pin) (epsex1) (epsex2));apply lt_intro;auto.
    rewrite Hexeq in H15. unfold not. intros. rewrite H16 in H15. rewrite msy in H15.
    assert(distX a1pin a2 + distX a2 a2pin >= distX a1pin a2pin). apply mtr.
    assert(eps1 > distX a1pin a2pin).
    destruct (le_lt_eq _ _ _ (distX a1pin a2pin) (distX a1pin a2 + distX a2 a2pin)). 
    apply H18 in H17. destruct H17. apply lttr with (y := distX a1pin a2 + distX a2 a2pin);auto.
    rewrite H17. auto. assert(distX a1pin a2pin < eps).
    assert(eps1 < eps). pose proof (lt_div X eqX _ leX plusX zeroX).
    destruct H19 with (a:=eps1) (b := eps2) (c := eps);auto. apply lt_intro;auto.
    apply lttr with (y := eps1);auto. pose proof (lt_not X eqX _ leX).
    destruct H20 with (x := distX a1pin a2pin) (y := eps). apply H22 in H0. unfold not in H0.
    apply H0. auto. auto.
Qed.

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
         { rewrite dist_eq. apply H3 with (n := n);auto. }
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
        rewrite msy. rewrite dist_eq. apply H3 with (n := n);auto.
      +intros. destruct p1. destruct p2. simpl. simpl in H. intros. 
        destruct H with (eps := eps) as[N];auto.
         exists N. intros. rewrite <-dist_eq. rewrite msy. apply H3 with (n := n);auto.
         apply dit with (a := a1) (b := a2);auto. reflexivity. apply sig.
     -intros. apply le_leC. destruct p1, p2, p3. simpl. intros. destruct H2. destruct H3. rewrite He.
       rewrite He0. destruct Ha0. rewrite He1. destruct Hb0. rewrite He2. 
       assert(eqA a1 b1). destruct H0. apply HCseq3 with (m := n);auto. rewrite H2.
       assert(eqA a0 a). destruct H. apply HCseq3 with (m := n);auto. rewrite H3.
       assert(eqA b0 b). destruct H1. apply HCseq3 with (m := n);auto. rewrite H4.
       apply mtr.
     -intros. destruct p1,p2,p3,p4. simpl. intro. simpl in H0,H. intros.
      destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
      destruct H with (eps := eps1) as [N1];auto. destruct H0 with (eps := eps2) as [N2];auto.
      destruct (always_greater N1 N2) as [G]. exists G. intros. destruct H10. destruct H11.
      rewrite He. rewrite He0.
      assert(distX (dist a b) (dist a0 b0) <= distX (dist a b) (dist a b0) + distX (dist a b0) (dist a0 b0)).
      apply mtr. rewrite HDD, (msy a b0), (msy a0 b0), HDD in H10.
      assert(dist b b0 + dist a a0 < eps). rewrite <-Heq. 
      pose proof (lt_two_plus_two X eqX _ leX plusX zeroX).
      destruct H11 with (a := dist b b0) (b := dist a a0) (c := eps2) (d := eps1).
      destruct H7 with (n := n) (a1 := b) (a2 := b0). destruct H8. apply (lt_trans _ G _);auto.
      auto. auto. apply lt_intro;auto. destruct H6 with (n := n) (a1 := a) (a2 := a0).
      destruct H8. apply (lt_trans _ G _);auto. auto. auto. apply lt_intro;auto.
      rewrite (pfc eps1 _). apply lt_intro;auto.
      destruct (le_lt_eq _ _ _ (distX (dist a b) (dist b0 a0)) (dist b b0 + dist a a0)).
      apply H12 in H10. destruct H10. apply lttr with (y := dist b b0 + dist a a0);auto.
      rewrite (msy a0 b0). apply lt_intro;destruct H10;auto. apply lt_intro;destruct H11;auto.
      rewrite (msy a0 b0), H10. apply lt_intro; destruct H11; auto.
Qed.

(**The proof of the next theorem is itself redundant and trivial since it can be yielded by taking A = X.**)
Theorem ms_trans_X : Metric equCX equCX leCX plusCX zeroCX pfCX
        (@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDDX).
Proof.
    split.
    -intros. destruct(classic (equCX p1 p2)).
      +destruct p1. destruct p2. simpl. left. intros. simpl in H.
         destruct H with (eps := eps) as [N];auto. exists N. intros.
         destruct H6. rewrite He. assert(eqX zeroX a1). destruct H5;[reflexivity | auto].
         rewrite <-H6. pose proof orderPres2. assert(distX a b >= zeroX) as H8. apply mle. 
         destruct (@le_lt_eq X eqX leX pofX zeroX (distX a b)). apply H9 in H8. destruct H8.
         assert(distX zeroX (distX a b) < distX zeroX eps). assert(eps > distX a b).
         destruct H3 with (n := n) (a1 := a) (a2 := b);auto. apply lt_intro;auto.
         destruct H7 with (a := zeroX) (b := distX a b) (c := eps);auto.
         { apply lt_intro;destruct H8;auto. }
         { apply lt_intro;destruct H11;auto. }
         { apply lt_intro;auto. }
         { rewrite distX_eq. apply H3 with (n := n);auto. }
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
        destruct H6. reflexivity. symmetry. auto. rewrite H10. assert(~eqX a b). unfold not. intros.
        destruct H0 with (m := n) (a := a) (n := N3) (b := apin). split;apply (lt_trans _ G1 _);auto.
        apply (lt_trans _ n _);auto. split;auto. destruct H1 with (m := n) (a := b) (n := N3) (b := bpin).
        split;apply(lt_trans _ G1 _);auto. apply (lt_trans _ n _);auto. split;auto.
        assert(epsex1 > distX a apin). apply lt_intro;auto. assert(epsex2 > distX b bpin).
        apply lt_intro;auto. rewrite H11 in H12. rewrite msy in H12.
        assert(distX apin b + distX b bpin >= distX apin bpin). apply mtr.
        assert(distX apin b + distX b bpin < epsex1 + epsex2).
        pose proof (lt_two_plus_two _ eqX _ leX plusX zeroX  (distX apin b) (distX b bpin) (epsex1) (epsex2)) as [H15];auto. apply lt_intro;destruct H12;auto. apply lt_intro;destruct H13;auto.
        apply lt_intro;auto. rewrite Hexeq in H15. assert(eps1 < eps).
        pose proof (lt_div X eqX _ leX plusX zeroX eps1 eps2 eps) as [H16]. auto. auto. auto.
        apply lt_intro;auto. assert(distX apin b + distX b bpin < eps). apply lttr with (y := eps1);auto.
        assert(eps > distX apin bpin).
        destruct (le_lt_eq _ _ _(distX apin bpin)  (distX apin b + distX b bpin) ). apply H18 in H14.
        destruct H14. apply lttr with (y := distX apin b + distX b bpin);auto. rewrite H14;auto.
        assert(~eps > distX apin bpin). apply lt_not;auto. unfold not in H19. apply H19. auto.
        assert(distX a b >= zeroX). apply mle. assert(~(eqX (distX a b) zeroX)). 
        unfold not. intros. apply mre in H13. unfold not in H11. apply H11. auto.
        apply lt_intro; auto. unfold not. intros. unfold not in H13. apply H13. symmetry;auto.
        auto.
     -intros. destruct p1. destruct p2. simpl. intros. exists 0. intros. destruct H3.
      destruct H4. rewrite He. rewrite He0. assert(eqX a b0). destruct H.
      apply HCseq3 with (m:= n);auto. assert(eqX b a0). destruct H0.
      apply HCseq3 with (m:=n);auto. rewrite H3. rewrite H4. rewrite (msy b0 a0). 
      pose proof (mre (distX a0 b0) (distX a0 b0)) as [Hex1 ?];rewrite Hex1;auto;reflexivity.
     -intros. split.
        +intros. destruct p1. destruct p2. simpl. simpl in H. intros.
        destruct H with (eps := eps) as [N];auto. exists N. intros. destruct H5. rewrite He.
        assert(eqX a2 zeroX). destruct H6. reflexivity. symmetry. auto. rewrite H5.
        rewrite msy. rewrite distX_eq. apply H3 with (n := n);auto.
      +intros. destruct p1. destruct p2. simpl. simpl in H. intros. 
        destruct H with (eps := eps) as[N];auto.
         exists N. intros. rewrite <-distX_eq. rewrite msy. apply H3 with (n := n);auto.
         apply dit with (a := a1) (b := a2);auto. reflexivity. apply sig.
     -intros. apply le_leC. destruct p1, p2, p3. simpl. intros. destruct H2. destruct H3. rewrite He.
       rewrite He0. destruct Ha0. rewrite He1. destruct Hb0. rewrite He2. 
       assert(eqX a1 b1). destruct H0. apply HCseq3 with (m := n);auto. rewrite H2.
       assert(eqX a0 a). destruct H. apply HCseq3 with (m := n);auto. rewrite H3.
       assert(eqX b0 b). destruct H1. apply HCseq3 with (m := n);auto. rewrite H4.
       apply mtr.
     -intros. destruct p1,p2,p3,p4. simpl. intro. simpl in H0,H. intros.
      destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
      destruct H with (eps := eps1) as [N1];auto. destruct H0 with (eps := eps2) as [N2];auto.
      destruct (always_greater N1 N2) as [G]. exists G. intros. destruct H10. destruct H11.
      rewrite He. rewrite He0.
      assert(distX (distX a b) (distX a0 b0) <= distX (distX a b) (distX a b0) + distX (distX a b0) (distX a0 b0)).
      apply mtr. rewrite HDDX, (msy a b0), (msy a0 b0), HDDX in H10.
      assert(distX b b0 + distX a a0 < eps). rewrite <-Heq. 
      pose proof (lt_two_plus_two X eqX _ leX plusX zeroX).
      destruct H11 with (a := distX b b0) (b := distX a a0) (c := eps2) (d := eps1).
      destruct H7 with (n := n) (a1 := b) (a2 := b0). destruct H8. apply (lt_trans _ G _);auto.
      auto. auto. apply lt_intro;auto. destruct H6 with (n := n) (a1 := a) (a2 := a0).
      destruct H8. apply (lt_trans _ G _);auto. auto. auto. apply lt_intro;auto.
      rewrite (pfc eps1 _). apply lt_intro;auto.
      destruct (le_lt_eq _ _ _ (distX (distX a b) (distX b0 a0)) (distX b b0 + distX a a0)).
      apply H12 in H10. destruct H10. apply lttr with (y := distX b b0 + distX a a0);auto.
      rewrite (msy a0 b0). apply lt_intro;destruct H10;auto. apply lt_intro;destruct H11;auto.
      rewrite (msy a0 b0), H10. apply lt_intro; destruct H11; auto.
Qed.
End BaseSpace.
