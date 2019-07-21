From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_prop.
(**definition and some propsition of new Cauchilized Space**)
Inductive Cauchilize {A X : Type} (eqX : relation X) (eqA : relation A)
                (leX : relation X) (plusX : X -> X -> X) (x0 : X) (dist : A -> A -> X)
                    {mof : Plus_Field eqX leX plusX x0}  {M : Metric eqX eqA leX plusX _ mof dist}  
                        : Type :=
  | con_intro (Cseq : prj_nat)(H : CauchySeq eqX eqA Cseq) .
Definition sig_inv {A X : Type} {eqX : relation X} {eqA : relation A}
          {leX : relation X} {plusX : X -> X -> X} {x0 : X} {dist : A -> A -> X}
                {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqA leX plusX _ mof dist}
                    {HEX : Equivalence eqX} {HEA : Equivalence eqA} (a : A) : 
            Cauchilize eqX eqA leX plusX _ _:= 
        con_intro eqX eqA leX plusX _ _ (@singleton A eqA a) 
                (c_trans X eqX HEX A eqA HEA leX plusX _ mof a).
Definition equC {A X : Type} {eqX : relation X} {eqA : relation A}
           {leX : relation X} {plusX : X -> X -> X} {x0 : X} {dist : A -> A -> X}
                {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqA leX plusX x0 mof dist} 
        (x1 x2 : Cauchilize eqX eqA leX plusX _ _):  Prop  :=
  match x1,   x2 with
    | con_intro _ _ _ _ _ _ cseq1 C1, con_intro _ _ _ _ _ _ cseq2 C2 =>
        (forall (eps : X), x0 < eps
             -> (exists (N : nat), forall (n :nat), (N < n)%nat
             -> forall (a1 a2 : A), cseq1 n a1  -> cseq2 n a2
             -> (dist a1 a2) < eps))
  end.
Notation "a == b" := (equC a b)
    (at level 70, no associativity) : equC.
Lemma refl_equC : forall {A X : Type} {eqX : relation X} {eqA : relation A}
          {leX : relation X} {plusX : X -> X -> X} {HE : Equivalence eqX} {x0 : X} {dist : A -> A -> X}
               {HEA : Equivalence eqA} {mof : Plus_Field eqX leX plusX x0} 
                  {M : Metric eqX eqA leX plusX _ mof dist} 
                      (x : @Cauchilize A X eqX eqA _ _ _ _ mof M), equC x x.
Proof.
  intros. unfold equC. destruct x. intros. inversion H. apply HCA in H0.
  destruct H0. exists x. intros. assert( (x < n) %nat /\  (x < n)%nat). split. auto. auto.
  apply H0 with (a := a1) (b := a2) in H4 . apply H4. split. apply H2. apply H3.
Qed.
Section EquR_playground.
Variables X : Type.
Variables A : Type.
Variables eqX : relation X.
Variables eqA : relation A. 
Variables  leX : relation X.
Variables plusX : X -> X -> X. 
Variables zero : X.
Variables HE : Equivalence eqX. 
Variables HEA : Equivalence eqA.
Variables mof : Plus_Field eqX leX plusX zero.
Variables dist : A -> A -> X.
Variables M : Metric eqX eqA leX plusX _ mof dist.
Variables Dpd : Density eqX mof.
Notation "a + b" := (plusX a b)
  (at level 50, left associativity).
Notation "a <= b" := (leX a b)
  (at level 70, no associativity).
Notation "a >= b" := (leX b a)
  (at level 70, no associativity).

Instance EquR_trans : Equivalence (equC).
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
  auto. destruct H3 with (eps := d2). auto. remember x0 as x1.
  assert((x <= x1) %nat \/ (x1 <= x)%nat). apply le_one.
  destruct H9. exists x1. intros. assert(exists a, Cseq0 n a). 
  apply HCseq1. destruct H13 as [a].
  destruct H7 with (n := n) (a1 := a1) (a2 := a). apply le_lt_or_eq in H9. 
  destruct H9. apply (lt_trans _ x1 _).
  auto. auto. rewrite H9. auto. auto. auto. 
  destruct H8 with (n := n) (a1 := a) (a2 := a2). auto. auto. auto. 
  assert(dist a1 a2 <= ((dist a1 a) + (dist a a2)) -> ((dist a1 a) + (dist a a2)) < eps -> dist a1 a2 < eps).
  intros. destruct (le_lt_eq X eqX _ (dist a1 a2) (plusX (dist a1 a) (dist a a2))) as [Hex1 Hex2].
  apply Hex1 in H14. destruct H14. 
  apply lttr with (y := (dist a1 a + dist a a2)). auto.
  auto. auto. rewrite H14. auto. apply H14. apply mtr. 
  apply lt_intro. rewrite <- H6. apply le_two_plus_two with (eqX := eqX) (x0 := zero);auto.
  rewrite <- H6. unfold not. intros. assert(dist a1 a + dist a a2 < d1 + d2).
  apply lt_two_plus_two. auto. apply lt_intro. auto. auto. 
  apply lt_intro. auto. auto. inversion H16.
  assert(eqX (dist a1 a + dist a a2) (d1 + d2) /\ ~eqX (dist a1 a + dist a a2) (d1 + d2)). 
  split. auto. auto.
  apply PNP in H17. destruct H17.
  +exists x. intros. assert(exists a, Cseq0 n a). apply HCseq1. destruct H13 as [a].
    destruct H8 with (n := n) (a1 := a) (a2 := a2).
         *apply le_lt_or_eq in H9. destruct H9. 
         apply (lt_trans _ x _). auto. auto. rewrite <-H9 in H10.
           auto.
         *auto. *auto.
          *destruct H7 with(n := n) (a1 := a1) (a2 := a). auto. auto. auto.
            rewrite <- H6. assert(dist a1 a2 <= dist a1 a + dist a a2). 
            apply mtr. assert(dist a1 a + dist a a2 < d1 + d2).
            apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro. auto. auto.
            destruct (le_lt_eq X eqX _  (dist a1 a2) (dist a1 a + dist a a2)) as [Hex1 Hex2]. apply Hex1 in H14. 
            destruct H14. apply lttr with (y := dist a1 a + dist a a2);auto.
            rewrite <-H14 in H15. auto.
  +auto.
  +auto.
Defined.
End EquR_playground.
Existing Instance EquR_trans.
Inductive ball {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
        {dist : X -> X -> X}
        {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqX _ _ _ mof dist} {HE : Equivalence eqX} 
    (a : X) (r : X) (x : X): Prop :=
    | ball_intro (L : x0 < r) (H : dist a x < r) : ball a r x.
Definition leC {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
        {dist : X -> X -> X}
        {mof : Plus_Field eqX leX plusX x0}  {M : Metric eqX eqX _ _ _ mof dist} {HE : Equivalence eqX} 
        (x1 x2 : Cauchilize eqX eqX _ _ _ _) : Prop :=
    match x1,   x2 with
    | con_intro _ _ _ _ _ _ cseq1 _, con_intro _ _ _ _ _ _ cseq2 _ =>
         equC  x1 x2 \/ (exists (N : nat), forall (n : nat) (a1 a2 : X), (N < n)%nat -> cseq1 n a1
             -> cseq2 n a2 -> a1 < a2)
    end.
Notation " x1 <= x2" := (leC x1 x2) : leC.
Definition ltC {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
        {dist : X -> X -> X}
        {mof : Plus_Field eqX leX plusX x0}  {M : Metric eqX eqX _ _ _ mof dist} {HE : Equivalence eqX} 
        (x1 x2 : Cauchilize eqX eqX _ _ _ _) : Prop := leC x1 x2 /\ ~equC x1 x2 .
Notation "x1 < x2" := (ltC x1 x2) : ltC.
Class PropBucket {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
                {dist : X -> X -> X}
                {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqX _ _ _ mof dist}
                {HE : Equivalence eqX} :={
          inBall1 :  forall (a x eps y : X), ball a eps x -> ~ball a eps y -> a < y -> x < y ;
          inBall2 : forall (a x eps y : X), ball a eps x -> ~ball a eps y -> y < a -> y < x;
          orderPres1 : forall (a b c : X), a < b -> a < c -> dist a b < dist a c -> b < c;
          orderPres2 : forall (a b c : X), a < b -> a < c -> b < c -> dist a b < dist a c;
}. 
Section leCpre_playground.
Variables X : Type.
Variables eqX : relation X.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables zero : X.
Variables mof : Plus_Field eqX leX plusX zero.
Variables dist : X -> X -> X.
Variables M : Metric eqX eqX _ _ _ mof dist.
Variables Dpd : Density eqX mof.
Variables HE : Equivalence eqX.

Variables HP : PropBucket.
Notation "a <= b" := (leX a b)
  (at level 70, no associativity).
Notation "a >= b" := (leX b a)
  (at level 70, no associativity).
Notation "a + b" := (plusX a b)
  (at level 50, left associativity).

Theorem leC_pre : forall (a b c d : Cauchilize eqX eqX _ _ _ _),
     equC a b -> equC c d -> leC a c -> leC b d .
Proof.
  intros.
  destruct (classic (equC a c)). -unfold leC. destruct b. destruct d. left.
  destruct (EquR_trans X X _ eqX leX plusX _ _ _ _ _ _); auto. rewrite <-H.
   rewrite  <-H0. auto.
    -unfold equC in H2. destruct a as [a ?], c as [c ?]. simpl in H1. destruct H1; [tauto |].
    apply not_all_ex_not in H2. destruct H2 as [eps]. apply not_all_ex_not in H2. destruct H2 as [Heps].
    assert(forall N : nat, (exists n : nat, (N < n)%nat /\ (exists a1 a2 : X, a n a1 /\
        c n a2 /\ eps <= dist a1 a2))).
        intros. apply not_ex_all_not with (n := N) in H2. apply not_all_ex_not in H2. destruct H2.
       exists x. split. apply not_all_ex_not in H2. destruct H2. auto. apply not_all_ex_not in H2.
       destruct H2. apply not_all_ex_not in H2. destruct H2. remember x1 as x2.
       exists x2. apply not_all_ex_not in H2. 
       destruct H2. exists x3. apply not_all_ex_not in H2. destruct H2. apply not_all_ex_not in H2. 
       destruct H2. split. auto. split. auto. destruct (lt_not X eqX _ _ (dist x2 x3) eps) as [Hex1 Hex2].
       apply Hex1;auto. destruct H1 as [N].
       destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2]]. auto. 
       destruct (division_of_eps _ _ _ _ _ _ eps1) as [eps1a [eps1b]]. destruct H6. auto.
        destruct (division_of_eps _ _ _ _ _ _ eps2) as [eps2a [eps2b]].
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
          auto. auto. rewrite Heps1eq in H21.
          destruct (le_lt_eq _ _ _  (dist apin a1) (dist apin afloat + dist afloat a1)) as [Hex1 Hex2]. 
          apply Hex1 in H20. destruct H20.
          apply lttr with (y := dist apin afloat + dist afloat a1). auto. auto. auto.
          rewrite <-H20 in H21. auto. }
      assert(dist cpin a2 < eps2). {
          assert(dist cpin a2 <= dist cpin cfloat + dist cfloat a2). apply mtr.
          assert(dist cpin cfloat + dist cfloat a2 < eps2a + eps2b).
          apply lt_two_plus_two. auto. apply lt_intro. auto. auto. apply lt_intro.
          auto. auto. rewrite Heps2eq in H22.
          destruct (le_lt_eq _ _ _ (dist cpin a2) (dist cpin cfloat +dist cfloat a2)) as [Hex1 Hex2].
          apply Hex1 in H21. destruct H21.
          apply lttr with (y := dist cpin cfloat + dist cfloat a2). auto. auto. auto.
          rewrite <-H21 in H22. auto. }
      assert(dist a1 cpin > eps2). {
          assert(dist a1 cpin + dist apin a1 >= dist apin cpin). rewrite pfc. 
           apply mtr. assert(exists id_api_a1,eqX (dist apin a1 + id_api_a1) zero).
           apply pfi. destruct H23 as [id_api_a1].
           assert(dist a1 cpin + dist apin a1 + id_api_a1 >= dist apin cpin + id_api_a1).
           apply le_two_plus_two with (eqX := eqX) (x0 := zero);auto. apply pofr. reflexivity.
           rewrite pfa in H24. rewrite H23 in H24. rewrite (pfc _ zero) in H24. rewrite pfz in H24.
           assert(exists ieps1, eqX (eps1 + ieps1) zero). apply pfi. destruct H25 as [ieps1].
           assert(id_api_a1 > ieps1). apply lt_inv with (x := dist apin a1) (y := eps1);auto.
           assert(dist apin cpin + id_api_a1 > eps + ieps1).
           destruct (le_lt_eq _ _ _ eps (dist apin cpin)) as [Hex1 Hex2].
           apply Hex1 in H18. destruct H18.
           apply lt_two_plus_two;auto. rewrite H18. rewrite pfc.
           rewrite (pfc _ id_api_a1). apply HpOt. auto. auto. rewrite <-Hepseq in H27.
           rewrite (pfc eps1 _) in H27. rewrite pfa in H27. rewrite H25 in H27. 
           rewrite pfc in H27. rewrite pfz in H27.
           destruct (le_lt_eq _ _ _ (dist apin cpin + id_api_a1) (dist a1 cpin)) as [Hex1 Hex2].
           apply Hex1 in H24.
           destruct H24. apply lttr with (y := dist apin cpin + id_api_a1); auto.
           rewrite H24 in H27. auto. }
       assert(dist a2 apin > eps1). {
           assert(dist a2 apin + dist cpin a2 >= dist apin cpin). rewrite (msy a2 _).
           rewrite (msy cpin _). apply mtr. 
           assert(exists id_cpi_a2, eqX (dist cpin a2 + id_cpi_a2) zero).
           apply pfi. destruct H24 as [id_cpi_a2].
           assert(dist a2 apin + dist cpin a2 + id_cpi_a2 >= dist apin cpin + id_cpi_a2).
           apply le_two_plus_two with (eqX := eqX) (x0 := zero);auto. apply pofr. reflexivity.
           rewrite pfa in H25.
           rewrite H24 in H25. rewrite (pfc _ zero) in H25. rewrite pfz in H25.
           assert(exists ieps2, eqX (eps2 + ieps2) zero). apply pfi. destruct H26 as [ieps2].
           assert(id_cpi_a2 > ieps2). apply lt_inv with (x := dist cpin a2) (y := eps2).
           auto. auto. auto. auto. assert(dist apin cpin + id_cpi_a2 > eps + ieps2).
           destruct (le_lt_eq _ _ _ eps (dist apin cpin)) as [Hex1 Hex2].
           apply Hex1 in H18. destruct H18. apply lt_two_plus_two;auto. 
           rewrite H18. rewrite pfc. rewrite (pfc _ id_cpi_a2). apply HpOt; auto.
           rewrite <-Hepseq in H28. rewrite pfa in H28. rewrite H26 in H28.
           rewrite pfc in H28. rewrite pfz in H28.
           destruct (le_lt_eq _ _ _ (dist apin cpin + id_cpi_a2) (dist a2 apin)) as [Hex1 Hex2].
           apply Hex1 in H25. destruct H25.
           apply lttr with (y := dist apin cpin + id_cpi_a2);auto.
           rewrite H25 in H28. auto. }
           assert(ball apin eps1 a1). {apply ball_intro;auto. }
           assert(ball cpin eps2 a2). {apply ball_intro;auto. }
           assert(~ball apin eps1 a2). {unfold not. intros. inversion H26.
               assert(eps1 > dist apin a2 /\ eps1 < dist apin a2). split. auto. rewrite msy. auto.
               apply lt_not_and in H28. destruct H28. }
           assert(~ball cpin eps2 a1). {unfold not. intros. inversion H27.
               assert(eps2 > dist cpin a1 /\ eps2 < dist cpin a1). split. auto. rewrite msy. auto.
               apply lt_not_and in H29. destruct H29. }
            assert(~ball cpin eps2 apin). {unfold not. intros. inversion H28.
                assert(dist apin cpin > eps2). assert(eps > eps2). apply lt_div with (b := eps1). 
                auto. rewrite pfc. auto. auto. auto. destruct (le_lt_eq _ _ _ eps (dist apin cpin)) as [Hex1 Hex2]. 
                apply Hex1 in H18. destruct H18.
                apply lttr with (y := eps);auto. rewrite <-H18;auto.
                assert(eps2 > dist cpin apin /\ eps2 < dist cpin apin). split. auto. rewrite msy. 
                auto. apply lt_not_and in H31. destruct H31. }
            assert(a2 > apin). {apply inBall2 with (a0 := cpin) (eps0 := eps2);auto.
                destruct H1 with (n := N15) (a1 := apin) (a2 := cpin). apply (lt_trans _ G0 _).
                auto. apply (lt_trans _ G1 _). auto. apply (lt_trans _ G3 _); auto. auto. auto.
                apply lt_intro. auto. auto. }
            apply inBall1 with (a0  := apin) (eps0 := eps1). auto. auto. auto.
Qed.
End leCpre_playground.
Instance leC_rewrite : forall (X : Type) (eqX : relation X) (leX : relation X) (plusX : X -> X -> X)
  (x0 : X) (dist : X -> X -> X)
  {mof : Plus_Field eqX leX plusX x0} (M : Metric eqX eqX _ _ _ mof dist) 
 {Dpd : Density eqX mof} (HE : Equivalence eqX) (HP : PropBucket) ,
      Proper (equC ==> equC ==> iff) leC.
    intros. hnf. intro x1. intro x2. intro. hnf. intro. intro. intro. split.
    -apply leC_pre. auto. auto. auto. auto.
    -apply leC_pre. auto. auto. destruct (EquR_trans X X _ eqX leX plusX _ _ _ _ _ _);auto.
      destruct (EquR_trans X X _ eqX leX plusX _ _ _ _ _ _);auto.
Defined.
Section leC_Field.
(**This section only talks about the pre_order_field on Cauchilize eqX eqX**)
Variables X : Type.
Variables eqX : relation X.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables x0 : X.
Variables HE : Equivalence eqX.
Variables mof : Plus_Field eqX leX plusX x0.
Variables dist : X -> X -> X.
Variables M : Metric eqX eqX _ _ _ mof dist.
Variables Dpd : Density eqX mof.
Variables HPB :PropBucket.
Notation "a == b" := (eqX a b)
    (at level 70, no associativity).
Notation "a != b" := (~eqX a b)
    (at level 70, no associativity).
Notation "a + b" := (plusX a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Instance le_prop_inst : Proper (equC ==> equC ==> iff) leC.
Proof.
       apply leC_rewrite;auto.
Defined.
Theorem preOrder_trans : @Pre_Order_Field (Cauchilize eqX eqX _ _ _ _) equC leC.
Proof.
      split.
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
                                    auto. apply H2 with (n := n). auto. auto. auto. apply H3 with (n := n). 
                                    apply le_lt_or_eq in H4. destruct H4. apply lt_trans with (p := n) in H4. 
                                    auto. auto. rewrite H4. auto. auto. auto. }
     -intros. rewrite <- H. rewrite <- H0. auto.
     -intros. destruct (classic (equC a b)). {left. unfold leC. destruct a. destruct b. left. auto. }
           {unfold not in H. destruct a. destruct b. unfold equC in H. apply not_all_ex_not in H.
           destruct H as [eps]. apply not_all_ex_not in H. destruct H as [Heps0].
           assert(forall N : nat, ~( forall n : nat,  (N < n)%nat -> forall a1 a2 : X, Cseq n a1 -> 
            Cseq0 n a2 -> eps > dist a1 a2)).
            intros. unfold not. intros. unfold not in H. apply H. exists N. auto.
            destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1]. auto. destruct H3 as [eps2].
            destruct H3 as [Heps1 [Heps2 Hepseq ]]. assert(forall eps : X,
       eps > x0 -> exists N : nat, forall m n : nat, (N < m)%nat /\ (N < n)%nat -> forall a b : X,
         Cseq0 m a /\ Cseq0 n b -> eps > dist a b). apply HCA.
         assert(forall eps : X,eps > x0 -> exists N : nat, 
         forall m n : nat, (N < m)%nat /\ (N < n)%nat -> forall a b : X,
         Cseq m a /\ Cseq n b -> eps > dist a b). apply HCA.
         destruct H3 with (eps := eps1) as [N5]. auto. destruct H4 with (eps := eps2) as [N6].
         auto. destruct (always_greater N5 N6) as [G0]. destruct H7. 
         assert(~ (forall n : nat, (G0 < n)%nat -> forall a1 a2 : X,  Cseq n a1 ->
      Cseq0 n a2 -> eps > dist a1 a2)). auto.
      apply not_all_ex_not in H9. destruct H9 as [N9]. apply not_all_ex_not in H9.
      destruct H9 as [N10]. apply not_all_ex_not in H9. destruct H9 as [pin].
      apply not_all_ex_not in H9. destruct H9 as [pin0]. apply not_all_ex_not in H9.
      destruct H9 as [Hpin]. apply not_all_ex_not in H9. destruct H9 as [Hpin0].
      apply lt_not in H9. assert(~ pin == pin0). unfold not. intros. apply mre in H10.
      rewrite H10 in H9. assert(~(x0 >= eps)). destruct (le_not _ _ _ _ x0 eps) as [Hex1 Hex2].
      apply Hex1;auto. unfold not in H11.
      apply H11. auto. assert(pin < pin0 \/ pin > pin0). apply ltor. auto. auto.
      destruct H11. {left. unfold leC. right. exists N9. intro n. intro float. intro float0.
      intros. destruct H6 with (m := N9) (a := pin) (n := n) (b := float). split.
      apply (lt_trans _ G0 _). auto. auto. apply (lt_trans _ G0 _). auto. apply (lt_trans _ N9 _).
      auto. auto. split. auto. auto. destruct H5 with (m := N9) (a := pin0) (n := n) (b := float0).
      split. apply (lt_trans _ G0 _). auto. auto. apply (lt_trans _ G0 _). auto.
      apply (lt_trans _ N9 _). auto. auto. split. auto. auto.
      assert(ball pin eps2 float). {apply ball_intro. auto. apply lt_intro. auto. auto. }
      assert(ball pin0 eps1 float0). {apply ball_intro. auto. apply lt_intro. auto. auto. }
      assert(~ball pin eps2 pin0). {unfold not. intros. inversion H17. assert(eps > eps2).
      apply lt_div with (b := eps1). auto. rewrite pfc. auto. auto. auto.
      assert(dist pin pin0 > dist pin pin0). destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex1 Hex2].
      apply Hex1 in H9. destruct H9.
      apply lttr with (y := eps). auto.
      apply lttr with (y := eps2). auto. auto. auto. auto.
      rewrite H9 in H19. apply lttr with (y := eps2);auto.
      pose proof (lt_not _ _ _ _ (dist pin pin0) (dist pin pin0)) as [Hex1 Hex2];auto.
      apply Hex2 in H20. destruct H20. auto. apply pofr. reflexivity. }
      assert(~ball pin0 eps1 float). {unfold not. intros. inversion H18.
          assert(eps1 < dist pin0 float). {assert(exists id_pin_float, dist pin float + id_pin_float == x0).
          apply pfi. destruct H20 as [id_pin_float]. assert(exists ieps2, eps2 + ieps2 == x0).
          apply pfi. destruct H21 as [ieps2]. assert(id_pin_float > ieps2).
           apply lt_inv with (y := eps2) (x := dist pin float). auto. auto. auto. apply lt_intro.
           auto. auto.
          assert(dist pin0 float + dist pin float >= dist pin pin0). rewrite pfc. rewrite (msy pin0 _). apply mtr.
          assert(dist pin0 float + dist pin float + id_pin_float >= dist pin pin0 + id_pin_float).
          apply le_two_plus_two with (eqX := eqX) (x0 := x0);auto. 
          apply pofr. reflexivity. rewrite pfa in H24.
          rewrite H20 in H24. rewrite (pfc _ x0) in H24. rewrite pfz in H24.
          assert(dist pin0 float > eps + ieps2). 
          destruct (le_lt_eq _ _ _ (dist pin pin0 + id_pin_float) (dist pin0 float)) as [Hex1 Hex2].
          apply Hex1 in H24. destruct H24.
          apply lttr with (y := dist pin pin0 + id_pin_float). auto. 
          destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex3 Hex4].
          apply Hex3 in H9.
          destruct H9. apply lt_two_plus_two. auto. auto. auto. rewrite H9.
          rewrite pfc. rewrite (pfc _ id_pin_float). apply HpOt. auto. auto. auto.
          rewrite <- H24. destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex3 Hex4].
          apply Hex3 in H9. destruct H9. apply lt_two_plus_two.
          auto. auto. auto. rewrite H9. rewrite pfc. rewrite (pfc _ id_pin_float). apply HpOt.
          auto. auto. rewrite <-Hepseq in H25. rewrite pfa in H25. rewrite H21 in H25.
          rewrite pfc in H25. rewrite pfz in H25. auto. }
          assert(~(dist pin0 float > eps1 /\ dist pin0 float < eps1)). apply lt_not_and.
          destruct H21. split. auto. auto. }
       assert(pin0 > float). apply inBall1 with (a := pin) (eps0 := eps2). auto. auto. auto.
       apply inBall2 with (a := pin0) (eps0 := eps1). auto. auto. auto. }
       {right. unfold leC. right. exists N9. intro n. intro float0. intro float.
      intros. destruct H6 with (m := N9) (a := pin) (n := n) (b := float). split.
      apply (lt_trans _ G0 _). auto. auto. apply (lt_trans _ G0 _). auto. apply (lt_trans _ N9 _).
      auto. auto. split. auto. auto. destruct H5 with (m := N9) (a := pin0) (n := n) (b := float0).
      split. apply (lt_trans _ G0 _). auto. auto. apply (lt_trans _ G0 _). auto.
      apply (lt_trans _ N9 _). auto. auto. split. auto. auto.
      assert(ball pin eps2 float). {apply ball_intro. auto. apply lt_intro. auto. auto. }
      assert(ball pin0 eps1 float0). {apply ball_intro. auto. apply lt_intro. auto. auto. }
      assert(~ball pin eps2 pin0). {unfold not. intros. inversion H17. assert(eps > eps2).
      apply lt_div with (b := eps1). auto. rewrite pfc. auto. auto. auto.
      assert(dist pin pin0 > dist pin pin0).
      destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex3 Hex4]. 
      apply Hex3 in H9. destruct H9.
      apply lttr with (y := eps). auto.
      apply lttr with (y := eps2). auto. auto. auto. auto.
      rewrite H9 in H19. apply lttr with (y := eps2). auto. auto. auto. 
      destruct (lt_not _ _ _ _ (dist pin pin0) (dist pin pin0)) as [Hex1 Hex2].
      apply Hex2 in H20.
      destruct H20. apply pofr. reflexivity. }
      assert(~ball pin0 eps1 float). {unfold not. intros. inversion H18.
          assert(eps1 < dist pin0 float). {assert(exists id_pin_float, dist pin float + id_pin_float == x0).
          apply pfi. destruct H20 as [id_pin_float]. assert(exists ieps2, eps2 + ieps2 == x0).
          apply pfi. destruct H21 as [ieps2]. assert(id_pin_float > ieps2).
           apply lt_inv with (y := eps2) (x := dist pin float). auto. auto. auto. apply lt_intro.
           auto. auto.
          assert(dist pin0 float + dist pin float >= dist pin pin0). rewrite pfc. rewrite (msy pin0 _). apply mtr.
          assert(dist pin0 float + dist pin float + id_pin_float >= dist pin pin0 + id_pin_float).
          apply le_two_plus_two with (eqX := eqX) (x0 := x0);auto. apply pofr. reflexivity. rewrite pfa in H24.
          rewrite H20 in H24. rewrite (pfc _ x0) in H24. rewrite pfz in H24.
          assert(dist pin0 float > eps + ieps2).
          destruct (le_lt_eq _ _ _ (dist pin pin0 + id_pin_float) (dist pin0 float)) as [Hex1 Hex2]. 
          apply Hex1 in H24. destruct H24.
          apply lttr with (y := dist pin pin0 + id_pin_float). auto.
          destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex3 Hex4]. 
          apply Hex3 in H9.
          destruct H9. apply lt_two_plus_two. auto. auto. auto. rewrite H9.
          rewrite pfc. rewrite (pfc _ id_pin_float). apply HpOt. auto. auto. auto.
          rewrite <- H24. destruct (le_lt_eq _ _ _ eps (dist pin pin0)) as [Hex3 Hex4].
          apply Hex3 in H9. destruct H9. apply lt_two_plus_two.
          auto. auto. auto. rewrite H9. rewrite pfc. rewrite (pfc _ id_pin_float). apply HpOt.
          auto. auto. rewrite <-Hepseq in H25. rewrite pfa in H25. rewrite H21 in H25.
          rewrite pfc in H25. rewrite pfz in H25. auto. }
          assert(~(dist pin0 float > eps1 /\ dist pin0 float < eps1)). apply lt_not_and.
          destruct H21. split. auto. auto. }
       assert(float > pin0). apply inBall2 with (a := pin) (eps0 := eps2). auto. auto. auto.
       apply inBall1 with (a := pin0) (eps0 := eps1). auto. auto. auto. } auto. }
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
          inversion H11. assert(a1 == a2). apply pore. auto. auto. assert(a1 == a2 /\ ~(a1 == a2)). 
          split. auto. auto. apply PNP in H13. destruct H13. apply H10 in H8.
           destruct H8. auto. }
           {exists n1. intros. assert(a1 > a2). apply H with (n := n). auto. auto. auto.
            assert(a2 > a1). apply H0 with (n := n). apply le_lt_or_eq in H3. destruct H3.
            apply lt_trans with (p := n) in H3. auto. auto. rewrite H3. auto. auto. auto.
            assert (a1 > a2 -> a2 > a1 -> False). intros. inversion H10.
          inversion H11. assert(a1 == a2). apply pore. auto. auto. 
          assert(a1 == a2 /\ ~(a1 == a2)). split. auto. auto. apply PNP in H13. 
          destruct H13. apply H10 in H8.
           destruct H8. auto. }
Qed.
End leC_Field.
Section plusC_playground.
Variables X : Type.
Variables eqX : relation X.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables HE : Equivalence eqX.
Variables A : Type.
Variables eqA : relation A.
Variables leA : relation A.
Variables plusA : A -> A -> A.
Variables HEA : Equivalence eqA.
Variables zeroX : X.
Variables mof : Plus_Field eqX leX plusX zeroX.
Variables dist : A -> A -> X.
Variables M : Metric eqX eqA _ _ _ mof dist.
Variables zeroA : A.
Variables HPA : Plus_Field eqA leA plusA zeroA.
        (**This Plus_Field is sometimes the same as the field mof**)
Variables Dpd : Density eqX mof.
Variables HPD : forall a b c, eqX (dist (plusA a b) (plusA a c)) (dist b c).
Notation "a + b" := (plusA a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Definition plusC (x y : Cauchilize eqX eqA _ _ _ _) : Cauchilize eqX eqA _ _ _ _.
    destruct x. destruct y. assert (CauchySeq eqX eqA (@dibasic A eqA _ _ _ HPA Cseq Cseq0)).
    apply plus_trans;auto. apply (con_intro eqX eqA _ _ _ _ (dibasic Cseq Cseq0) H1).
Defined.
Instance plusC_rewrite : Proper (equC ==> equC ==> equC) plusC.
    hnf. intros. hnf. intros. destruct x. destruct y. destruct x0. destruct y0. simpl in H0. simpl in H.
    simpl. intros. destruct (division_of_eps _ eqX _ _ _ _ eps H5) as [eps1].
    destruct H6 as [eps2[Heps1 [Heps2 Heq]]]. destruct H with (eps := eps1) as [N]. auto.
    destruct H0 with (eps := eps2) as [N0]. auto. destruct (always_greater N N0) as [G]. destruct H8.
    exists G. intros. destruct H11. destruct H12. rewrite He. rewrite He0.
    assert(dist (a + b) (a0 + b0) <= 
        plusX (dist (a + b) (a + b0)) (dist (a + b0) (a0 + b0))). apply mtr.
    rewrite HPD in H11. rewrite (pfc a b0) in H11. rewrite (pfc a0 b0) in H11. rewrite HPD in H11.
    assert(dist b b0 < eps2). apply H7 with (n := n). apply (lt_trans _ G _). auto. auto. auto. auto.
    assert (dist a a0 < eps1). apply H6 with (n := n). apply (lt_trans _ G _). auto. auto. auto. auto. auto.
    assert(plusX (dist b b0) (dist a a0) <plusX eps2 eps1). apply lt_two_plus_two. auto. auto. auto.
    rewrite (pfc eps2 _) in H14. rewrite Heq in H14.
    destruct (le_lt_eq _ _ _  (dist (a + b) (b0 + a0)) (plusX (dist b b0) (dist a a0))) as [Hex1 Hex2].
    apply Hex1 in H11. destruct H11. 
    apply lttr with (y := plusX (dist b b0) (dist a a0)). auto. rewrite (pfc a0 _ ); auto. 
    auto. rewrite (pfc a0 _). rewrite H11. auto.
Defined.

End plusC_playground.
Existing Instance plusC_rewrite.
Section plus_field_trans. 
 (**This section only prove that the Group (S, plusC, zeroC) is a well Group.
      S is the space of Type Cauchilize eqX eqX.**)
Variables X : Type.
Variables eqX : relation X.
Variables HE : Equivalence eqX.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables x0 : X.
Variables dist : X -> X -> X.
Notation "a + b" := (plusX a b)
    (at level 50, left associativity).
Notation "a <= b" := (leX a b)
    (at level 70, no associativity).
Notation "a >= b" := (leX b a)
    (at level 70, no associativity).
Variables mof : Plus_Field eqX leX plusX x0.
Variables MX : Metric eqX eqX _ _ _ mof dist.
Variables DX : Density eqX mof.
Variables HPD : forall a b c : X, eqX (dist (a + b) (a + c)) (dist b c).
Variables HPB :PropBucket.
Variables HIN : forall a b, eqX (dist a b) (dist (inv a) (inv b)).

Definition CX :Type := Cauchilize eqX eqX _ _ _ _.
Definition plusCX :CX -> CX -> CX.
    apply plusC with (leA := leX) (plusA := plusX) (zeroA := x0); auto.
Defined.
Definition zeroX :CX.
    apply (sig_inv x0).
Defined.
Definition invX (x : CX) :CX.
    destruct x. pose proof inv_trans.
    assert(CauchySeq eqX eqX (invseq Cseq)). apply H0;auto.
    apply (con_intro eqX eqX _ _ _ _ (invseq Cseq) H1).
Defined.
Definition pofX :Pre_Order_Field equC leC.
    apply preOrder_trans with (HE := HE). auto. auto.
Defined.
Theorem pf_trans : Plus_Field equC leC plusCX zeroX.
Proof.
  split.
  -apply pofX.
  -intros. destruct x. destruct y. simpl. intros. destruct H. destruct H0.
    exists 0. intros. destruct H0. destruct H2. assert(eqX a b0).
    destruct HWS. apply HCseq3 with (m := n). auto. auto.
    assert(eqX a0 b). apply HCseq3 with (m := n). auto. auto.
    rewrite He. rewrite He0. rewrite H0. rewrite H2.
    rewrite pfc. pose proof mre. destruct H3 with (p1 := b + b0) (p2 := b + b0).
    rewrite H4. auto. reflexivity.
  -intros. destruct x. destruct y. destruct z. simpl. intros. exists 0. intros. destruct H4. destruct H5.
    rewrite He. rewrite He0. destruct Ha. destruct Hb0. rewrite He2. rewrite He1.
    assert(eqX a a0). destruct H. destruct HWS. apply HCseq3 with (m := n). auto. auto.
    assert(eqX b1 a1). destruct H0. destruct HWS. apply HCseq3 with (m := n). auto.
    auto. assert(eqX b b0). destruct H1. apply HCseq3 with (m := n). auto. auto. 
    rewrite H4. rewrite H5. rewrite H6. rewrite pfa. 
    pose proof (mre (a0 + (a1 + b0)) (a0 + (a1 + b0))) as [Hex1 Hex2].
    rewrite Hex1. auto. reflexivity.
    -intros. destruct x. simpl. intros. exists 0. intros. destruct H2. assert(eqX a x0).
      destruct (@well_sig X eqX x0). auto. assert(@singleton X eqX x0 n x0). apply sig.
      apply HCseq3 with (m := n). auto. auto. rewrite H2 in He. rewrite pfz in He. rewrite He.
      assert(eqX a2 b). apply HCseq3 with (m := n). auto. auto. rewrite H4.
      pose proof (mre b b) as [Hex1 Hex2];rewrite Hex1. auto.
      reflexivity.
    -intros. exists(invX x). destruct x. simpl. intros. exists 0.
      intros. assert(eqX a2 x0). destruct H3. reflexivity. symmetry;auto.
      assert(eqX a1 x0). destruct H2. rewrite He. destruct Hb.
      assert(eqX a a0). destruct H. apply HCseq3 with (m := n);auto.
      rewrite <-H5. unfold inv. destruct pfi_strong;auto. rewrite He0.
      assert(eqX a a0). destruct H. apply HCseq3 with (m := n);auto.
      rewrite H5. unfold inv. destruct pfi_strong. auto. rewrite H5. rewrite H4.
      pose proof (mre x0 x0) as [Hex1 ?];rewrite Hex1;[auto |reflexivity].
    -intros. destruct a. destruct b. destruct c. destruct d. simpl.
      intros. destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1];auto.
      destruct H6 as [eps2 [Heps1 [Heps2 Heq]]].
      destruct H with (eps := eps1) as [N1];auto.
      destruct H0 with (eps := eps2) as [N2];auto.
      destruct (always_greater N1 N2) as [G]. destruct H8. exists G.
      intros. destruct H11. destruct H12. rewrite He. rewrite He0.
      assert(dist (a + b) (a0 + b0) <= dist (a + b) (a + b0) + dist (a + b0) (a0 + b0)).
      apply mtr. 
      assert(eqX (dist (a + b) (a + b0)) (dist b b0)) as Hex1.
      rewrite HPD. reflexivity.
      assert(eqX (dist (a + b0) (a0 + b0)) (dist a a0)) as Hex2.
      rewrite (pfc _ b0). rewrite (pfc _ b0). rewrite HPD;reflexivity.
      rewrite Hex1 in H11. rewrite Hex2 in H11.
      assert(dist b b0 + dist a a0 < eps2 + eps1). apply lt_two_plus_two;auto.
      apply H7 with (n := n) (a1 := b) (a2 := b0);auto. apply (lt_trans _ G _);auto.
      apply H6 with (n := n) (a1 := a) (a2 := a0);auto. apply(lt_trans _ G _);auto.
      rewrite (pfc eps2 _) in H12. rewrite Heq in H12.
      destruct (le_lt_eq _ _ _ (dist (a + b) (a0 + b0)) (dist b b0 + dist a a0)) as [Hex3 Hex4].
      apply Hex3 in H11.
      destruct H11. apply lttr with (y := (dist b b0 + dist a a0));auto.
      rewrite H11;auto.
    -intros. destruct x. destruct y. destruct z. simpl. simpl in H. destruct H.
      +left. intros. destruct H with (eps := eps) as [N];auto. exists N.
        intros. destruct H6. destruct H7. rewrite He. rewrite He0.
        assert(eqX b b0). destruct H2. apply HCseq3 with (m := n);auto.
        rewrite H6. rewrite (pfc a _). rewrite (pfc a0 _). rewrite HPD.
        apply H4 with (n := n);auto.
      +right. destruct H as [N]. exists N. intros. destruct H4. destruct H5.
        rewrite He. rewrite He0. assert(eqX b0 b). destruct H2.
        apply HCseq3 with (m := n);auto. rewrite H4. apply HpOt;auto.
        apply H with (n := n);auto.
Qed.
End plus_field_trans.
Definition distC  {A X : Type} {eqX : relation X} {eqA : relation A} {HE : Equivalence eqX} {HEA : Equivalence eqA}
           {leX : relation X} {plusX : X -> X -> X} {x0 : X} {dist : A -> A -> X} {distX : X -> X -> X}
                {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqA leX plusX x0 mof dist} 
                    {MX : Metric eqX eqX leX plusX x0 mof distX} {Dpd : Density eqX mof}
                        {HDD : forall (a b c : A), eqX (distX (dist a b) (dist a c)) (dist b c)} 
            (x1 x2 : Cauchilize eqX eqA leX plusX _ _) : Cauchilize eqX eqX leX plusX _ _ .
Proof.
  destruct x1. destruct x2.
    assert(CauchySeq eqX eqX (@distseq A X eqX eqA leX plusX x0 mof dist M Cseq Cseq0)).
    apply dist_trans;auto.
    apply(con_intro eqX eqX _ _ _ _ (@distseq A X eqX eqA leX plusX x0 mof dist M Cseq Cseq0) H1).
Defined.