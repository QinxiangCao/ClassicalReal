From CReal.MetricSpace Require Export M_pack.
From CReal.MetricSpace Require Export M_def.
Instance le_rewrite : forall (X : Type) (eqX : relation X) (H : Equivalence eqX) 
    (le : relation X) (Hpoe : Pre_Order_Field eqX le),
    Proper (eqX ==> eqX ==> iff) le.
Proof.
    intros. hnf. intros. split. -apply poeq. auto. auto.
        -apply poeq. symmetry. auto. symmetry. auto.
Defined.
Instance  lt_rewrite : forall (X : Type) (eqX : relation X) (H : Equivalence eqX) 
 (le : relation X) (Hpoe : Pre_Order_Field eqX le),
    Proper (eqX ==> eqX ==> iff) lt.
Proof.
    intros. hnf. intros. hnf. intros. split.
    -intros. inversion H2. rewrite H0 in ltle. rewrite H1 in ltle.
      rewrite H1 in lteq. rewrite H0 in lteq. apply lt_intro. auto. auto.
    -intros. inversion H2. rewrite <-H0 in ltle. rewrite <-H1 in ltle.
      rewrite <-H1 in lteq. rewrite <-H0 in lteq. apply lt_intro. auto. auto.
Defined.
Theorem pfi : forall {X : Type} {eqX : relation X} {le : relation X} {plus : X -> X -> X}
     {x0 : X} {PF : Plus_Field eqX le plus x0} (x : X), 
          (exists ix, eqX (plus x ix) x0).
Proof.
    intros. pose proof pfi_strong. destruct X0 with (x := x). exists x1. auto.
Qed.

Instance plus_rewrite : forall (X : Type) (eqX : relation X) (H : Equivalence eqX)
 (le : relation X) (plus : X -> X -> X) (x0 : X) (Hpf : Plus_Field eqX le plus x0),
    Proper (eqX ==> eqX ==> eqX) plus.
Proof.
    intros. hnf. intros. hnf. intros. apply pfeq. auto. auto.
Defined.
Definition plus_le  {X : Type} {eqX : relation X}
     {le : relation X} {plus : X -> X -> X} {x0 : X} {Hpf : Plus_Field eqX le plus x0} :
             X -> X -> X -> X -> Prop  :=
    fun a b c d => le (plus a b) (plus c d).
Instance plus_le_rewrite : forall (X : Type) (eqX : relation X) (H : Equivalence eqX)     
     (le : relation X) (plus : X -> X -> X) (zero : X) (Hpf : Plus_Field eqX le plus zero),
    Proper (eqX ==> eqX ==> eqX ==> eqX ==> iff) plus_le.
Proof.
    intros. hnf. intros. hnf. intros. hnf. intros. hnf. intros. split.
    -unfold plus_le. intros. assert(eqX (plus x x0) (plus y y0)). apply pfeq.
      auto. auto. assert(eqX (plus x1 x2) (plus y1 y2)). apply pfeq. auto. auto.
      rewrite <-H5. rewrite <-H6. auto.
    -unfold plus_le. intros. assert(eqX (plus x x0) (plus y y0)). apply pfeq.
      auto. auto. assert(eqX (plus x1 x2) (plus y1 y2)). apply pfeq. auto. auto.
      rewrite H5. rewrite H6. auto.
Defined.

Section plus_prop.
Variables X : Type.
Variables eqX : relation X.
Variables HE : Equivalence eqX.
Variables le : relation X.
Variables plus : X -> X -> X.
Variables x0 : X.

Notation "a == b" := (eqX a b)
    (at level 70, no associativity).
Notation "a != b" := (~eqX a b)
    (at level 70, no associativity).
Notation "a <= b" := (le a b)
    (at level 70, no associativity).
Notation "a >= b" := (le b a)
    (at level 70, no associativity).
Notation "a + b" := (plus a b)
    (at level 50, left associativity).

Theorem ltor : forall {H : Pre_Order_Field eqX le}
     (x y : X) , x != y <-> x < y \/ y < x .
Proof.
    intros. split. { assert(x <= y \/ y <= x). apply poor. destruct H0. 
    -left. apply lt_intro. auto. auto.
    -right. apply lt_intro. auto. unfold not. intros. unfold not in H1. apply H1.
      symmetry. auto. }
                        { intros. destruct H0. inversion H0. auto. inversion H0. unfold not in lteq.
                           unfold not. intros. apply lteq. symmetry. auto. }
Qed.
Theorem le_two_plus_two : forall  {H : Plus_Field eqX le plus x0} (a b c d : X),
    a <= c -> b <= d -> a + b <= c + d.
Proof.
    intros. assert(a + b <= c + b). apply ppof. auto. assert(c + b <= c + d). rewrite pfc. rewrite (pfc c d).
    apply ppof. auto. apply (poft _ (c + b) _). auto. auto.
Qed.

Lemma ppot : forall {H : Plus_Field eqX le plus x0}  (x y z : X), 
        lt x y -> lt (plus x z) (plus y z).
Proof.
    intros. apply lt_intro. inversion H0. apply ppof. auto. unfold not. intros. assert(exists iz , z + iz == x0).
    apply pfi. destruct H2 as [iz].
    assert(x + z + iz == y + z + iz). apply (pfeq (x + z) (y + z) iz iz).
    auto. reflexivity. rewrite pfa in H3. rewrite pfa in H3. rewrite H2 in H3.
    rewrite pfc, pfz in H3. rewrite pfc, pfz in H3. inversion H0.
    assert(x == y /\ x != y). split. auto. auto. apply PNP in H4. destruct H4.
Qed.

Theorem ltre : forall {H : Pre_Order_Field eqX le} (x : X), ~(x < x) .
Proof.
    intros. unfold not. intros. inversion H0. unfold not in lteq. apply lteq.
    reflexivity.
Qed.

Theorem le_lt_eq : forall {H : Pre_Order_Field eqX le} (x y : X), x <= y <-> (x  < y) \/ (x == y)  .
Proof.

    intros. split. { assert(x == y \/ ~(x == y)). apply classic.  destruct H0. right. auto. left. apply lt_intro.
    auto. auto. }
                      { intros. destruct H0. inversion H0. auto. apply pofr. auto. }
Qed.

Theorem lt_not : forall {H : Pre_Order_Field eqX le} (x y : X), ~(x < y) <-> y <= x.
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

Theorem lt_not_and :  forall {H : Pre_Order_Field eqX le} (x y : X), ~(x < y /\ y < x).
Proof.
    intros. unfold not. intros. destruct H0. inversion H0. inversion H1. assert(x == y).
    apply pore. auto. auto. unfold not in lteq. apply lteq. auto.
Qed.

Lemma le_not : forall {H : Pre_Order_Field eqX le} (x y : X), x < y <-> ~(y <= x).
Proof.
    intros. split. intros. unfold not. intros. inversion H0. assert(x == y). apply pore.
    auto. auto. unfold not in lteq. apply lteq. auto.
    intros. unfold not in H0. assert(~(~y>x)). +unfold not. intros. apply lt_not in H1.
    apply H0 in H1. destruct H1. +apply NNPP in H1. auto. 
 Qed.
Theorem lttr : forall {H : Pre_Order_Field eqX le} (x y z : X),
   x < y -> y < z -> x < z.
Proof.
    intros. inversion H0. inversion H1. apply lt_intro. apply (poft _ y _).
    auto. auto. unfold not. intros. rewrite <-H2 in ltle0. assert(x == y).
    apply pore. auto. auto. assert(~(x == y /\ x != y)). apply PNP.
    unfold not in H4. apply H4. split. auto. auto.
Qed.

Theorem lt_two_plus_two : forall  {H : Plus_Field eqX le plus x0} (a b c d : X),
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

Lemma HpOt : forall {H : Plus_Field eqX le plus x0} (x y z : X), 
        lt x y -> lt (plus x z) (plus y z).
Proof.
  intros. inversion H0. apply (ppof _ _ z) in ltle. assert(x + z != y  + z).
  unfold not. intros. unfold not in lteq. apply lteq. assert(exists z', z + z' == x0).
  apply pfi. destruct H2 as[z']. assert(x + z + z' == y + z + z'). rewrite H1. reflexivity.
  rewrite pfa in H3. rewrite H2 in H3. rewrite pfa in H3. rewrite H2 in H3. rewrite pfc in H3.
   rewrite pfz in H3. rewrite pfc in H3. rewrite pfz in H3. auto. apply lt_intro. auto. auto.
Qed.

Theorem lt_inv :forall {H : Plus_Field eqX le plus x0} (x y ix iy: X) ,x + ix == x0 -> y + iy == x0 ->
   x < y -> ix > iy.
Proof.
    intros. assert(x + ix < y + ix). apply HpOt. auto. rewrite H0 in H3.
    assert(iy + y + ix >iy + x0). rewrite pfa. rewrite pfc. rewrite (pfc iy _).
    apply HpOt. auto. rewrite pfc in H1. rewrite H1 in H4. rewrite pfc in H4. rewrite pfz in H4.
    rewrite pfz in H4. auto.
Qed.

Theorem division_of_eps : forall {H : Plus_Field eqX le plus x0} 
      {Dpd : Density eqX H} (eps : X ), lt x0 eps
    -> (exists (d1 d2 : X), lt x0 d1 /\ lt x0 d2 /\ eqX (plus d1 d2) eps) .
Proof.
    intros. destruct (pd x0 eps). auto. destruct H1. exists x.
    destruct (pfi x) as [x']. exists (eps + x'). split. auto. split.
    apply (HpOt x eps x') in H2. rewrite H3 in H2. auto. rewrite (pfc eps x').
    rewrite <-pfa. rewrite H3. rewrite pfz. reflexivity.
Qed. 

Theorem lt_div :  forall {H : Plus_Field eqX le plus x0} (a b c : X), 
        eqX (plus a b) c -> a > x0 -> b > x0 -> c  > a.
Proof.
    intros. assert(c <= a -> False). intros. rewrite <-H0 in H3. assert(exists ia, a + ia == x0).
    apply pfi. destruct H4 as [ia]. assert(a + ia >= a + b + ia). apply ppof. auto. rewrite H4 in H5.
    rewrite pfc in H5. rewrite <- pfa in H5. rewrite (pfc ia a) in H5. rewrite H4 in H5. rewrite pfz in H5.
    apply lt_not in H5. unfold not in H5. apply H5. auto. apply le_not in H3. auto.  
Qed.

Theorem plus_same : forall {H : Plus_Field eqX le plus x0} (a b c : X), eqX a b <->
                eqX (c + a) (c + b).
Proof.
    intros. split.
    -intros. rewrite H0. reflexivity.
    -intros. assert(x0 + a == a). rewrite pfz. reflexivity.
    rewrite <-H1. destruct (pfi_strong c) as [ic]. rewrite <-e.
    rewrite pfc. rewrite <-pfa. rewrite (pfc a c). rewrite H0. rewrite pfa.
    rewrite (pfc b _). rewrite <-pfa. rewrite e. rewrite pfz. reflexivity.
Qed.

End plus_prop.
Instance dist_rewrite : forall (X A : Type) (eqX : relation X) (le : relation X)
    (plus : X -> X -> X) (x0 : X) (eqA : relation A) (Heq : Equivalence eqX) 
        (HeqA : Equivalence eqA) (mof : Plus_Field eqX le plus x0) (dist : A -> A -> X)
      (Hm : Metric eqX eqA le plus _ mof dist), Proper (eqA ==> eqA ==> eqX) dist.
Proof.
    intros. hnf. intros. hnf. intros. apply meq. auto. auto.
Defined.

Lemma well_sig : forall {A : Type} {eqA : relation A} {a : A},
    Equivalence eqA -> @well_seq A eqA (@singleton A eqA a).
Proof.
  intros. split.
  -intros. pose proof (@sig A eqA). exists a. auto.
  -intros. apply sig_eqv. destruct H1. auto. rewrite H1. auto.
  -intros. destruct H0. destruct H1. reflexivity. auto. destruct H1. symmetry. auto.
    rewrite <-H0. auto.
Qed.

Section injectionC.
Variables X : Type.
Variables eqX : relation X.
Variables HE : Equivalence eqX.
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.
Variables le : relation X.
Variables plus : X -> X -> X.
Variables x0 : X.
Variables mof : Plus_Field eqX le plus x0.

Notation "a == b" := (eqX a b)
    (at level 70, no associativity).
Notation "a != b" := (~eqX a b)
    (at level 70, no associativity).
Theorem c_trans :
    forall {dist : A -> A -> X} {M : Metric eqX eqA le plus _ mof dist} (a : A),
      CauchySeq eqX eqA (@singleton A eqA a).
Proof.
  intros. split. apply well_sig. auto.
  intros. exists 0. intros. destruct H1. pose proof (@well_sig A eqA a HEA).
  assert (eqA a0 b).
  assert(@singleton A eqA a m a). apply sig.
  assert(@singleton A eqA a n a). apply sig.
  assert(eqA a0 a). apply HCseq3 with (m0 := m).
  auto. auto. assert(eqA b a).
  apply HCseq3 with (m0 := n). auto. auto.
  rewrite H6. symmetry. rewrite H7. reflexivity.
  assert(eqX (dist a0 b) x0). rewrite H4. apply mre. reflexivity.
  rewrite H5. auto.
Qed.
End injectionC.
Lemma well_dibasic : forall {A : Type} {eqA : relation A} 
    {leA : relation A} {plusA : A -> A -> A} {zero : A} {HP : Plus_Field eqA leA plusA zero}
        (Pa Pb : @prj_nat A),
    Equivalence eqA -> @well_seq A eqA Pa -> @well_seq A eqA Pb
      -> @well_seq A eqA (dibasic Pa Pb).
Proof.
    intros. split.
    -intros. destruct H0. destruct H1. destruct (HCseq1 n). destruct (HCseq0 n).
      exists(plusA x x0). apply bin with (a := x) (b := x0). auto. auto. reflexivity.
    -intros. destruct H3. rewrite He in H2. apply bin with (a0 := a) (b0 := b).
    auto. auto. symmetry. auto.
    -intros. destruct H2. destruct H3. assert(eqA a a0). destruct H0.
      apply HCseq3 with (m := n). auto. auto. assert(eqA b b0).
      destruct H1. apply HCseq3 with (m := n). auto. auto.
      rewrite H2 in He. rewrite H3 in He. rewrite <- He in He0. symmetry. auto.
Qed.
Instance inv_rewrite : forall {A : Type} {eqA : relation A}
        {leA : relation A} {plusA : A -> A -> A} {x0 : A} {HP : Plus_Field eqA leA plusA x0}
               {HE : Equivalence eqA},
    Proper (eqA ==> eqA) inv.
Proof.
    intros. hnf. intros. destruct (pfi_strong x) as [ix]. destruct (pfi_strong y) as [iy].
    unfold inv. destruct pfi_strong as [ix']. destruct pfi_strong as [iy'].
    rewrite <-e in e1. rewrite <-plus_same in e1.
    rewrite <-e0 in e2. rewrite <- plus_same in e2.
    rewrite <-e in e0. rewrite H in e0. rewrite <-plus_same in e0.
    rewrite e0 in e2. rewrite <-e2 in e1. auto. auto. apply HP. auto. apply HP. auto.
    apply HP.
Defined.
Lemma well_inv : forall {A : Type} {eqA : relation A} {leA : relation A} {plusA : A -> A -> A}  {x0 : A}
    {HP : Plus_Field eqA leA plusA x0} (P : @prj_nat A),
          Equivalence eqA -> @well_seq A eqA P -> @well_seq A eqA (invseq P).
Proof.
    intros. split.
    -intros. destruct (HCseq1 n). destruct (pfi_strong x) as [ix]. exists ix.
      apply inveqv with (a := x). auto. assert(eqA (plusA x (inv x)) x0).
      unfold inv. destruct pfi_strong. auto. rewrite <-H2 in e.
      rewrite <-plus_same in e;[auto | auto | apply HP].
    -intros. destruct (HCseq1 m). apply inveqv with (a := x).
    auto. destruct H2. assert(eqA a x). apply HCseq3 with (m := n);auto.
     rewrite <-H4. symmetry. auto. rewrite <-H1.
     assert(eqA a x). apply HCseq3 with (m := n);auto. rewrite <-H4;auto.
   -intros. destruct H1. destruct H2. assert(eqA a a0).
     apply HCseq3 with (m := n);auto. rewrite H3;reflexivity.
     assert(eqA a a0). apply HCseq3 with (m := n);auto. rewrite H3;symmetry;auto.
     destruct H2. assert(eqA a a0). apply HCseq3 with (m := n);auto. rewrite <-H3.
     auto. assert(eqA a a0). apply HCseq3 with (m := n);auto. rewrite He0.
     rewrite <-H3. auto.
Qed.
Lemma well_dis : forall {A X : Type} {eqX : relation X} {eqA : relation A} 
  {leX : relation X} {plusX : X -> X -> X} {x0 : X} {pfX : Plus_Field eqX leX plusX x0} 
       {dist : A -> A -> X} {M : Metric eqX eqA leX plusX x0 pfX dist}
           (Pa Pb : @prj_nat A),
              Equivalence eqX -> Equivalence eqA -> @well_seq A eqA Pa
                  -> @well_seq A eqA Pb -> @well_seq X eqX (distseq Pa Pb).
Proof.
    intros. split.
    -intros. destruct H1. destruct H2. destruct HCseq1 with (n := n) as [a].
      destruct HCseq0 with (n := n) as [b]. exists(dist a b).
      apply dit with (a0 := a) (b0 := b);auto. reflexivity.
    -intros. destruct H4. apply dit with (a0 := a) (b0 := b);auto. rewrite <-H3;auto.
    -intros. destruct H3. destruct H4. rewrite He, He0. assert (eqA a a0). destruct H1.
     apply HCseq3 with (m:= n);auto. assert(eqA b b0). destruct H2.
     apply HCseq3 with (m:=n);auto. rewrite H3. rewrite H4. reflexivity.
Qed. 

Section plus_pre.
Variables X : Type.
Variables eqX : relation X.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables x0 : X.
Variables HE : Equivalence eqX.
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.
Variables mof : Plus_Field eqX leX plusX x0.
Variables dist : A -> A -> X.
Variables M : Metric eqX eqA leX plusX _ mof dist.
Variables leA : relation A.
Variables plusA : A -> A -> A.
Variables x0A : A.
Variables HPA : Plus_Field eqA leA plusA x0A.
        (**This Plus_Field is sometimes the same as the mof**)
Variables Dpd : Density eqX mof.
Notation "a + b" := (plusA a b)
  (at level 50, left associativity).
Notation "a <= b" := (leX a b)
  (at level 70, no associativity).
Notation "a >= b" := (leX b a)
  (at level 70, no associativity).
Variables HPD : forall (a b c : A), eqX (dist (a + b) (a + c)) (dist b c).
Variables HIN : forall a b, eqX (dist a b) (dist (inv a) (inv b)).

Notation "a == b" := (eqX a b)
    (at level 70, no associativity).
Notation "a != b" := (~eqX a b)
    (at level 70, no associativity).

Theorem plus_trans : forall {Pa Pb : @prj_nat A},
    CauchySeq eqX eqA Pa -> CauchySeq eqX eqA Pb
        -> CauchySeq eqX eqA (@dibasic A eqA leA plusA _ HPA Pa Pb).
Proof.
    intros. split. apply well_dibasic. auto. destruct H. apply HWS. destruct H0.
    apply HWS.
    intros. destruct H. destruct H0.
    destruct division_of_eps with (X := X) (eqX := eqX) (H := mof) (eps := eps) as [eps1].
    auto. auto. auto. destruct H as [eps2]. destruct H as [Heps1 [Heps2 Heq]].
    destruct HCA with (eps := eps1) as [N1]. auto.
    destruct HCA0 with (eps := eps2) as [N2]. auto.
    destruct (always_greater N1 N2) as [G]. destruct H2. exists G. intros. destruct H5.
    destruct H5. destruct H6. rewrite He. rewrite He0.
    assert(plusX (dist (a + b0) (a + b)) (dist (a + b) (a0 + b)) >= dist (a + b0) (a0 + b)).
    apply mtr. assert(dist (a + b0) (a + b) == dist b0 b). rewrite HPD. reflexivity.
    assert(dist (a + b) (a0 + b) == dist a a0). rewrite (pfc a _). rewrite (pfc a0 _).
    rewrite HPD. reflexivity. rewrite H7 in H5. rewrite H6 in H5.
    assert (dist b0 b < eps2). apply H0 with (m := n0) (n := n). destruct H4. 
    split. apply (lt_trans _ G _). auto. auto. apply (lt_trans _ G _). auto. auto.
    split. auto. auto.
    assert(dist a a0 < eps1). apply H with (m := n0) (n := n). destruct H4. split.
    apply (lt_trans _ G _). auto. auto. apply (lt_trans _ G _). auto. auto.
    split. auto. auto.
    assert (plusX (dist b0 b) (dist a a0) < plusX eps2 eps1). apply lt_two_plus_two;auto.
    rewrite (pfc eps2 _) in H10. rewrite Heq in H10.
    destruct (le_lt_eq X eqX _ ((dist (plusA a b0) (plusA a0 b))) (plusX (dist b0 b) (dist a a0)) ).
    apply H11 in H5. destruct H5. apply lttr with (y := plusX (dist b0 b) (dist a a0));auto.
    rewrite H5;auto.
Qed.

Theorem inv_trans : forall (P : @prj_nat A),
                CauchySeq eqX eqA P -> CauchySeq eqX eqA (invseq P).
Proof.
    intros. split. destruct H. apply well_inv; auto.
    intros. destruct H. destruct HCA with (eps := eps) as [N];auto.
    exists N. intros. destruct H2. destruct H2. destruct H3. rewrite <-HIN.
    apply H with (m := n0) (n := n). auto. split;auto. rewrite He.
    rewrite <-HIN. apply H with (m := n0) (n := n);auto. rewrite He.
    destruct H3. rewrite <- HIN. apply H with (m := n0) (n := n); auto.
    rewrite He0. rewrite <-HIN. apply H with (m := n0) (n := n); auto.
Qed.
End plus_pre.
Inductive ball {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
        {dist : X -> X -> X}
        {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqX _ _ _ mof dist} {HE : Equivalence eqX} 
    (a : X) (r : X) (x : X): Prop :=
    | ball_intro (L : x0 < r) (H : dist a x < r) : ball a r x.

Class PropBucket {X : Type} {eqX : relation X} {leX : relation X} {plusX : X -> X -> X} {x0 : X}
                {dist : X -> X -> X}
                {mof : Plus_Field eqX leX plusX x0} {M : Metric eqX eqX _ _ _ mof dist}
                {HE : Equivalence eqX} :={
          inBall1 :  forall (a x eps y : X), ball a eps x -> ~ball a eps y -> a < y -> x < y ;
          inBall2 : forall (a x eps y : X), ball a eps x -> ~ball a eps y -> y < a -> y < x;
          orderPres1 : forall (a b c : X), a < b -> a < c -> dist a b < dist a c -> b < c;
          orderPres2 : forall (a b c : X), a < b -> a < c -> b < c -> dist a b < dist a c;
}.
Section dist_pre.
Variables X : Type.
Variables eqX : relation X.
Variables leX : relation X.
Variables plusX : X -> X -> X.
Variables x0 : X.
Variables HE : Equivalence eqX.
Variables A : Type.
Variables eqA : relation A.
Variables HEA : Equivalence eqA.
Variables pfX : Plus_Field eqX leX plusX x0.
Variables dist : A -> A -> X.
Variables distX : X -> X -> X.
Variables MX : Metric eqX eqX leX plusX _ pfX distX.
Variables M : Metric eqX eqA leX plusX _ pfX dist.
Variables Dpd : Density eqX pfX.
Variables HPD : forall (a b c : X),
    eqX (distX (plusX a b) (plusX a c)) (distX b c).
Variable BP :PropBucket.
(*Variables HDD : forall (a b c : A), eqX (distX (dist a b) (dist a c)) (dist b c). *)
Variable HDD_pre : forall (x : X), leX x0 x -> eqX (distX x0 x) x.
Lemma HDD_l_pre : forall (a b c : X), leX x0 a -> leX x0 b -> leX x0 c ->
                                 leX c (plusX a b) -> leX a (plusX b c) ->
                                 leX (distX a c) b.
Proof.
  intros. destruct (poor a c).
  -rewrite <-(HDD_pre b).
   assert (eqX (distX x0 b) (distX a (plusX a b))).
   assert (eqX a (plusX a x0)).
   rewrite pfc, pfz;reflexivity.
   assert (eqX (distX a (plusX a b)) (distX (plusX a x0) (plusX a b))).
   rewrite <-H5;reflexivity.
   rewrite H6, HPD;reflexivity.
   rewrite H5.
   assert (leX a (plusX a b)).
   pose proof (lt_div X eqX _ leX plusX x0 a b (plusX a b)).
   apply (le_lt_eq X eqX leX x0 a) in H.
   destruct H.
   apply (le_lt_eq X eqX leX x0 b) in H0.
   destruct H0.
   apply H6;[reflexivity|auto|auto].
   rewrite <-H0, pfc, pfz; apply pofr;reflexivity.
   rewrite <-H, pfz;auto.
   apply (le_lt_eq X eqX leX c (plusX a b)) in H2.
   destruct H2.
   apply (le_lt_eq X eqX leX a c) in H4.
   destruct H4.
   apply (le_lt_eq X eqX leX a (plusX a b)) in H6.
   destruct H6.
   pose proof (orderPres2 a c (plusX a b)).
   destruct H7;auto.
   rewrite H6 in H4.
   destruct (lt_not_and X eqX leX c (plusX a b)).
   split;auto.
   rewrite H4.
   assert (eqX x0 (distX c c)). symmetry.
   apply (mre c c);reflexivity.
   rewrite <-H7. apply mle.
   rewrite H2. apply pofr;reflexivity.
   auto.
   -rewrite <-(HDD_pre b).
   assert (eqX (distX x0 b) (distX c (plusX c b))).
   assert (eqX c (plusX c x0)).
   rewrite pfc, pfz;reflexivity.
   assert (eqX (distX c (plusX c b)) (distX (plusX c x0) (plusX c b))).
   rewrite <-H5;reflexivity.
   rewrite H6, HPD;reflexivity.
   rewrite H5.
   assert (leX c (plusX c b)).
   pose proof (lt_div X eqX _ leX plusX x0 c b (plusX c b)).
   apply (le_lt_eq X eqX leX x0 c) in H1.
   destruct H1.
   apply (le_lt_eq X eqX leX x0 b) in H0.
   destruct H0.
   apply H6;[reflexivity|auto|auto].
   rewrite <-H0, pfc, pfz; apply pofr;reflexivity.
   rewrite <-H1, pfz;auto.
   apply (le_lt_eq X eqX leX a (plusX b c)) in H3.
   destruct H3.
   apply (le_lt_eq X eqX leX c a) in H4.
   destruct H4.
   apply (le_lt_eq X eqX leX c (plusX c b)) in H6.
   destruct H6.
   pose proof (orderPres2 c a (plusX c b)).
   destruct H7;[auto|auto|rewrite pfc;auto|auto].
   rewrite (msy a c). exact ltle.
   rewrite H6 in H4. rewrite pfc in H4.
   destruct (lt_not_and X eqX leX a (plusX b c)).
   split;auto.
   rewrite H4.
   assert (eqX x0 (distX a a)). symmetry.
   apply (mre a a);reflexivity.
   rewrite <-H7. apply mle.
   rewrite H3, (msy _ c), (pfc b _). apply pofr;reflexivity.
   auto.
Qed.   
   
Lemma HDD_l : forall (a b c : A), leX (distX (dist a b) (dist a c)) (dist b c).
Proof.
  intros.
  apply HDD_l_pre.
  apply mle.
  apply mle.
  apply mle.
  apply mtr.
  repeat (rewrite (msy a _)).
  apply mtr.
Qed.  
Notation "a + b" := (plusX a b)
  (at level 50, left associativity).
Notation "a <= b" := (leX a b)
  (at level 70, no associativity).
Notation "a >= b" := (leX b a)
  (at level 70, no associativity).
Notation "a == b" := (eqX a b)
    (at level 70, no associativity).
Notation "a != b" := (~eqX a b)
    (at level 70, no associativity).

Theorem dist_trans : forall {Pa Pb : @prj_nat A},
    CauchySeq eqX eqA Pa -> CauchySeq eqX eqA Pb
        -> CauchySeq eqX eqX (@distseq A X eqX eqA leX plusX x0 pfX dist M Pa Pb).
Proof.
    intros. split.
    -apply well_dis;auto. destruct H;auto. destruct H0;auto.
    -intros. 
      destruct (division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
      destruct H. destruct HCA with (eps := eps1) as [N1];auto. destruct H0.
      destruct HCA0 with (eps := eps2) as [N2];auto. destruct(always_greater N1 N2) as [G].
      exists G. intros. destruct H4. destruct H4. destruct H5. rewrite He.
      rewrite He0. 
      assert(distX (dist a b0) (dist a0 b) <= distX (dist a b0) (dist a b) + distX (dist a b) (dist a0 b)). 
      apply mtr. specialize (HDD_l a b b0).
      specialize (HDD_l b a a0). intros.
      rewrite (msy b a), (msy b a0) in H5.
      assert (distX (dist a b0) (dist a b) +
              distX (dist a b) (dist a0 b) <= dist b b0 + dist a a0).
      apply le_two_plus_two with (eqX := eqX) (x0 := x0);auto.
      rewrite (msy (dist a b0) _);auto.
      assert (distX (dist a b0) (dist a0 b) <= dist b b0 + dist a a0).
      apply (poft _ _ _ H4 H7).
      assert(dist b0 b < eps2). apply H0 with (m := n0) (n := n).
      destruct H2, H3. split;apply (lt_trans _ G _);auto. split;auto.
      assert(dist a a0 < eps1). apply H with (m := n0) (n := n).
      destruct H2, H3. split;apply (lt_trans _ G _);auto. split;auto.
      assert(dist b0 b + dist a a0 < eps2 + eps1). apply lt_two_plus_two;auto.
      rewrite (pfc eps2 _),Heq in H11. destruct (le_lt_eq _ _ _ (distX (dist a b0) (dist b a0)) (dist b0 b + dist a a0)).
      rewrite (msy a0 b), (msy b b0) in H8.
      apply H12 in H8. destruct H8.
          +apply lttr with (y := dist b0 b + dist a a0);auto. rewrite (msy a0 b);auto.
          +rewrite (msy a0 b);rewrite H8;auto.
Qed.
End dist_pre.
