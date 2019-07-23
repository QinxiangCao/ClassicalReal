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
Definition leCX : CX -> CX -> Prop :=@leC X eqX leX plusX _ _ pfX MX HE.
Variables PB : PropBucket.
Definition pofCX :Pre_Order_Field equCX leCX :=@preOrder_trans X eqX leX plusX _ HE pfX _ MX Dp PB.
Definition ltCX : CX -> CX -> Prop :=@lt CX equCX leCX pofCX.
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
Definition distCA : CA -> CA -> CX :=(@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDD).
Definition distCX : CX -> CX -> CX :=(@distC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDDX).
Definition MC : Metric equCX equCA leCX plusCX zeroCX pfCX distCA.
  apply ms_trans;auto.
Defined.
Definition MCX : Metric equCX equCX leCX plusCX zeroCX pfCX distCX.
  apply ms_trans_X;auto.
Defined.

Definition CCA : Type :=@Cauchilize CA CX equCX equCA leCX plusCX zeroCX distCA pfCX MC.
Definition equCCA :CCA -> CCA -> Prop :=
    @equC CA CX equCX equCA leCX plusCX zeroCX distCA pfCX MC.

Definition sig_C_CC : CA -> CCA.
  intros p.
  apply (@sig_inv CA CX equCX equCA leCX plusCX zeroCX distCA pfCX MC _ _ p).
Defined.

Fixpoint n_plus (n : nat) (x : X)  :=
  match n with
  | 0 => zeroX
  | S n' => x + (n_plus n' x)
  end.

Lemma n_plus_add1 : forall (m n : nat) (x : X), eqX (n_plus (m + n) x) ((n_plus m x) + (n_plus n x)).
Proof.
  intros. generalize dependent m. induction n.
  -intros. simpl. replace ((m + 0)%nat) with m. rewrite pfc, pfz. reflexivity. omega.
  -intros. simpl. replace ((m + S n)%nat) with (S (m + n)%nat). simpl. rewrite IHn.
    rewrite <-pfa, (pfc x _). rewrite <-pfa. reflexivity. omega.
Qed.

Lemma n_plus_add2 : forall (m : nat) (x1 x2 : X), eqX (n_plus m (x1 + x2)) ((n_plus m x1) + (n_plus m x2)).
Proof.
  intro m. induction m. intros. simpl. rewrite pfz. reflexivity.
  intros. simpl. rewrite IHm. rewrite <-pfa, <- pfa. assert(eqX (x1 + x2 + n_plus m x1) (x1 + n_plus m x1 + x2)).
  rewrite pfa. rewrite (pfc x2 _). rewrite <-pfa. reflexivity. rewrite H. reflexivity.
Qed.

Lemma n_plus_great : forall (m n : nat) (x : X), x > zeroX -> (m > n)%nat -> (n_plus m x) > (n_plus n x).
Proof.
  intros. generalize dependent n. induction m.
  -intros. inversion H0.
  -intros. simpl. assert((m >= n)%nat). omega.
    apply le_lt_or_eq in H1. 
    assert(x + n_plus m x > zeroX +  n_plus m x).
    destruct (HpOt X eqX _ leX plusX zeroX zeroX x (n_plus m x)).
    apply lt_intro;destruct H;auto. apply lt_intro;auto. rewrite pfz in H2.
    destruct H1.
    +apply lttr with (y := n_plus m x);auto.
    +rewrite H1. auto.
Qed.
  
Variables Archimedian : forall (x y : X), x > zeroX -> y > zeroX -> x < y
         -> (exists n : nat, n_plus n x > y).
Variables pd_strong : forall (x1 x2 : X), x1 < x2 -> {x3 : X | x1 < x3 /\  x3 < x2}.
Variables pd_strong_eqv : forall (x1 x2 : X), x1 < x2 ->
    (forall (y1 y2 : X), eqX y1 x1 -> eqX y2 x2 -> 
            {x3 : X | x1 < x3 /\  x3 < x2}).

Definition pairX := prod X X.

Theorem division_of_eps_strong : forall (eps : X),  zeroX < eps ->
  {pr : pairX | zeroX < (fst pr) /\ zeroX < (snd pr) /\ eqX ((fst pr) + (snd pr)) eps}.
Proof.
  intros. destruct (pd_strong zeroX eps) as [x H1]. auto. destruct H1.
    destruct (pfi_strong x) as [x']. exists (pair x (eps + x')). split. auto. split.
    destruct (@HpOt X eqX _ leX plusX zeroX _  x eps x').
    apply lt_intro;destruct H1;auto.
    assert(eps + x' > x + x'). apply lt_intro;auto.
    rewrite e in H2. auto. simpl. rewrite (pfc eps x').
    rewrite <-pfa. rewrite e. rewrite pfz. reflexivity.
Qed.

Variables poor_strong :  forall (a b : X), {a <= b} + {b <= a}.
(**The succ has to make the same division for all the equivalence class of a**)
Definition succ (a : X) (H : a > zeroX) : X.
  destruct (division_of_eps_strong  a). auto. destruct x as [eps1 eps2]. simpl in a0.
  destruct a0 as [Heps1 [Heps2 Hepseq]]. destruct (poor_strong eps1 eps2).
  apply eps1. apply eps2.
Defined.

Inductive zeroSeq (x : X) (H : x > zeroX) : nat -> X -> Prop :=
  | ini (x' : X) (Heq : eqX x x') : zeroSeq x H 0 x'
  | suc (n : nat) (a b : X) (IH : zeroSeq x H n a) (IHg : a > zeroX) (Heq : eqX (succ a IHg) b) : 
      zeroSeq x H (S n) b.

Lemma greater_ext : (exists a : X, (~eqX a zeroX)) ->(exists b : X, (b > zeroX)).
Proof.
  intros. destruct H. destruct(classic (x > zeroX)). exists x;auto.
  apply lt_not  in H0. pose proof (pfi x) as [ix]. exists ix.
  rewrite <-H1 in H. assert(~eqX (x + ix) (x + ix + ix)).
  pose proof (plus_same X eqX _ leX plusX zeroX). rewrite pfc. rewrite pfa.
  unfold not. intros. apply H2 in H3. unfold not in H. apply H. auto.
  assert(ix >= zeroX). rewrite <-H1. assert(ix >= ix). apply pofr;reflexivity.
  assert(zeroX + ix >= x + ix). apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto.
  rewrite pfz in H4. auto. apply lt_intro;auto. rewrite H1 in H2. rewrite pfz in H2. auto. auto.
Qed.

Lemma zeroSeq_nonzero : forall (a x: X) (H : a > zeroX) (n : nat) (Hs : zeroSeq a H n x),
    x > zeroX.
Proof.
  intros. inversion Hs. rewrite <-Heq. auto. rewrite <-Heq. unfold succ.
  destruct (division_of_eps_strong a0 IHg).
  destruct x0 as [eps1 eps2]. simpl in a1. destruct a1 as [Heps1 [Heps2 Hepseq]].
  destruct (poor_strong eps1 eps2);auto.
Qed.

Lemma zeroSeq_well : forall (a : X) (H : a > zeroX), (@well_seq X eqX (zeroSeq a H)).
Proof.
  intros. split. 
  -intros. induction n. exists a. apply ini. reflexivity.
    destruct IHn. pose proof (zeroSeq_nonzero a x H n H0).
    exists (succ x H1). apply suc with (a := x) (IHg := H1);auto. reflexivity.
  -intros. inversion H1. apply ini. rewrite Heq. auto.
    apply suc with (a := a0) (IHg := IHg);auto. rewrite <-H0. auto.
  -intro m. induction m. intros. inversion H0. inversion H1. rewrite <-Heq. auto.
    intros. inversion H0. inversion H1. assert(eqX a0 a3). apply IHm;auto.
    assert(eqX (succ a0 IHg) (succ a3 IHg0)). 
      +admit.
      +rewrite H7 in Heq. rewrite Heq in Heq0. auto.
Admitted.

Lemma succ_dual : forall (a x1 x2: X) (H : a > zeroX) (n1 n2 : nat) (Hs1 : zeroSeq a H n1 x1)
  (Hs2 : zeroSeq a H n2 x2),
    (n2 > n1)%nat -> x1 >= n_plus 2 x2.
Proof.
  intros. simpl. rewrite (pfc _ zeroX). rewrite pfz. 
  generalize dependent n1. generalize dependent x1. generalize dependent x2.
  induction n2. intros. inversion H0. intros.
  assert(forall (n : nat) (x y : X),zeroSeq a H n x -> zeroSeq a H (S n) y -> x >= y + y).
  -intros. inversion H2. rewrite <- Heq. unfold succ.
    destruct (division_of_eps_strong a0 IHg) as [pr [Heps1 [Heps2 Hepseq]]].
    destruct pr as [eps1 eps2]. simpl in Heps1,Heps2,Hepseq. 
    destruct(poor_strong eps1 eps2). assert(eqX x a0). pose proof (zeroSeq_well a H).
    apply HCseq3 with (m := n);auto. rewrite H5. rewrite <-Hepseq.
    apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto. apply pofr;reflexivity.
    assert(eqX x a0). pose proof (zeroSeq_well a H).
    apply HCseq3 with (m := n);auto. rewrite H5. rewrite <-Hepseq.
    apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto. apply pofr;reflexivity.
  -pose proof (zeroSeq_well a H). destruct HCseq1 with (n := n2).
    assert((n2 >= n1)%nat). apply lt_n_Sm_le;auto.
    apply le_lt_or_eq in H4. destruct H4. assert(x1 >= x + x).
    apply IHn2 with(x2 :=x) (n1 := n1) (x1 := x1);auto.
    assert(x >= x2 + x2). apply H1 with (n := n2);auto.
    assert(x1 >= x). assert(x + x >= x + zeroX).
    apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto. apply pofr. reflexivity.
    pose proof (zeroSeq_nonzero a x H n2 H3). destruct H7. auto. rewrite pfc in H7.
    rewrite pfz in H7. apply poft with (b := x + x);auto. apply poft with (b := x);auto.
    assert(eqX x x1). apply HCseq3 with (m := n1). rewrite H4. auto. auto.
    rewrite <-H5. apply H1 with (n := n2);auto.
Qed.

Lemma zeroSeq_lesseps : forall(a eps : X) (H : a > zeroX) (Hex : eps > zeroX),
      (exists (N : nat), (forall (n : nat)(x : X), (n > N)%nat -> zeroSeq a H n x -> x < eps)).
Proof.
  intros.
  assert(~~(exists (N : nat), (forall (n : nat)(x : X), (n > N)%nat -> zeroSeq a H n x -> x < eps))).
  unfold not. intro.
  assert(~(exists (N : nat), (forall (n : nat)(x : X), (n > N)%nat -> zeroSeq a H n x -> x < eps))
    -> forall (N : nat), (exists (n : nat) (x : X) ( H1 : (n > N)%nat) (H2 : zeroSeq a H n x), x >= eps)).
   -intros. apply not_ex_all_not with (n := N) in H1. apply not_all_ex_not in H1.
    destruct H1 as [n]. exists n. apply not_all_ex_not in H1. destruct H1 as [x]. exists x.
    apply not_all_ex_not in H1 as [H2]. apply not_all_ex_not in H1 as[H3].
    intros. apply lt_not in H1. exists H2. exists H3. auto. auto.
   -assert(forall (N : nat), (exists (n : nat) (x : X) (_ : (n > N)%nat) (_ : zeroSeq a H n x), x >= eps)).
    apply H1. unfold not. apply H0.
    assert(forall (n : nat) (x : X), zeroSeq a H n x -> x >= eps).
    intros. destruct H2 with (N := n) as [n'].
    destruct H4. destruct H4 as [H5]. destruct H4 as [H6].
    assert(x >= n_plus 2 x0). apply (succ_dual a x x0 H n n');auto.
    simpl in H7. rewrite (pfc x0 zeroX) in H7. rewrite pfz in H7.
    assert(x0 + x0 >= x0 + zeroX). apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto.
    apply pofr;reflexivity. pose proof zeroSeq_nonzero.
    destruct H8 with (a := a) (x := x0) (H := H) (n := n'). auto. auto. rewrite pfc in H8.
    rewrite pfz in H8. assert(x0 + x0 >= eps). apply poft with (b := x0);auto.
    apply poft with (b := x0 + x0);auto.
    assert(forall (n : nat), n_plus (2 ^ n) eps <= a). intros.
    pose proof (zeroSeq_well a H). assert(exists a1, zeroSeq a H n a1).
    apply HCseq1. destruct H5 as [a1]. assert(a1 >= eps).
    apply H3 with (n := n);auto.
    assert(forall (m : nat)(t am : X), am >= t -> zeroSeq a H m am -> a >= n_plus (2 ^ m) t).
    intro m. induction m.
      { intros. simpl. rewrite pfc,pfz. assert(eqX a am). apply HCseq3 with (m := 0);[apply ini|auto].
        reflexivity. rewrite H9;auto. }
      { intros. simpl. replace((2 ^ m + (2 ^ m + 0))%nat) with ((2 ^ m + 2 ^ m)%nat).
         rewrite n_plus_add1. pose proof HCseq1. destruct H9 with (n := m) as [a'].
         assert(a' >= n_plus 2 am). apply (succ_dual a a' am H m (S m));auto.
         simpl in H11. rewrite (pfc _ zeroX), pfz in H11. assert(am + am >= t + t).
         apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto.
         assert(a' >= t + t). apply poft with (b := am + am);auto. apply IHm in H13. rewrite n_plus_add2 in H13.
         apply H13. auto. omega. }
       { apply H7 with (am := a1). auto. auto. }
       { assert(forall n : nat, a >= n_plus n eps). intros. assert((2 ^ n > n)%nat).
          { apply Nat.pow_gt_lin_r. omega. }
          { assert(a >= n_plus (2 ^ n) eps). apply H4. assert(n_plus (2 ^ n) eps > n_plus n eps).
             apply n_plus_great;auto. destruct H7. apply poft with (b := n_plus (2 ^ n) eps);auto. }
          { pose proof Archimedian. destruct H6 with (x := eps) (y := a) as [n];auto.
             assert(a >= n_plus 2 eps). apply H5. simpl in H7. rewrite (pfc _ zeroX), pfz in H7.
             assert(eps + eps > zeroX + eps). pose proof (HpOt X eqX _ leX plusX zeroX zeroX eps eps).
             destruct H8. apply lt_intro;destruct Hex;auto. apply lt_intro;auto. rewrite pfz in H8.
             destruct (le_lt_eq _ _ _ (eps + eps) a). apply H9 in H7. destruct H7.
             apply lttr with (y := eps + eps);auto. rewrite <-H7;auto. assert(n_plus n eps > a /\ ~(n_plus n eps > a)).
             split. auto. apply lt_not;auto. apply PNP in H8. destruct H8. } }
  -apply NNPP in H0. apply H0.
Qed.

Variables distX_eq_strong : forall (x : X), eqX (distX zeroX x) x.

Lemma always_smaller : forall (a b : X), a > zeroX -> b > zeroX -> exists c, (c < a /\ c < b/\ c > zeroX).
Proof.
  intros. destruct(classic (a <= b)).
  destruct(division_of_eps _ _ _ _ _ _ a) as [eps1[eps2 [Heps1[Heps2 Heq]]]];auto.
  apply lt_intro;destruct H;auto. exists eps1. assert(a > eps1). 
  pose proof (lt_div X eqX _ leX plusX zeroX). destruct H2 with (a := eps1) (b := eps2) (c := a);auto.
  apply lt_intro;auto. split. auto. pose proof (le_lt_eq X eqX _ a b). apply H3 in H1.
  destruct H1. split. apply lttr with (y := a);auto. apply lt_intro;apply Heps1. rewrite <-H1. split. auto.
  apply lt_intro;apply Heps1.
  assert(~~b < a). unfold not. intros. apply lt_not in H2. apply H1. auto. auto.
  apply NNPP in H2.
  destruct(division_of_eps _ _ _ _ _ _ b) as [eps1[eps2 [Heps1[Heps2 Heq]]]];auto.
  apply lt_intro;destruct H0;auto. exists eps1. assert(b > eps1).
  pose proof (lt_div X eqX _ leX plusX zeroX). destruct H3 with (a := eps1) (b := eps2) (c := b);auto.
  apply lt_intro;auto. split. apply lttr with (y := b);auto. split;auto. apply lt_intro;apply Heps1.
Qed.

Theorem zeroSeq_Cauchy :forall (a : X) (H : a > zeroX), CauchySeq eqX eqX (zeroSeq a H).
Proof.
  intros. split. apply zeroSeq_well.
  intros. pose proof zeroSeq_lesseps.
  destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
  destruct(always_smaller eps1 eps2) as [s];auto. apply lt_intro;destruct Heps1;auto.
  apply lt_intro;apply Heps2. destruct H2. destruct H3.
  destruct H1 with (a := a) (eps := s) (H := H) as [N];auto. exists N.
  intros. destruct H6. assert(distX a0 b <= distX a0 zeroX + distX zeroX b). apply mtr.
  rewrite (msy a0 zeroX) in H9. rewrite distX_eq_strong,distX_eq_strong in H9.
  assert(a0 + b < s + s). pose proof (lt_two_plus_two X eqX _ _ _ _). destruct H7.
  destruct (H10 a0 b s s). apply lt_intro; destruct (H5 m a0);auto.
  apply lt_intro; destruct (H5 n b);auto. apply lt_intro;auto.
  assert(s + s < eps1 + eps2). pose proof (lt_two_plus_two X eqX _ _ _ _).
  destruct (H11 s s eps1 eps2). apply lt_intro;apply H2. apply lt_intro;apply H3.
  apply lt_intro;auto. rewrite Heq in H11. apply lttr with (y := s + s);auto.
  pose proof (le_lt_eq X eqX _ (distX a0 b) (a0 + b)). apply H12 in H9. destruct H9.
  apply lttr with (y := a0 + b);auto. apply lt_intro;apply H9. apply lt_intro;apply H10.
  rewrite H9;apply lt_intro;apply H10. apply lt_intro;apply H11.
Qed.

Definition zeroN (a : X) (H : a > zeroX) : CX.
  pose proof (zeroSeq_Cauchy a H). apply (con_intro _ _ _ _ _ _ (zeroSeq a H) H0).
Defined.

Theorem zeroSeq_eqzero : forall (a : X) (H : a > zeroX), equCX (zeroN a H) zeroCX.
Proof.
  intros. simpl. intros. pose proof (zeroSeq_lesseps a eps H).
  destruct H1 as [N]. apply lt_intro;apply H0. exists N. intros. assert(eqX zeroX a2).
  destruct H4. reflexivity. auto. rewrite <-H5. rewrite msy, distX_eq_strong.
  destruct (H1 n a1);auto. apply lt_intro;auto.
Qed.
(**up to now, we have constructed a sequence, which is equivalent to zeroX while each
     a_n is greater than zeroX. Meanwhile, we have proved that this sequence exists if there
     is at least one elements x in X s.t. ~eqX x zeroX**)
Definition Sq (p : CA) :@prj_nat A.
  destruct p. apply Cseq.
Defined.
Lemma Select_CA : forall (x x' : X) (H : x > zeroX) (p : CA) (m : nat), zeroSeq x H m x' ->
    (exists (n0 : nat) (a0 : A) (H : Sq p n0 a0), (forall (n : nat) (a : A), Sq p n a -> (n > n0)%nat ->  dist a a0 < x')).
Proof.
  intros. destruct p. simpl. pose proof HCA. destruct H2 with (eps := x') as [N].
  pose proof (zeroSeq_nonzero x x' H m). apply H3 in H0. apply lt_intro;apply H0.
  exists (S N). pose proof HCseq1. destruct H4 with (n := S N). exists x0. exists H5.
  intros. destruct H3 with (m := (S N)) (n := n) (a := x0) (b := a). split. omega. omega.
  split;auto. apply lt_intro;auto. rewrite msy;auto. rewrite msy. auto.
Qed.
Definition cSq (r : CCA) :@prj_nat CA.
  destruct r. apply Cseq.
Defined.

Inductive approxSeq (r : CCA) (x : X) (Hb : x > zeroX) : nat -> A -> Prop :=
  | aps (n n1 : nat) (p : CA) (a aeq: A) (x1 : X) (H : zeroSeq x Hb n x1) (H1 : cSq r n p) (H2 : Sq p n1 a) (HeqA : eqA a aeq)
     (H3 : forall (n2 : nat) (a1 : A), Sq p n2 a1 -> (n2 > n1)%nat -> dist a a1< x1) : approxSeq r x Hb n aeq.

Lemma approxSeq_well : forall (r : CCA) (x : X) (Hb : x > zeroX), @well_seq A eqA (approxSeq r x Hb).
Proof.
  intros. split.
  -intros. pose proof Select_CA. destruct r. pose proof (HCseq1 n) as [p].
   pose proof (zeroSeq_well x Hb). pose proof (HCseq1 n) as [x1].
   destruct (H x x1 Hb p n) as [n1]. auto. destruct H4 as [a]. destruct H4 as [H1_]. exists a.
   apply aps with (n := n) (n1 := n1) (x1 := x1) (p := p) (a := a). auto. simpl. auto. auto. reflexivity.
   intros. rewrite msy. destruct (H4 n2 a1);auto. apply lt_intro;auto.
  -intros. destruct H0. apply aps with (n1 := n1) (p := p) (a := a) (x1 := x1). auto. auto. auto.
   rewrite <-H. auto. intros. apply (H3 n2);auto.
  -intros. destruct H. destruct H0. rewrite <-HeqA. rewrite <-HeqA0.
    assert(equCA p p0). destruct r. destruct H7. destruct HWS. apply (HCseq3 n);auto.
    admit.
Admitted.

Definition sig_X_CX (x : X) : CX :=@sig_inv X X eqX eqX leX plusX zeroX distX pfX MX _ _ x.

Lemma distC_dist : forall (c1 c2 : CA) (x y z : X) (N1 N2 : nat), x > zeroX ->ltCX (distCA c1 c2) (sig_X_CX x) 
    -> (forall (n1 n2 : nat) (a1 a2 : A),(n1 > N1)%nat -> (n2 > N1)%nat
                     -> Sq c1 n1 a1 -> Sq c1 n2 a2 -> dist a1 a2 < y)
    -> (forall (n3 n4 : nat) (a3 a4 : A),(n3 > N2)%nat -> (n4 > N2)%nat
                     -> Sq c2 n3 a3 -> Sq c2 n4 a4 -> dist a3 a4 < z)
    -> (forall (n : nat) (a5 a6 : A), (n > (max N1 N2))%nat 
                     -> Sq c1 n a5 -> Sq c2 n a6 -> dist a5 a6 <= x + y + z ).
Proof.
  intros.
Admitted.

Lemma distC_dist_fixed : forall (c1 c2 : CA) (x y z : X) (a1 a2 : A) (N1 N2 : nat),
    x > zeroX ->ltCX (distCA c1 c2) (sig_X_CX x) -> Sq c1 N1 a1 -> Sq c2 N2 a2
          -> (forall (n1 : nat) (a3 : A), (n1 > N1)%nat -> Sq c1 n1 a3 -> dist a3 a1 < y)
          -> (forall (n2 : nat) (a4 : A), (n2 > N2)%nat -> Sq c2 n2 a4 -> dist a4 a2 < z)
          -> dist a1 a2 <= x + y + z.
Proof.
  intros.
Admitted.

Theorem approxSeq_Cauchy : forall (r : CCA) (x : X) (Hb : x > zeroX), CauchySeq eqX eqA (approxSeq r x Hb).
Proof.
  intros. split.
  -apply approxSeq_well.
  -intros. destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Hepseq]]]];auto.
   destruct r. destruct H0. destruct HCA with (eps := sig_inv eps1) as [N1]. apply lt_intro.
   simpl. right. exists 0. intros. destruct H1. destruct H2. auto. rewrite <-H1. auto.
   rewrite <-H1. destruct H2. auto. rewrite <-H2. auto. simpl. unfold not. intros.
   assert(distX eps1 zeroX >= eps1). apply pofr. rewrite msy, distX_eq_strong. reflexivity.
   destruct H0 with (eps := eps1) as [N]. auto. destruct H2 with (n := S N) (a1 := zeroX) (a2 := eps1).
   omega. apply sig. apply sig. assert(eps1 > distX zeroX eps1). apply lt_intro;auto.
   assert(~(eps1 > distX zeroX eps1)). apply lt_not;auto. rewrite msy in H1. auto. apply H4. apply H3.
   destruct(division_of_eps _ _ _ _ _ _  eps2) as [epsex1 [epsex2 [Hex1 [Hex2 Hexeq]]]];auto.
   destruct(always_smaller epsex1 epsex2) as [epsex[Heex1 [Heex2 Heex]]]. 
   apply lt_intro;apply Hex1. apply lt_intro;apply Hex2.
   pose proof (zeroSeq_lesseps x epsex Hb). destruct H1 as [N2]. apply lt_intro;apply Heex.
   destruct(always_greater N1 N2) as [G [H2 H3]]. exists G. intros. destruct H5.
   destruct H5. destruct H6. destruct H4. assert(x1 < epsex). apply (H1 n0 _). apply (lt_trans _ G _);auto.
   exact H5. assert(x0 < epsex). apply (H1 n _). apply (lt_trans _ G _);auto. exact H6. rewrite <-HeqA.
   rewrite <-HeqA0. assert(dist a a0 <= eps1 + epsex + epsex). pose proof distC_dist_fixed.
   apply (H16 p p0 eps1 epsex epsex a a0 n1 n2). apply lt_intro;apply Heps1. simpl in H7.
   simpl in H10.
   destruct H0 with (m := n0) (n := n) (a := p) (b := p0). split;apply (lt_trans _ G _);auto.
   split;auto. apply lt_intro;auto. auto. auto. intros. destruct (H9 n3 a3). auto. auto.
   apply lttr with (y := x1);auto. rewrite msy. apply lt_intro;auto. intros.
   destruct (H12 n3 a4);auto. apply lttr with (y := x0);auto. rewrite msy. apply lt_intro;auto.
   assert(epsex + epsex < eps2). rewrite <-Hexeq.
   pose proof (lt_two_plus_two X eqX _ leX plusX zeroX epsex epsex epsex1 epsex2).
   destruct H17. apply lt_intro;apply Heex1. apply lt_intro;apply Heex2. apply lt_intro;auto.
   assert(eps1 + epsex + epsex < eps1 + eps2). rewrite pfa, (pfc eps1 _),(pfc eps1 _).
   pose proof (HpOt X eqX _ leX plusX zeroX (epsex + epsex) eps2 eps1). destruct H18.
   apply lt_intro;apply H17. apply lt_intro;auto. rewrite Hepseq in H18.
   pose proof (le_lt_eq X eqX leX (dist a a0) (eps1 + epsex + epsex) ). destruct H19.
   apply H19 in H16. destruct H16.
   apply lttr with (y := eps1 + epsex + epsex);auto. apply lt_intro;apply H16.
   apply lt_intro;apply H18. rewrite H16. apply lt_intro;apply H18.
Qed.

Definition approx (r : CCA) (x : X) (Hb : x > zeroX) : CA :=
  con_intro _ _ _ _ _ _ (approxSeq r x Hb) (approxSeq_Cauchy r x Hb).

Theorem Complete : exists (f : CA -> CCA),(forall (r : CCA), (exists (p : CA), 
        equCCA (f p) r)).
Proof.
  destruct(classic (exists a : X, (~eqX a zeroX))).
  -apply greater_ext in H. destruct H as [x Hb]. exists sig_C_CC. intros. exists(approx r x Hb).
    simpl. destruct r. intros. 


