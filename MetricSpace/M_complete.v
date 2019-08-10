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
Instance distCA_rewrite : Proper (equCA ==> equCA ==> equCX) distCA.
Proof.
  apply (dist_rewrite _ _ equCX leCX plusCX zeroCX equCA _ _ pfCX _).
  apply MC.
Defined.
Instance distCX_rewrite : Proper (equCX ==> equCX ==> equCX) distCX.
Proof.
  apply (dist_rewrite _ _ equCX leCX plusCX zeroCX equCX _ _ pfCX _).
  apply MCX.
Defined.  

Definition CCA : Type :=@Cauchilize CA CX equCX equCA leCX plusCX zeroCX distCA pfCX MC.
Definition equCCA :CCA -> CCA -> Prop :=
    @equC CA CX equCX equCA leCX plusCX zeroCX distCA pfCX MC.

Definition lt_prop (a : CX) (b : CX) : Prop :=
    match a, b with
    | con_intro _ _ _ _ _ _ cseq1 _, con_intro _ _ _ _ _ _ cseq2 _ =>
    (exists (N : nat), forall (n : nat) (a1 a2 : X), (N < n)%nat -> cseq1 n a1
             -> cseq2 n a2 -> a1 < a2)
    end.

Lemma lt_lt_prop : forall (a b : CX), ltCX a b -> lt_prop a b.
Proof.
  intros. destruct H. destruct a. destruct b. simpl. simpl in ltle. simpl in lteq.
        destruct ltle. destruct lteq. apply H1. destruct H1 as [N].
        exists N. intros. destruct (H1 n a1 a2 H2 H3 H4). apply lt_intro;auto.
Qed.

Lemma lt_plus : forall (a b c d : X), a < b -> c < d -> a + c < b + d.
Proof.
  intros. pose proof (lt_two_plus_two X eqX _ leX plusX _ a c b d). destruct H1.
  apply lt_intro;apply H. apply lt_intro;apply H0.
  apply lt_intro;auto.
Qed.

Lemma le_or : forall (a b : X), a <= b -> a < b \/ eqX a b.
Proof.
  intros. pose proof (le_lt_eq X eqX _ a b). apply H0 in H. auto.
Qed.

Lemma lt_t : forall (a b c : X), a < b -> b < c -> a < c.
Proof.
  intros. pose proof (lttr X eqX _ leX a b c). apply H1;auto.
Qed.

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


Variable eq_prj : forall (x1 x2 x1' x2' : X) (Heq1 : eqX x1 x1') (Heq2 : eqX x2 x2')
   (H : x1 < x2) (H' : x1' < x2'),
   eqX (proj1_sig (pd_strong x1 x2 H)) (proj1_sig (pd_strong x1' x2' H')).

Definition pairX := prod X X.

Definition division_of_eps_strong : forall (eps : X),  zeroX < eps ->
  {pr : pairX | zeroX < (fst pr) /\ zeroX < (snd pr) /\ eqX ((fst pr) + (snd pr)) eps}.
Proof.
  intros. destruct (pd_strong zeroX eps) as [x H1]. auto. destruct H1.
    destruct (pfi_strong x) as [x']. exists (pair x (eps + x')). split. auto. split.
    destruct (@HpOt X eqX _ leX plusX zeroX _  x eps x').
    apply lt_intro;destruct H1;auto.
    assert(eps + x' > x + x'). apply lt_intro;auto.
    rewrite e in H2. auto. simpl. rewrite (pfc eps x').
    rewrite <-pfa. rewrite e. rewrite pfz. reflexivity.
Defined.
Definition eqXp (px1 px2 : pairX) : Prop := (eqX (fst px1) (fst px2)) /\
                                         (eqX (snd px1) (snd px2)).
Lemma eq_div_eps_strong :
  forall (eps1 eps2 : X) (H1 : zeroX < eps1) (H2 : zeroX < eps2),
    eqX eps1 eps2 ->
    eqXp (proj1_sig (division_of_eps_strong eps1 H1))
         (proj1_sig (division_of_eps_strong eps2 H2)).
Proof.
  intros. unfold division_of_eps_strong.
  specialize (eq_prj zeroX eps1 zeroX eps2 ltac:(reflexivity) H H1 H2) .
  destruct (pd_strong zeroX eps1 H1), (pd_strong zeroX eps2 H2).
  destruct a, a0. destruct (pfi_strong x), (pfi_strong x0).
  simpl. simpl in eq_prj. unfold eqXp.
  split;simpl;auto. assert (eqX x1 x2).
  rewrite eq_prj in e. rewrite <-e0 in e.
  assert (eqX (x2 + x0 + x1) (x2 + x0 + x2)).
  rewrite pfa,pfa. rewrite e. reflexivity.
  rewrite pfc in e0. rewrite e0 in H0. rewrite pfz, pfz in H0.
  auto. rewrite H0. rewrite H. reflexivity.
Qed.
  
Variables poor_strong :  forall (a b : X), {a <= b} + {b <= a}.
(**The succ has to make the same division for all the equivalence class of a**)
Definition succ (a : X) (H : a > zeroX) : X.
  destruct (division_of_eps_strong  a). auto. destruct x as [eps1 eps2]. simpl in a0.
  destruct a0 as [Heps1 [Heps2 Hepseq]]. destruct (poor_strong eps1 eps2).
  apply eps1. apply eps2.
Defined.
Definition succ' (a :{a : X | a > zeroX}) : X := succ (proj1_sig a) (proj2_sig a).
Definition eqX' (a b : {a : X | a  > zeroX}) : Prop := eqX (proj1_sig a) (proj1_sig b).
Lemma succ_proper :
  forall (a b : X) (H1 : a > zeroX) (H2 : b > zeroX), eqX a b ->
               eqX (succ a H1) (succ b H2).
Proof.
  intros. unfold succ. pose proof eq_div_eps_strong.
  specialize (H0 a b H1 H2 H).
  destruct (division_of_eps_strong a H1), (division_of_eps_strong b H2).
  simpl. simpl in H0. destruct a0 as [? [? ?]].
  destruct a1 as [? [? ?]]. destruct x, x0.
  simpl in l, l0, e, l1, l2, e0, H0.
  unfold eqXp in H0. simpl in H0. destruct H0 as [? ?].
  destruct (poor_strong x x1). destruct (poor_strong x0 x2).
  auto. rewrite <-H3. apply pore. auto. rewrite H0, H3;auto.
  destruct (poor_strong x0 x2). rewrite H3.
  apply pore. rewrite <-H0, <-H3. auto. auto.
  auto.
Qed.

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
   +pose proof succ_proper.
    specialize (H7 a0 a3 IHg IHg0 H6).
    auto.
   +rewrite H7 in Heq. rewrite Heq in Heq0. auto.
Qed.

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

Definition appropriate (a b : @prj_nat A) : Prop :=
  forall (n: nat) (x y : A), a n x -> b n y -> eqA x y.
Class select_function (f : CA -> @prj_nat A -> Prop) :Prop:=
  {
    sfe : forall (a b : CA) (x y : @prj_nat A),
      equCA a b -> f a x -> f b y -> appropriate x y;
    sfs : forall (a : CA), exists (x : @prj_nat A), f a x;
    sfi1 : forall (a : CA) (x y : @prj_nat A),
        appropriate x y -> f a x -> f a y;
    sfi2 : forall (a b : CA) (x : @prj_nat A),
        equCA a b -> f a x -> f b x;
    sfc : forall (a : CA) (x : @prj_nat A),
        f a x -> CauchySeq eqX eqA x;
    sfp : forall (a : CA) (x : @prj_nat A) (H : f a x),
        equCA a (con_intro _ _ _ _ _ _ x (sfc a x H));
                                                 }.
Variable sf :CA -> @prj_nat A -> Prop.
Variable sfs_f : select_function sf.
Instance sf_ins : select_function sf.
apply sfs_f.
Defined.

Definition bound_prop (seq : @prj_nat A) (n : nat) (eps : X) : Prop :=
  forall (j k : nat) (a b : A), (j > n)%nat -> (k > n)%nat -> seq j a -> seq k b ->
    dist a b < eps.

Definition not_bound_prop (seq : @prj_nat A) (n : nat) (eps : X) : Prop :=
  exists (j k : nat) (a b : A) (H1 : (j > n)%nat) (H2 : (k > n)%nat)
    (H3 : seq j a) (H4 : seq k b), dist a b >= eps.

Lemma bp_not_bp : forall (seq : @prj_nat A) (n : nat) (eps : X),
    bound_prop seq n eps <-> not(not_bound_prop seq n eps).
Proof.
  intros. split.
  -intros. unfold bound_prop in H. unfold not_bound_prop.
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros. 
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros.
   apply all_not_not_ex. intros.
   assert (dist n2 n3 < eps).
   specialize (H n0 n1 n2 n3 n4 n5 n6 n7).
   apply lt_intro;apply H.
   unfold not. intros. assert (not(eps > dist n2 n3)).
   apply lt_not;auto. apply H2. auto.
  -intros. unfold not_bound_prop in H.
   unfold bound_prop. intros.
   apply not_ex_all_not with (n := j) in H.
   apply not_ex_all_not with (n := k) in H.
   apply not_ex_all_not with (n := a) in H.
   apply not_ex_all_not with (n := b) in H.
   apply not_ex_all_not with (n := H0) in H.
   apply not_ex_all_not with (n := H1) in H.
   apply not_ex_all_not with (n := H2) in H.
   apply not_ex_all_not with (n := H3) in H.
   pose proof not_iff_compat. pose proof lt_not.
   specialize (H5 X eqX _ leX _ (dist a b) (eps)).
   apply H4 in H5. assert(~ ~ eps > dist a b).
   apply H5. apply H. apply NNPP in H6.
   apply lt_intro;apply H6.
Qed.   

Lemma partial_bound_tr1 : forall (seq : @prj_nat A) (eps : X)
                           (HC : CauchySeq eqX eqA seq) (n m : nat)
                           (Hb : bound_prop seq n eps),
    (m >= n)%nat -> bound_prop seq m eps.
Proof.
  intros. unfold bound_prop in Hb. unfold bound_prop.
  intros. apply (Hb j k);[omega| omega| auto| auto].
Qed.
Lemma partial_bound_tr2 : forall (seq : @prj_nat A) (eps : X)
                           (HC : CauchySeq eqX eqA seq) (n m : nat)
                           (Hb : not_bound_prop seq n eps),
    (m <= n)%nat -> not_bound_prop seq m eps.
Proof.
  intros. unfold not_bound_prop in Hb. unfold not_bound_prop.
  destruct Hb as [j [k [a [b [? [? [? [? ?]]]]]]]].
  exists j, k, a, b. assert (j > m)%nat. omega.
  assert (k > m)%nat. omega.
  exists H1, H2, x1, x2. auto.
Qed.

Theorem fst_nCauchy_ext : forall (seq : @prj_nat A) (eps : X)
                            (HC : CauchySeq eqX eqA seq)
                            (He : eps > zeroX),
    exists! (n : nat),
      (bound_prop seq n eps) /\ (forall (m : nat), (m < n)%nat -> not_bound_prop seq m eps).
Proof.
  intros. destruct (HCA eps) as [n1]. apply lt_intro; apply He.
  pose proof dec_inh_nat_subset_has_unique_least_element.
  pose proof classic.
  specialize (H0 (fun (n : nat) => bound_prop seq n eps)).
  destruct H0. intros. apply H1. exists n1. unfold bound_prop.
  intros. destruct H with (m := j) (n := k) (a := a) (b := b).
  split;auto. split;auto. apply lt_intro;auto.
  exists x. split. split.
  unfold unique in H0. destruct H0. apply H0.
  intros m H2. unfold unique in H0. destruct H0.
  apply NNPP. unfold not. intros. apply bp_not_bp in H4.
  specialize (H3 m). assert (x = m).
  apply H3. split. destruct H0. auto. destruct H0.
  intros. assert (x <= x')%nat.
  apply H5. auto. omega.
  assert ((m < x)%nat -> m <> x). omega.
  apply H6 in H2. apply H2. symmetry. auto.
  intros. destruct H0. apply H3. split.
  destruct H2. auto. intros. destruct H2.
  apply NNPP. unfold not. intros. apply not_le in H6.
  apply H5 in H6. apply bp_not_bp in H6.
  auto. auto.
Qed.

Definition fst_nCauchy (seq : @prj_nat A) (n : nat) (eps : X):Prop:=
  (bound_prop seq n eps) /\ (forall (m : nat), (m < n)%nat -> not_bound_prop seq m eps).
Definition snd_nCauchy (seq : @prj_nat A)(n : nat)(eps : X)(a : A)(H:seq n a):Prop:=
  forall (n1 : nat) (a1 : A), seq n1 a1 -> (n1 > n)%nat -> dist a a1 < eps.
Lemma fst_snd_prop :
  forall (seq : @prj_nat A) (n : nat) (eps : X) (a : A) (H : seq (S n) a),
    fst_nCauchy seq n eps -> snd_nCauchy seq (S n) eps a H.
Proof.
  intros. unfold snd_nCauchy. intros. destruct H0. unfold bound_prop in H0.
  specialize (H0 (S n) n1 a a1). destruct H0;auto. omega.
  apply lt_intro;auto.
Qed.

Lemma Select_CA : forall (x x' : X) (Hb : x > zeroX) (Cseq : @prj_nat A) (H : CauchySeq eqX eqA Cseq) (m : nat), 
    zeroSeq x Hb m x' ->
        (exists! (n : nat),fst_nCauchy Cseq n x') .
Proof.
  intros. pose proof fst_nCauchy_ext. unfold fst_nCauchy. apply H1.
  auto. apply (zeroSeq_nonzero x x' Hb m);auto.
Qed.

Lemma appro_eq_eqX : forall (seq1 seq2 : @prj_nat A) (n1 n2 : nat) (eps1 eps2 : X)
                       (H1:CauchySeq eqX eqA seq1) (H2:CauchySeq eqX eqA seq2),
    appropriate seq1 seq2 -> eqX eps1 eps2 -> eps1 > zeroX ->
    eps2 > zeroX-> fst_nCauchy seq1 n1 eps1 -> fst_nCauchy seq2 n2 eps2 -> n1 = n2.
Proof.
  intros. pose proof fst_nCauchy_ext.
  specialize (fst_nCauchy_ext seq2 eps2 H2 H4).
  specialize (fst_nCauchy_ext seq1 eps1 H1 H3).
  intros. destruct H8 as [n]. destruct H9 as [n0].
  assert (n1 = n). destruct H8. symmetry. apply H10.
  auto. assert (n2 = n0). destruct H9. symmetry. apply H11.
  auto. rewrite H10, H11. destruct H8. apply H12.
  split.
  -unfold bound_prop. intros. specialize (HCseq1 j).
   specialize (HCseq1 k). intros. destruct H17 as [b0].
   destruct H18 as [a0]. assert (eqA a a0). apply (H j a a0);auto.
   assert (eqA b b0). apply (H k b b0);auto. rewrite H19, H20.
   rewrite H0.  destruct H9. destruct H9. unfold bound_prop in H9.
   apply (H9 j k a0 b0 H13 H14 H18 H17).
  -intros. unfold not_bound_prop. destruct H9.
   destruct H9. specialize (H15 m H13). unfold not_bound_prop in H15.
   destruct H15 as [j [k [a [b [? [? [? ?]]]]]]].
   exists j, k, a, b, x, x0. assert (seq1 j a).
   destruct H1. specialize (HCseq1 j).
   specialize (HCseq1 k). intros. destruct H1 as [b0].
   destruct H15. destruct H16 as [a0].
   assert (eqA a a0). symmetry. pose proof (H j a0 a).
   apply H17;auto. destruct HWS. apply HCseq2 with (a1 := a0).
   symmetry. auto. auto. exists H16. destruct H15.
   assert (seq1 k b). destruct H1. specialize (HCseq1 k) as [b0].
   apply HCseq2 with (a1 := b0). apply (H k);auto. auto.
   exists H17. rewrite H0. auto.
Qed.




Inductive approxSeq (CCseq : @prj_nat CA) (x : X) (Hb : x > zeroX) : nat -> A -> Prop :=
| aps (n n1 : nat) (Cseq : @prj_nat A) (t : CA) (a aeq: A) (x1 : X)
      (H : zeroSeq x Hb n x1) 
    (H1 : CCseq n t)(Hsf : sf t Cseq) (H2 : Cseq (S n1) a) (HeqA : eqA a aeq)
        (H3 : fst_nCauchy Cseq n1 x1) : approxSeq CCseq x Hb n aeq.
(*n1 is certain, hence the (S n1) is the very same nat of each Equivalent class*)
Lemma approxSeq_well : forall (CCseq : @prj_nat CA)
    (HCC : @CauchySeq CA CX equCX equCA leCX plusCX zeroCX pfCX distCA MC CCseq)
     (x : X) (Hb : x > zeroX), @well_seq A eqA (approxSeq CCseq x Hb).
Proof.
  intros. split.
  -intros. pose proof Select_CA. pose proof (HCseq1 n) as [p].
   pose proof (zeroSeq_well x Hb). pose proof (HCseq1 n) as [x1].
   pose proof sfs. specialize (H3 p) as [Cseq].
   specialize (H x x1 Hb Cseq (sfc p Cseq H3) n H2) as [n1 ?].
   destruct H. pose proof (sfc p Cseq H3). assert (exists a, Cseq (S n1) a).
   apply H5. destruct H6 as [a].
   exists a.
   apply aps with (n := n) (n1 := n1) (x1 := x1) (Cseq := Cseq) (a := a)
                  (t := con_intro eqX eqA leX plusX zeroX dist Cseq (sfc p Cseq H3)).
   auto. pose proof (sfp p Cseq H3). apply HCseq2 with (a1 := p).
   auto. auto. pose proof sfi2.
   apply (H7 p _ Cseq). apply sfp. auto. auto.
   reflexivity. auto.
  -intros. destruct H0.
   apply aps with (n1 := n1) (Cseq := Cseq)(a := a) (x1 := x1) (t := t).
   auto. auto. auto. auto.
   rewrite <-H. auto. auto.
  -intros. destruct H, H0. assert (equCA t t0).
   apply HCseq3 with (m := n);auto. assert (appropriate Cseq Cseq0).
   apply (sfe t t0);auto. assert (n0 = n1). assert (eqX x1 x0).
   pose proof (zeroSeq_well x Hb). apply HCseq3 with (m := n);auto.
   symmetry. apply (appro_eq_eqX Cseq Cseq0 _ _ x1 x0);auto.
   apply (sfc t Cseq);auto. apply (sfc t0 Cseq0);auto.
   apply (zeroSeq_nonzero x x1 Hb n); auto.
   apply (zeroSeq_nonzero x x0 Hb n); auto.
   rewrite H9 in H5. rewrite <-HeqA, <-HeqA0.
   apply (H8 (S n1));auto.
Qed.   


Definition sig_X_CX (x : X) : CX :=@sig_inv X X eqX eqX leX plusX zeroX distX pfX MX _ _ x.

Lemma distC_dist_fixed : forall (cq1 cq2 : @prj_nat A) (HC1 : CauchySeq _ _ cq1) (HC2 : CauchySeq _ _ cq2)
  (x y z : X) (a1 a2 : A) (N1 N2 : nat),
    x > zeroX ->ltCX (distCA (con_intro _ _ _ _ _ _ cq1 HC1) (con_intro _ _ _ _ _ _ cq2 HC2)) (sig_X_CX x) -> cq1 N1 a1 -> cq2 N2 a2
          -> (forall (n1 : nat) (a3 : A), (n1 > N1)%nat -> cq1 n1 a3 -> dist a3 a1 < y)
          -> (forall (n2 : nat) (a4 : A), (n2 > N2)%nat -> cq2 n2 a4 -> dist a4 a2 < z)
          -> dist a1 a2 <= x + y + z.
Proof.
  intros. apply lt_lt_prop in H0. simpl in H0. destruct H0 as [N].
  destruct(always_greater N1 N2) as [G1]. destruct H5. destruct(always_greater G1 N) as [G].
  destruct H7. assert(exists a , distseq cq1 cq2 G a). pose proof(well_dis cq1 cq2 _ _ _ _) as [?].
  apply HCseq1. destruct H9 as [a]. destruct (H0 G a x);auto. apply sig.
  destruct H9. assert(dist a b < x). rewrite<-He. apply lt_intro;auto.
  assert(dist a1 a < y). destruct (H3 n a). apply (lt_trans _ G1 _);auto. auto. rewrite msy. apply lt_intro;auto.
  assert(dist a2 b < z). destruct (H4 n b). apply (lt_trans _ G1 _);auto. auto. rewrite msy. apply lt_intro;auto.
  assert(dist a1 a2 <=dist a1 a + dist a b + dist b a2). assert(dist a1 b <= dist a1 a + dist a b). apply mtr.
  assert(dist a1 a2 <= dist a1 b + dist b a2). apply mtr. apply (poft _ (dist a1 b + dist b a2) _). auto.
  apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto. apply pofr;reflexivity.
  assert(dist a1 a + dist a b + dist b a2 < x + y + z). assert(dist a1 a + dist a b < x + y).
  rewrite (pfc x _). apply lt_plus;auto. apply lt_plus;auto. rewrite msy;auto. apply le_or in H12.
  destruct H12. apply (lt_t _ (dist a1 a + dist a b + dist b a2) _);auto. rewrite H12;auto. apply H13.
Qed.
Theorem approxSeq_Cauchy : forall (CCseq : @prj_nat CA) 
 (H0 : @CauchySeq CA CX equCX equCA leCX plusCX zeroCX pfCX distCA MC CCseq)
 (x : X) (Hb : x > zeroX), 
    CauchySeq eqX eqA (approxSeq CCseq x Hb).
Proof.
  intros. split.
  -apply approxSeq_well. auto.
  -intros. destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Hepseq]]]];auto.
   destruct H0. destruct HCA with (eps := sig_inv eps1) as [N1]. apply lt_intro.
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
   apply (H16 Cseq Cseq0 (sfc t Cseq Hsf) (sfc t0 Cseq0 Hsf0) eps1 epsex epsex a a0 (S n1) (S n2)). apply lt_intro;apply Heps1. 
   destruct H0 with (m := n0) (n := n) (a := t) (b := t0). split;apply (lt_trans _ G _);auto.
   split;auto. 
   assert (equCA t (con_intro eqX eqA leX plusX zeroX dist Cseq
                              (sfc t Cseq Hsf))). apply sfp.
   assert (equCA t0 (con_intro eqX eqA leX plusX zeroX dist Cseq0
                               (sfc t0 Cseq0 Hsf0))). apply sfp.
   rewrite <-H17. rewrite <-H18.
   apply lt_intro;auto.
   auto. auto. intros.
   assert (forall (n2 : nat) (a1 : A),
              Cseq n2 a1 ->(n2 > S n1)%nat -> x1 > dist a a1).
   pose proof fst_snd_prop. unfold snd_nCauchy in H19.
   apply H19;auto.
   destruct (H19 n3 a3). auto. auto.
   apply lttr with (y := x1);auto. rewrite msy. apply lt_intro;auto. intros.
   assert(forall (n3 : nat) (a1 : A),
             Cseq0 n3 a1 -> (n3 > S n2)%nat -> x0 > dist a0 a1).
   pose proof fst_snd_prop. unfold snd_nCauchy in H19.
   apply H19;auto.
   destruct (H19 n3 a4);auto. apply lttr with (y := x0);auto. rewrite msy. apply lt_intro;auto.
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

Definition approx (CCseq : @prj_nat CA) (HCC : CauchySeq _ _ CCseq) (x : X) (Hb : x > zeroX) : CA :=
  con_intro _ _ _ _ _ _ (approxSeq CCseq x Hb) (approxSeq_Cauchy CCseq HCC x Hb).

Lemma less_sig : forall (epsC : CX), ltCX zeroCX epsC 
      -> (exists eps : X, ltCX zeroCX (sig_inv eps) /\ ltCX (sig_inv eps) epsC).
Proof.
  intros. destruct H. destruct epsC. simpl in ltle. simpl in lteq.
  destruct ltle. apply lteq in H0. destruct H0. destruct H0 as [N1].
  apply not_all_ex_not in lteq. destruct lteq as [eps]. apply not_all_ex_not in H1. destruct H1 as [H2].
  destruct(division_of_eps _ _ _ _ _ _ eps) as [eps1 [eps2 [Heps1 [Heps2 Heq]]]];auto.
  destruct(division_of_eps _ _ _ _ _ _ eps1) as [epsex1 [epsex2 [Hex1 [Hex2 Hexeq]]]];auto.
  destruct H. destruct HCA with (eps := epsex1) as [N3];auto.
  destruct(always_greater N1 N3) as [N2[? ?]].
  apply not_ex_all_not with (n := N2) in H1. apply not_all_ex_not in H1. destruct H1 as [N4].
  apply not_all_ex_not in H1. destruct H1 as [H5]. apply not_all_ex_not in H1. destruct H1 as [a1].
  apply not_all_ex_not in H1 as [a2]. apply not_all_ex_not in H1 as [H6]. apply not_all_ex_not in H1 as[H7].
  apply lt_not in H1. assert(eqX a1 zeroX). pose proof (@well_sig X eqX zeroX _). destruct H8.
  apply HCseq3 with (m := N4);auto. apply sig. rewrite H8 in H1. rewrite distX_eq_strong in H1.
   exists eps2.
  split. split. simpl. right. exists 0. intros. assert(eqX a0 zeroX).
  pose proof (@well_sig X eqX zeroX _). destruct H12. 
  apply(HCseq3 n a0 zeroX);auto. apply sig. assert(eqX a3 eps2).
  pose proof (@well_sig X eqX eps2 _). destruct H13.
  apply (HCseq3 n a3 eps2);auto. apply sig.
  rewrite H12, H13. auto. unfold not. intros.
  simpl in H9. assert(distX zeroX eps2 >= eps2). rewrite distX_eq_strong.
  apply pofr. reflexivity. destruct (H9 eps2) as [N]. auto.
  destruct H11 with (n := (S N)) (a1 :=  zeroX) (a2 := eps2). omega.
  apply sig. apply sig.
  assert(~(eps2 > distX zeroX eps2) /\ (eps2 > distX zeroX eps2)).
  split. apply lt_not;auto. apply lt_intro;auto.
  destruct H12. apply H12. auto. split. simpl. right.
  exists N2. intros. assert(eqX eps2 a0). pose proof (@well_sig _ _ eps2 _).
  destruct H12. apply (HCseq3 n);auto. apply sig. rewrite <-H12.
  destruct H with (m := n) (n := N4) (a := a3) (b := a2). split.
  apply (lt_trans _ N2 _);auto. apply (lt_trans _ N2 _);auto. split.
  auto. auto. assert(epsex1 > distX a3 a2). apply lt_intro;auto.
  assert(distX a2 zeroX >= eps). rewrite msy,distX_eq_strong.
  auto. destruct (pfi epsex1) as [iepsex1].
  assert(distX zeroX a3 + distX a3 a2 >= distX zeroX a2).
  apply mtr. destruct(pfi (distX a3 a2)) as [id32].
  assert(distX zeroX a3 + distX a3 a2 + id32 >=distX zeroX a2 + id32).
  apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto.
  apply pofr;reflexivity. rewrite pfa, H17,(pfc _ zeroX), pfz in H18.
  assert(id32 > iepsex1). 
  pose proof (lt_inv X eqX _ leX plusX zeroX (distX a3 a2) epsex1 id32 iepsex1). 
  destruct H19 ;auto. apply lt_intro;apply H13. apply lt_intro;auto.
  assert(distX zeroX a2 + id32 > eps + iepsex1). destruct (le_lt_eq _ _ _ eps (distX zeroX a2)).
  rewrite msy in H14. apply H20 in H14. destruct H14.
  pose proof (lt_two_plus_two X eqX _ leX plusX zeroX eps iepsex1 (distX zeroX a2) id32).
  destruct H22. apply lt_intro;apply H14. apply lt_intro;apply H19. apply lt_intro; auto.
  rewrite <-H14. rewrite pfc, (pfc eps _). pose proof (HpOt X eqX _ leX plusX _ iepsex1 id32 eps).
  destruct H22. apply lt_intro;apply H19. apply lt_intro;auto.
  rewrite <-Heq in H20. rewrite pfc, <-pfa, (pfc iepsex1 _), <-Hexeq in H20.
  rewrite (pfa epsex1 epsex2 iepsex1), (pfc epsex2),<-pfa, H15 ,pfz in H20.
  assert(distX zeroX a3 > epsex2 + eps2).
  pose proof (le_lt_eq X eqX leX (distX zeroX a2 + id32) (distX zeroX a3)). apply H21 in H18.
  destruct H18. apply lttr with (y := distX zeroX a2 + id32);auto.
  rewrite <-H18;apply lt_intro;apply H20. rewrite distX_eq_strong in H21.
  apply lttr with (y := epsex2 + eps2);auto.
  pose proof (lt_div X eqX _ leX plusX _ eps2 (epsex2) (epsex2 + eps2)). destruct H22.
  rewrite pfc;reflexivity. auto. auto. apply lt_intro;auto. apply lt_intro;apply H21.
  simpl. unfold not. intros.
  destruct H9 with (eps := epsex2) as [N];auto.
  destruct (always_greater N N2) as [G [? ?]]. destruct HWS. destruct (HCseq1 G) as [a3].
  destruct (@well_sig X eqX eps2);auto. destruct (HCseq0 G) as [a4].
  destruct H10 with (n := G) (a1 := a4) (a2 := a3);auto.
   assert(epsex2 > distX a4 a3). apply lt_intro;auto.
  destruct H with (m := N4) (n := G) (a := a2) (b := a3).
  split. apply (lt_trans _ N2 _);auto. apply (lt_trans _ N2 _);auto. split;auto.
  assert(epsex1 > distX a2 a3). apply lt_intro;auto. assert(distX a2 zeroX >= eps).
  rewrite msy, distX_eq_strong;auto. assert(eqX a4 eps2).
  pose proof (@well_sig X eqX eps2 _). destruct H18. apply HCseq8 with (m := G);auto.
  apply sig. rewrite H18 in H15. assert(distX eps2 a2 < eps1).
  assert(distX eps2 a2 <= distX eps2 a3 + distX a3 a2). apply mtr.
  rewrite (msy a3 _) in H19. assert(distX eps2 a3 + distX a2 a3 < eps1).
  rewrite <-Hexeq. rewrite pfc.
  pose proof (lt_two_plus_two X eqX _ leX plusX _ (distX a2 a3) (distX eps2 a3) epsex1 epsex2).
  destruct H20. apply lt_intro; apply H16. apply lt_intro; apply H15. apply lt_intro;auto.
  pose proof (le_lt_eq X eqX leX (distX eps2 a2) (distX eps2 a3 + distX a2 a3)).
  apply H21 in H19. destruct H19. apply lttr with (y := distX eps2 a3 + distX a2 a3);auto.
  rewrite H19. auto. destruct(pfi eps1) as [ieps1]. destruct(pfi (distX eps2 a2)) as [id22].
  assert(ieps1 < id22). pose proof (lt_inv X eqX _ leX plusX _  (distX eps2 a2) eps1 id22 ieps1).
  destruct H22;auto. apply lt_intro;apply H19. apply lt_intro;auto.
  assert(distX eps2 zeroX + distX eps2 a2 >= distX a2 zeroX). rewrite pfc, (msy _ a2). apply mtr.
  assert(distX eps2 zeroX + distX eps2 a2 + id22 > distX a2 zeroX + ieps1).
  destruct (le_lt_eq _ _ _ (distX a2 zeroX) (distX eps2 zeroX + distX eps2 a2)).
  apply H24 in H23. destruct H23.
  destruct (lt_two_plus_two X eqX _ leX plusX _ (distX a2 zeroX) ieps1 (distX eps2 zeroX + distX eps2 a2) id22). 
  apply lt_intro;apply H23. apply lt_intro;apply H22. apply lt_intro;auto.
  rewrite <-H23. rewrite (pfc (distX a2 zeroX) _),(pfc (distX a2 zeroX) _).
  pose proof (@HpOt X eqX _ leX plusX _ _ ieps1 id22 (distX a2 zeroX)). destruct H26.
  apply lt_intro;apply H22. apply lt_intro;auto. rewrite pfa , H21, (pfc _ zeroX), pfz in H24.
  assert(distX a2 zeroX + ieps1 >= eps + ieps1).
  apply le_two_plus_two with (eqX := eqX) (x0 := zeroX);auto. apply pofr;reflexivity.
  rewrite <-Heq in H25. rewrite (pfc eps1 _), pfa, H20, (pfc _ zeroX), pfz in H25.
  assert(distX eps2 zeroX > eps2). pose proof (le_lt_eq _ _ _ eps2 (distX a2 zeroX + ieps1)).
  apply H26 in H25. destruct H25. apply lttr with (y := distX a2 zeroX + ieps1);auto.
  rewrite <-H25 in H24;auto. rewrite msy, distX_eq_strong in H26.
  pose proof (ltre X eqX _ leX eps2). apply H27, H26. auto.
Qed.

Lemma ltCtr : forall (a b c : CX), ltCX a b -> ltCX b c -> ltCX a c.
Proof.
  apply lttr. unfold equCX. apply EquR_trans;auto.
Qed.

Lemma X_sig_X : forall (a b : X), a < b <-> ltCX (sig_inv a) (sig_inv b).
Proof.
  intros. split. 
  -split. simpl. right.
    exists 0. intros. assert(eqX a1 a). destruct (@well_sig X eqX a);auto.
    apply (HCseq3 n);auto. apply sig. assert(eqX a2 b). destruct(@well_sig X eqX b);auto.
    apply (HCseq3 n);auto. apply sig. rewrite H3, H4. apply lt_intro;apply H.
    unfold not. intros. simpl in H0. destruct(H0 (distX a b)). split. apply mle.
    unfold not. intros. assert(~eqX a b). destruct H. auto. apply H2. symmetry in H1.
    apply mre in H1. auto. destruct H1 with (n := (S x)) (a1 := a) (a2 := b). omega.
    apply sig. apply sig. apply lteq. reflexivity.
  -intros. apply lt_lt_prop in H. simpl in H. destruct H as [N]. destruct H with (n := S N) (a1 := a) (a2 := b).
  omega. apply sig. apply sig. apply lt_intro;auto.
Qed.


Theorem Complete : forall (r : CCA), (exists (p : CA), 
        equCCA (sig_C_CC p) r).
Proof.
  destruct(classic (exists a : X, (~eqX a zeroX))).
  -apply greater_ext in H. destruct H as [x Hb]. intros. destruct r as [CCseq HCC].
   exists(approx CCseq HCC x Hb).
    simpl. intros. destruct (less_sig eps) as [eps0 [Heps0 Heps1]]. split; apply H.
    unfold ltCX in Heps0. unfold ltCX in Heps1. assert(eps0 > zeroX).
    apply X_sig_X in Heps0. auto.
    destruct(division_of_eps _ _ _ _ _ _ eps0) as [eps1 [eps2 [Heps2 [Heps3 Hepseq]]]];auto.
    apply lt_intro;apply H0. pose proof (zeroSeq_lesseps x eps1 Hb).
    destruct H1 as [N1]. apply lt_intro;apply Heps2.
    pose proof (approxSeq_Cauchy CCseq _ x Hb).
    destruct H2. destruct (HCA eps2) as [N2]. auto. destruct (always_greater N1 N2) as [G [? ?]].
    exists G. intros. assert(leCX (distCA a1 a2) (sig_inv eps0)).
      +
          assert(equCA a1 (approx CCseq HCC x Hb)). pose proof (@well_sig CA equCA (approx CCseq HCC x Hb) _).
          destruct H8. apply (HCseq3 n). auto. apply sig. rewrite H8.
          assert(exists t, approxSeq CCseq x Hb n t). pose proof(@approxSeq_well CCseq _ x Hb).
          destruct H9. apply HCseq1. destruct H9. assert(approxSeq CCseq x Hb n x0) as Hv. apply H9. 
          destruct H9.
          assert (CauchySeq eqX eqA Cseq) as HC. apply (sfc t);auto.
          assert(leCX (distCA (approx CCseq HCC x Hb) (con_intro eqX eqA leX plusX zeroX dist Cseq HC)) (sig_inv eps0)).
          simpl. right. destruct(always_greater n (S n1)) as [G2 [? ?]].
          exists G2. intros. assert(eqX a3 eps0). destruct H17; [reflexivity| symmetry; auto]. rewrite H18.
          destruct H16. rewrite He. assert(dist aeq a0 < eps2).
          destruct H2 with (m := n) (n := n0) (a := aeq) (b := a0). split;apply (lt_trans _ G _);auto.
          apply (lt_trans _ n _);auto. apply (lt_trans _ G2 _);auto. split;auto. apply lt_intro;auto.
          assert(dist a b < x1).
          assert (forall (n2 : nat) (a1 : A),
                     Cseq n2 a1 -> (n2 >S n1)%nat -> x1 > dist a a1).
          apply fst_snd_prop;auto.
          destruct (H19 n0 b). auto. apply (lt_trans _ G2 _);auto. apply lt_intro;auto.
          rewrite <-HeqA in H16. assert(x1 < eps1). apply (H1 n).
          apply (lt_trans _ G _);auto. auto. assert(dist a b < eps1). apply lttr with (y := x1);auto.
          assert(dist a b + dist a a0 < eps1 + eps2).
          pose proof (lt_two_plus_two X eqX _ leX plusX zeroX (dist a b) (dist a a0) (eps1) (eps2)).
          destruct H22. apply lt_intro; apply H21. apply lt_intro;apply H16. apply lt_intro;auto.
          rewrite Hepseq in H22. assert(dist a b + dist a a0 >= dist a0 b). rewrite (msy a a0), pfc.
          apply mtr. pose proof (le_lt_eq X eqX leX (dist a0 b) (dist a b + dist a a0)). apply H24 in H23.
          destruct H23. apply lttr with (y := dist a b + dist a a0);auto. apply lt_intro;apply H23.
          apply lt_intro;apply H22. rewrite H23. apply lt_intro;apply H22.
          assert(equCA (con_intro eqX eqA leX plusX zeroX dist Cseq HC) a2).
          destruct HCC. destruct HWS0. apply (HCseq3 n);auto.
          apply HCseq2 with (a1 := t). apply sfp;auto. auto.
          rewrite <-H14. auto.
       +apply (@le_lt_eq CX equCX leCX pofCX) in H8. destruct H8.
          pose proof ltCtr. unfold ltCX in H9. destruct(H9 (distCA a1 a2) (sig_inv eps0) eps).
          auto. auto. apply lt_intro;auto. rewrite H8. apply lt_intro;apply Heps1.
  -unfold not in H. intros. assert(forall a : X, eqX a zeroX).
    intros. apply not_ex_all_not with (n := a) in H. apply NNPP in H. auto.
    assert(forall p : CA,equCCA (sig_C_CC p) r). intros. destruct r. simpl. intros.
    assert(equCX eps zeroCX). destruct eps. simpl. intros. exists 0. intros.
    assert(eqX (distX a1 a2) zeroX). apply H0. rewrite H8;auto. destruct H2. destruct lteq.
    symmetry;auto.
    destruct r. assert(exists p : CA, Cseq 0 p). destruct H2. destruct HWS. apply HCseq1.
    destruct H3. exists x. apply H1.
Qed.
(**Up to now, we have proven that there is trivial projection from CA to CCA, 
     which means that for every r : CCA, there is an element p in CA has the 
     same "limit" as r, note that we havn't defined the process of limition, 
     hence we use the equivelent definition to show that the CCA is complete**)
End complete.
