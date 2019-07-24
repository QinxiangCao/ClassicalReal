Set Warnings "-notation-overridden,-parsing".
From Coq Require Import QArith.QArith_base.
From Coq Require Import QArith.Qabs.
From Coq Require Import QArith.Qminmax.
From Coq Require Import Logic.Classical.
From Coq Require Import micromega.Psatz.

Lemma Qabs_triangle_extend: forall (a b c:Q), Qabs (a - c) <=
   Qabs (a - b) + Qabs (b - c).
Proof. intros.
    assert (Heq: a - c == (a - b) + (b - c)) by ring.
    rewrite Heq.
    apply Qabs_triangle.
Qed.
Lemma eps_divide_2_positive: forall (eps:Q), 0 < eps -> eps * (1 # 2) > 0.
Proof. intros. unfold Qmult. unfold Qlt. simpl.
    rewrite <- Zmult_assoc. simpl. apply H.
Qed.

Lemma eps_divide_2M_positive: forall (eps M:Q), 0 < eps -> 0 < M -> eps * (1 # 2) *(/M) > 0.
Proof. intros.
  apply (Qmult_lt_r _ _ _ H0). rewrite Qmult_0_l.
  rewrite <- (Qmult_assoc (eps * (1 # 2))). rewrite (Qmult_comm _ M). rewrite Qmult_inv_r.
  rewrite Qmult_1_r. apply eps_divide_2_positive. apply H.
  intros contra. rewrite contra in H0. discriminate.
Qed.
Lemma Qabs_0: forall q, Qabs q == 0 -> q==0.
Proof. intros. assert (Qabs q <= 0) by lra.
apply Qabs_Qle_condition in H0. lra.
Qed.

Lemma Qnot_0_abs: forall (q:Q), ~(q==0) -> ~(Qabs q == 0).
Proof.
intros. intros contra. apply Qabs_0 in contra. contradiction. 
Qed.
Lemma Qabs_not_0: forall (q:Q),  ~(Qabs q == 0) -> ~(q==0).
Proof.
intros. intros contra. rewrite contra in H. apply H. reflexivity.
Qed.

Lemma Qlt_not_0: forall (q:Q), q>0 -> ~(q==0).
Proof. intros. lra.
Qed.
(* TODO: This lemma is weird. Usually, when one writes
[/q], there must be some restriction saying that q is not zero. *)
Lemma Qinv_not_0: forall(q:Q), ~(/q == 0) -> ~(q==0).
Proof. intros. intros C. rewrite C in H. apply H. reflexivity. Qed.

Lemma Qmult_lt_compat_trans_positive: forall a b c d, a >= 0 -> c > 0
  -> a < b -> c <= d -> a*c < b*d.
Proof. intros. nra. Qed.

Lemma Qmult_le_compat_nonneg: forall (a1 b1 a2 b2:Q), 0 <= a1 -> 0 <= b1 
  -> a1 <= a2 -> b1 <= b2 -> a1 * b1 <= a2 * b2.
Proof. intros. nra. Qed.

Lemma Qmult_lt_compat_nonneg: forall (a1 b1 a2 b2:Q), 0 <= a1 -> 0 <= b1 
  -> a1 < a2 -> b1 < b2 -> a1 * b1 < a2 * b2.
Proof. intros. nra. Qed.

Lemma Qopp_lt_compat : forall p q, p<q -> -q < -p.
Proof. intros. nra. Qed.

Lemma Qopp_le_compat_iff: forall p q, p<=q <-> -q <= -p.
Proof. intros. nra. Qed.

Lemma Qarchimedean : forall p q :Q, p > 0 -> exists n : Q, n*p>q.
Proof.
  intros. exists ((q*/p)+1)%Q.
  assert ((q * / p + 1) * p == q + p) by (field; lra).
  rewrite H0.
  lra.
Qed.

Fact Qdiv2 : forall x : Q, (x == ((x * / (2 # 1)) + (x * / (2 # 1))))%Q.
Proof.
  intros. assert( x == 0 \/~ x == 0)%Q. { apply classic. } destruct H.
  - rewrite H. reflexivity.
  - rewrite <- Qmult_plus_distr_r. rewrite <- Qmult_1_r.
    rewrite <- Qmult_assoc.
    rewrite Qmult_inj_l with (z := x).
    reflexivity. apply H.
Qed.

Fact Qdiv2_opp : forall x : Q, (- x == - (x * / (2 # 1)) + - (x * / (2 # 1)))%Q.
Proof.
  intros.
  rewrite <- Qplus_inj_l with (z:=(x / (2 # 1))).
  rewrite Qplus_assoc.
  rewrite Qplus_opp_r with (q:=(x / (2 # 1))). rewrite Qplus_0_l.
  rewrite <- Qplus_inj_l with (z:=(x / (2 # 1))).
  rewrite Qplus_assoc.
  rewrite Qplus_opp_r with (q:=(x / (2 # 1))).
  rewrite <- Qplus_inj_r with (z:=x).
  rewrite <- Qplus_assoc. rewrite (Qplus_comm (-x) x ).
  rewrite Qplus_opp_r with (q:=x).
  rewrite Qplus_0_l. rewrite Qplus_0_r.
  symmetry. apply Qdiv2.
Qed.

Fact Qdiv2_x_y : forall x y :Q, x>0 -> y>0 -> x / (2 # 1) * (y / (2 # 1)) <= x * y.
Proof.
  unfold Qdiv. intros. rewrite Qmult_assoc.
  rewrite (Qmult_comm x (/(2#1))).
  rewrite <- (Qmult_assoc (/(2#1)) x y).
  rewrite <- (Qmult_comm (x*y) (/(2#1))).
  rewrite <- (Qmult_assoc (x*y) (/(2#1)) (/(2#1)) ).
  rewrite (Qmult_comm x y). rewrite <- (Qmult_1_r (y*x)).
  rewrite <- (Qmult_assoc (y*x) 1 ((/(2#1)) *(/(2#1)))).
  apply Qlt_le_weak.
  rewrite Qmult_lt_l.
  { reflexivity. }
  { rewrite <- (Qmult_0_l x). apply (Qmult_lt_compat_r 0 y x).
  auto. auto. }
Qed.

Lemma Qmult_lt_compat : forall x y z t : Q,
0 <= x -> 0 <= z -> x < y -> z < t -> x * z < y * t .
Proof.
  intros. apply Qle_lt_trans with (y:= y*z).
  - apply Qmult_le_compat_r. apply Qlt_le_weak. auto. auto.
  - rewrite Qmult_comm. rewrite (Qmult_comm y t).
    apply Qmult_lt_compat_r.
    apply Qle_lt_trans with (y:=x). auto. auto. auto.
Qed.

Lemma Qplus_opp_assoc : forall x y : Q, (-(x + y)== - x + - y)%Q.
Proof.
  intros. rewrite <- Qplus_inj_l with (z:=(x+y)).
  rewrite Qplus_opp_r. rewrite (Qplus_comm x y).
  rewrite <- Qplus_assoc. rewrite (Qplus_assoc x (-x) (-y)).
  rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite Qplus_opp_r.
  reflexivity.
Qed.

Lemma Qdensity : forall p q : Q, p<q-> exists x : Q, p<x/\x<q.
Proof.
  intros. exists ((p+q)/(2#1)). split.
  - apply Qlt_shift_div_l. reflexivity.
    assert(p * (2 # 1)==p+p)%Q.
    { rewrite <- Qmult_inj_r with (z:=/(2#1)).
    { assert(p * (2 # 1) * / (2 # 1)==p)%Q.
    { apply Qdiv_mult_l. unfold not. intros. inversion H0. }
      rewrite H0. rewrite Qmult_plus_distr_l.
      rewrite <- Qdiv2. reflexivity. }
    { unfold not. intros. inversion H0. } }
    rewrite H0. rewrite Qplus_lt_r. auto.
  - apply Qlt_shift_div_r. reflexivity.
    assert(q * (2 # 1)==q+q)%Q.
    { rewrite <- Qmult_inj_r with (z:=/(2#1)).
    { assert(q * (2 # 1) * / (2 # 1)==q)%Q.
    { apply Qdiv_mult_l. unfold not. intros. inversion H0. }
      rewrite H0. rewrite Qmult_plus_distr_l.
      rewrite <- Qdiv2. reflexivity. }
    { unfold not. intros. inversion H0. } }
    rewrite H0. rewrite Qplus_lt_l. auto.
Qed.

Lemma Qlt_mult0 : forall x y : Q, 0 < x -> 0 < y -> 0 < x * y.
Proof.
  intros. rewrite <- (Qmult_0_r 0).
 apply Qmult_lt_compat; try apply Qle_refl;try auto.
Qed.

Lemma Qmult_le_compat_l: forall x y z : Q, x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros. rewrite Qmult_comm. rewrite (Qmult_comm z y). apply Qmult_le_compat_r. auto. auto.
Qed.

Lemma Qdiv_lt_P : forall x y : Q , x > 0 -> x < y -> /y < /x.
Proof.
  intros.
  assert(forall x y, x > 0 -> x < y -> / y < / x).
  { intros. assert(y0>0).
    { apply Qlt_trans with (y:=x0);auto. } apply Qlt_shift_inv_l;auto.
    rewrite <- (Qmult_inv_r y0). { rewrite Qmult_comm.
    apply Qmult_lt_compat_r with (z:=/y0);auto.
    apply Qinv_lt_0_compat;auto. } unfold not.
    intros. apply Qlt_not_eq in H3. destruct H3. symmetry;auto. } auto.
Qed.

Lemma Qdiv_le_P : forall x y : Q , x > 0 -> x <= y -> /y <= /x.
Proof.
  intros.
  assert(forall x y, x > 0 -> x <= y -> / y <= / x).
  { intros. assert(y0>0).
    { apply Qlt_le_trans with (y:=x0);auto. } apply Qle_shift_inv_l;auto.
    rewrite <- (Qmult_inv_r y0). { rewrite Qmult_comm.
    apply Qmult_le_compat_r with (z:=/y0);auto.
    apply Qinv_le_0_compat. apply Qlt_le_weak. auto. } unfold not.
    intros. apply Qlt_not_eq in H3. destruct H3. symmetry;auto. } auto.
Qed.

Lemma Qmult_opp_assoc : forall x y : Q, -x*-y==x*y.
Proof.
  intros.
  rewrite <- Qplus_inj_l with (z:=x*-y).
  rewrite <- Qmult_plus_distr_r. rewrite <- Qmult_plus_distr_l.
  rewrite Qplus_opp_r. rewrite Qplus_comm. rewrite Qplus_opp_r.
  rewrite Qmult_0_r. apply Qmult_0_l.
Qed.

Lemma Qinv_0_le_compat: forall a : Q, a < 0 -> / a <= 0.
Proof.
  intros. assert(~-a==0). apply Qopp_lt_compat in H.
  apply Qlt_not_0 in H. auto.
  pose proof Qlt_not_eq a 0 H.
  rewrite Qopp_le_compat_iff in *.
  assert(-/a==/-a). rewrite <- Qmult_inj_l with (z:=-a);auto.
  rewrite Qmult_inv_r;auto. rewrite Qmult_opp_assoc. rewrite Qmult_inv_r;auto.
  reflexivity. rewrite H2. apply Qopp_lt_compat in H.
  apply Qmult_le_l with (z:=-a). auto. rewrite Qmult_inv_r;auto.
  rewrite Qmult_0_r. apply Qlt_le_weak. reflexivity.
Qed.

Lemma Qmult_opp_assoc_l : forall x y : Q, -(x*y)==-x*y.
Proof.
  intros. 
  rewrite <- Qplus_inj_l with (z:=x*y).
  rewrite <- Qmult_plus_distr_l.
  rewrite Qplus_opp_r. rewrite Qplus_opp_r.
  rewrite Qmult_0_l. reflexivity.
Qed.

Lemma Qinv_opp : forall a:Q,(~a==0->-/a==/-a)%Q.
Proof.
  intros. assert(~-a==0)%Q. { hnf. intros. apply H.
  rewrite <- Qplus_inj_l with (z:=a) in H0. rewrite Qplus_opp_r in H0.
  rewrite Qplus_0_r in H0. rewrite H0. reflexivity. }
  rewrite <- Qmult_inj_l with (z:=-a);auto.
  rewrite Qmult_inv_r;auto. rewrite Qmult_opp_assoc. rewrite Qmult_inv_r;auto.
  reflexivity.
Qed.

Lemma Qdiv_le_N : forall x y : Q , 0 > y -> x <= y -> /y <= /x.
Proof.
  intros.
  assert(forall x y, 0 > y -> x <= y -> / y <= / x).
  { intros. assert(x0<0).
    { apply Qle_lt_trans with (y:=y0);auto. }
    rewrite Qopp_le_compat_iff in *.
    apply Qopp_lt_compat in H1. apply Qopp_lt_compat in H3.
    rewrite Qinv_opp. rewrite Qinv_opp. apply Qle_shift_inv_l;auto.
    rewrite <- (Qmult_inv_r (-x0)). { rewrite Qmult_comm.
    apply Qmult_le_compat_r with (z:=(/(-x0)));auto.
    apply Qinv_le_0_compat. apply Qlt_le_weak. auto. }
    unfold not. intros. apply Qlt_not_eq in H3. destruct H3. symmetry;auto.
    unfold not. intros. apply Qlt_not_eq in H1. destruct H1. rewrite H4. reflexivity.
    unfold not. intros. apply Qlt_not_eq in H3. destruct H3. rewrite H4. reflexivity. } auto.
Qed.

Lemma Qinv_0_lt_compat: forall a : Q, a < 0 -> / a < 0.
Proof.
  intros.
  pose proof Qlt_not_eq a 0 H.
  rewrite Qlt_minus_iff in *. rewrite Qplus_0_l in *. rewrite Qinv_opp;auto.
  apply Qinv_lt_0_compat. auto.
Qed.

Lemma Qdiv_lt_N : forall x y : Q , 0 > y -> x < y -> /y < /x.
Proof.
  intros.
  assert(forall x y, 0 > y -> x < y -> / y < / x).
  { intros. assert(x0<0).
    { apply Qlt_trans with (y:=y0);auto. }
    rewrite <- Qopp_involutive. rewrite <- (Qopp_involutive (/x0)).
    apply Qopp_lt_compat. apply Qopp_lt_compat in H1.
    apply Qopp_lt_compat in H2. apply Qopp_lt_compat in H3.
    rewrite Qinv_opp. rewrite Qinv_opp. apply Qlt_shift_inv_l;auto.
    rewrite <- (Qmult_inv_r (-x0)). { rewrite Qmult_comm.
    apply Qmult_lt_compat_r with (z:=(/(-x0)));auto.
    apply Qinv_lt_0_compat. auto. }
    unfold not. intros. apply Qlt_not_eq in H3. destruct H3. symmetry;auto.
    unfold not. intros. apply Qlt_not_eq in H1. destruct H1. rewrite H4. reflexivity.
    unfold not. intros. apply Qlt_not_eq in H3. destruct H3. rewrite H4. reflexivity. } auto.
Qed.

Lemma Qplus_le_lt_compat:forall x y z t, x<=y -> z<t -> x+z < y+t.
Proof. intros.
  rewrite (Qplus_comm x). rewrite (Qplus_comm y).
  apply Qplus_lt_le_compat.
  auto. auto.
Qed.

Lemma Qopp_Qlt_compat: forall p q, p<q -> -q < -p.
Proof. intros. apply (Qplus_lt_r _ _ (p+q)).
  rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
  rewrite Qplus_0_r. rewrite Qplus_comm.
  rewrite Qplus_assoc. rewrite (Qplus_comm _ p). rewrite Qplus_opp_r.
  rewrite Qplus_0_l. auto.
Qed.

Lemma Qle_lt_minus (a b c d:Q): a <= b -> c < d -> a - d < b - c.
Proof. intros.
  apply Qplus_le_lt_compat. auto. apply Qopp_Qlt_compat. auto.
Qed.


Lemma Qdiv_lt_compat (a b c :Q): c> 0 ->a < b ->  a/c < b/c.
Proof. intros. apply Qinv_lt_0_compat in H.
  apply (Qmult_lt_r _ _ _ H). auto.
Qed.


Lemma Qdiv_le_compat (a b c :Q):  c> 0 ->a <= b -> a/c <= b/c.
Proof. intros. apply Qinv_lt_0_compat in H.
  apply (Qmult_le_r _ _ _ H). auto.
Qed.


Lemma Qabs_Qlt_condition x y: Qabs x < y <-> -y < x /\ x < y.
Proof.
 split.
  split.
   rewrite <- (Qopp_opp x).
   apply Qopp_lt_compat.
   apply Qle_lt_trans with (Qabs (-x)).
   apply Qle_Qabs.
   now rewrite Qabs_opp.
  apply Qle_lt_trans with (Qabs x); auto using Qle_Qabs.
 intros (H,H').
 apply Qabs_case; trivial.
 intros. rewrite <- (Qopp_opp y). now apply Qopp_lt_compat.
Qed.


Lemma Qabs_diff_Qlt_condition:
  forall x y r : Q, Qabs (x - y) < r <-> (x - r < y /\ y < x + r)%Q.
Proof.
 intros. unfold Qminus.
 rewrite Qabs_Qlt_condition.
 rewrite <- (Qplus_lt_l (-r) (x+-y) (y+r)).
 rewrite <- (Qplus_lt_l (x+-y) r (y-r)).
 setoid_replace (-r + (y + r)) with y by ring.
 setoid_replace (r + (y - r)) with y by ring.
 setoid_replace (x + - y + (y + r)) with (x + r) by ring.
 setoid_replace (x + - y + (y - r)) with (x - r) by ring.
 intuition.
Qed.

Lemma max_lt_lub_l: forall n m p, (max n m < p -> n < p)%nat.
Proof. intros. apply (le_lt_trans _ (max n m)).
  apply Nat.le_max_l. auto.
Qed.

