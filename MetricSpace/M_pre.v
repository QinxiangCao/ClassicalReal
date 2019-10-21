From CReal.MetricSpace Require Export M_pack.
Theorem PNP : forall p : Prop, ~(p /\ ~p) .
Proof.
  unfold not. intros. destruct H. apply H0 in H. apply H.
Qed.

Lemma le_one : forall (m n : nat), (m <= n)%nat \/ (n <= m)%nat.
Proof.
  intro m. induction m.
  -intros. left. induction n. apply le_n. apply le_S. apply IHn.
  -intros. destruct n. +right. apply le_0_n. +destruct IHm with (n := n).
  {left. apply le_n_S. auto. } {right. apply le_n_S. auto. }
Qed.

Lemma le_equ : forall (m n : nat), (m <= n)%nat -> (n <= m)%nat -> m = n.
Proof.
  intro m. induction m as [| m' IH]. -intros. destruct n. auto. inversion H0.
  -intros. destruct n. +inversion H. +apply le_S_n in H. apply le_S_n in H0.
    assert (m' = n). apply IH. apply H. apply H0. auto.
Qed.


Lemma always_greater : forall (m n : nat), exists N, (m < N)%nat /\ (n < N)%nat.
Proof.
    intro m. induction m. -intros. exists (S n).
    split. apply neq_0_lt. unfold not. intros. inversion H. unfold lt. apply le_n.
    -intros. destruct IHm with (n :=n) as [N']. destruct H. exists (S N').
    split. apply lt_n_S. auto. unfold lt. unfold lt in H0. apply (le_trans (S n) N' (S N')).
    auto. apply le_S. apply le_n.
Qed. 