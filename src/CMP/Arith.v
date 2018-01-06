Require Import PeanoNat.

Lemma leq_and_not: forall x y, x <= S y -> x = S y \/ x <= y.
Proof.
  intro x.
  case x.
  + right.
    exact (le_0_n _).
  + intros n y H.
    case (le_S_n _ _ H).
    - left.
      reflexivity.
    - right.
      apply le_n_S.
      assumption.
Qed.

Lemma leq_and_not': forall x y, x <= S y -> x <> S y -> x <= y.
Proof.
  intros x y H.
  case (leq_and_not _ _ H).
  - contradiction.
  - intros.
    assumption.
Qed.

Lemma leq_and_not'': forall x y, x <= y -> x <> y -> x <= pred y.
Proof.
  intro x.
  induction y.
  - intros H H0.
    pose (p := proj1 (Nat.le_0_r x) H).
    contradiction.
  - apply leq_and_not'.
Qed.

Lemma le_sub: forall n x y, n + x <= y -> n <= y - x.
Proof.
  intros n x y H.
  assert (x <= y) as H0.
  - pose (p := Nat.add_le_mono 0 n x x (le_0_n _) (le_n _)).
    Nat.order.
  - assert (y = y - x + x) as H1.
    + symmetry.
      exact (Nat.sub_add x y H0).
    + rewrite H1 in H.
      rewrite (Nat.add_comm n x) in H.
      rewrite (Nat.add_comm (y - x) x) in H.
      exact (proj2 (Nat.add_le_mono_l n (y-x) x) H).
Qed.

Lemma le_sub_ident: forall n x y, n + x <= y -> y = y - x + x.
Proof.
  intros n x y H.
  assert (x <= y) as H0.
  - pose (p := Nat.add_le_mono 0 n x x (le_0_n _) (le_n _)).
    Nat.order.
  - symmetry.
    exact (Nat.sub_add x y H0).
Qed.
