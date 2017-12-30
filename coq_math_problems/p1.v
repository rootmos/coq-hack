(* https://coq-math-problems.github.io/Problem1/ *)

Definition decr (f: nat -> nat) := forall n, f (S n) <= f n.

Require Import PeanoNat.

Definition bounded_by (f: nat -> nat) (n: nat) := forall x, f x <= n.
Definition bounded (f: nat -> nat) := exists n, bounded_by f n.

Theorem decr_is_bounded: forall f, decr f -> bounded f.
Proof.
  intros.
  refine (ex_intro _ (f 0) _).
  unfold bounded_by.
  induction x.
  - exact (le_n (f 0)).
  - pose (p := H x).
    Nat.order.
Qed.

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

Theorem decr_estimate: forall f, decr f -> forall x y, x <= y -> f y <= f x.
Proof.
  intros f D x.
  induction y.
  + intro.
    rewrite (proj1 (Nat.le_0_r _) H).
    apply le_n.
  + intro.
    case (Nat.eq_dec x (S y)).
    - intro.
      rewrite e.
      apply le_n.
    - intro.
      pose (p := IHy (leq_and_not' _ _ H n)).
      pose (q := D y).
      Nat.order.
Qed.

Definition eventually_bounded_by_at (f: nat -> nat) (n: nat) (x: nat)
  := forall y, x <= y -> f y <= n.
Definition eventually_bounded_by (f: nat -> nat) (n: nat)
  := exists x, eventually_bounded_by_at f n x.
Definition eventually_bounded (f: nat -> nat)
  := exists n, eventually_bounded_by f n.

Theorem bounded_is_eventually_bounded: forall f, bounded f -> eventually_bounded f.
Proof.
  intros.
  destruct H as [b pb].
  refine (ex_intro _ b _).
  refine (ex_intro _ 0 _).
  unfold eventually_bounded_by_at.
  intros.
  exact (pb y).
Qed.

Definition valley (f: nat -> nat)(n x : nat) :=
  forall y, (x <= y) -> (y <= x+n) -> f y = f x.

Lemma eventually_bounded_by_0:
  forall f,
  eventually_bounded_by f 0 ->
  forall n, exists x, valley f n x.
Proof.
  intros.
  destruct H as [x px].
  refine (ex_intro _ x _).
  unfold valley.
  intros.
  transitivity 0.
  - exact (proj1 (Nat.le_0_r _) (px y H)).
  - symmetry.
    exact (proj1 (Nat.le_0_r _) (px x (le_n x))).
Qed.

Lemma valley_continues_or_bound_decreases:
  forall f n x m,
  decr f ->
  f x = m -> valley f n x ->
  valley f (S n) x \/ (eventually_bounded_by f (pred m)).
Proof.
  intros.
  case (Nat.eq_dec (f (x + S n)) m).
  + intro.
    left.
    unfold valley.
    intros y G0 G1.
    assert (x + S n = S (x + n)). { apply eq_sym; trivial. }
    rewrite H2 in G1.
    case (leq_and_not _ _ G1).
    - intro.
      rewrite H3.
      rewrite <- H2.
      transitivity m.
      * assumption.
      * symmetry.
        assumption.
    - intro.
      exact (H1 _ G0 H3).
  + intro.
    right.
    refine (ex_intro _ (x + S n) _).
    intros y H2.
    pose (p := H1 (x + n) (Nat.le_add_r _ _) (le_n _)).
    rewrite H0 in p.
    pose (q := decr_estimate _ H _ _ (proj1 (Nat.add_le_mono_l _ _ x) (le_S n n (le_n _)))).
    rewrite p in q.
    exact (Nat.le_trans _ _ _ (decr_estimate _ H _ _ H2) (leq_and_not'' _ _ q n0)).
Qed.

Lemma decr_and_eventually_bounded_by:
  forall f n m x,
  decr f ->
  eventually_bounded_by_at f (S m) x ->
  valley f n x \/ (eventually_bounded_by f m).
Proof.
  intro f.
  induction n.
  + intros.
    left.
    unfold valley.
    intros y H1 H2.
    assert (x = y).
    - rewrite <- plus_n_O in H2.
      exact (Nat.le_antisymm _ _ H1 H2).
    - rewrite H3.
      reflexivity.
  + intros m x D pb.
    case (IHn m x D pb).
    - intro.
      case (valley_continues_or_bound_decreases f n x (f x) D eq_refl H).
      * apply or_introl.
      * intros H1.
        right.
        destruct H1 as [x0 px0].
        refine (ex_intro _ x0 _).
        intros y H1.
        exact (Nat.le_trans _ _ _ (px0 y H1) (Nat.pred_le_mono _ _ (pb x (le_n _)))).
    - apply or_intror.
Qed.

Lemma decr_valleys_lemma:
  forall m f,
  eventually_bounded_by f m -> decr f ->
  forall n, exists x, valley f n x.
Proof.
  induction m.
  + intros f eB0 D.
    exact (eventually_bounded_by_0 f eB0).
  + intros f eBSM D n.
    destruct eBSM as [x pb].
    case (decr_and_eventually_bounded_by f n m x D pb).
    - intro.
      refine (ex_intro _ x _).
      assumption.
    - intro eBM.
      exact (IHm f eBM D n).
Qed.

Theorem decr_valleys: forall n f, decr f -> exists x, valley f n x.
Proof.
  intros.
  destruct (bounded_is_eventually_bounded f (decr_is_bounded f H)) as [b pb].
  exact (decr_valleys_lemma b f pb H n).
Qed.
