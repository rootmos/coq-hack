Require Import PeanoNat.
Require Import CMP.Arith.
Require Import CMP.Bounded.

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

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
