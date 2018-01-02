Require Import PeanoNat.

Definition LPO :=
  forall f : nat -> bool,
  (exists x, f x = true) \/ (forall x, f x = false).

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.
Definition infvalley(f : nat -> nat)(x : nat) := forall y, x <= y -> f y = f x.

Lemma f_bool_to_nat:
  forall f: nat -> bool, exists g: nat -> nat,
  forall n, (f n = true /\ g n = 1) \/ (f n = false /\ g n = 0).
Proof.
  intro f.
  refine (ex_intro _ (fun n => if f n then 1 else 0) _).
  intro n.
  case (f n). +auto. +auto.
Qed.

Definition f_has_a_true(f: nat -> bool) := exists x, f x = true.
Definition f_false(f: nat -> bool) := forall x, f x = false.

Lemma LPO_disjoint f:
  (f_has_a_true f -> ~ f_false f) /\ (f_false f -> ~ f_has_a_true f).
Proof.
  split.
  + intros H G.
    destruct H as [x px].
    rewrite (G x) in px.
    discriminate.
  + intros H G.
    destruct G as [x px].
    rewrite (H x) in px.
    discriminate.
Qed.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
Admitted.

Lemma f_nat_to_bool_if_next_eq:
  forall f: nat -> nat, exists g: nat -> bool,
  forall n, (f n = f (S n) /\ g n = true) \/ (f n <> f (S n) /\ g n = false).
Proof.
  intro f.
  refine (ex_intro _ (fun n => f n =? f (S n)) _).
  intro n.
  case (Nat.eq_dec (f n) (f (S n))).
  + intro H.
    left.
    exact (conj H (proj2 (Nat.eqb_eq _ _) H)).
  + intro H.
    right.
    refine (conj H _).
    case_eq (f n =? f (S n)).
    - intro G; contradiction (proj1 (Nat.eqb_eq _ _) G).
    - trivial.
Qed.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Proof.
Admitted.
