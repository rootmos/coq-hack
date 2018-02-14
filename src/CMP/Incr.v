Require Import PeanoNat.
Require Import Omega.

Definition strict_incr (f: nat -> nat) :=
  forall n, f n < f (S n).

Lemma f_nat_incr {f: nat -> nat}:
  strict_incr f -> forall m, f 0 < f (S m).
Proof.
  intros I.
  induction m; [pose (I 0)|pose (I (S m))]; omega.
Qed.

Lemma f_nat_incr_neq {f: nat -> nat}:
  strict_incr f -> forall {n m}, n <> m -> f n <> f m.
Proof.
  intros I n m.
  case (Nat.compare_spec n m); [now intros| |]; intros t _. 
  + assert (strict_incr (fun i => f (n + i))) as I'.
    { intro i. now replace (n + S i) with (S (n + i)) by omega. }
    replace n with (n + 0) by omega.
    replace m with (n + S (m - n - 1)) by omega.
    apply Nat.lt_neq, (f_nat_incr I').
  + assert (strict_incr (fun i => f (m + i))) as I'.
    { intro i. now replace (m + S i) with (S (m + i)) by omega. }
    replace m with (m + 0) by omega.
    replace n with (m + S (n - m - 1)) by omega.
    apply Nat.neq_sym, Nat.lt_neq, (f_nat_incr I').
Qed.
