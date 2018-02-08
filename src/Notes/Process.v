Require Import ClassicalUniqueChoice.

Fixpoint Pow {X} (f: X -> X) (x: X) (n: nat) :=
  match n with
  | O => x
  | S m => f (Pow f x m)
  end.

Theorem process {X} {R: X -> X -> Prop}:
  (forall x, exists! y, R x y) ->
  X -> exists f: nat -> X,
  forall n, R (f n) (f (S n)).
Proof.
  intros pr x.
  destruct (unique_choice _ _ _ pr) as [s p].
  exists (Pow s x).
  induction n; apply p.
Qed.

Require Import ClassicalChoice.

Theorem process' {X} {R: X -> X -> Prop}:
  (forall x, exists y, R x y) ->
  X -> exists f: nat -> X,
  forall n, R (f n) (f (S n)).
Proof.
  intros pr x.
  destruct (choice _ pr) as [s p].
  exists (Pow s x).
  induction n; apply p.
Qed.
