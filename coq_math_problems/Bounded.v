Definition bounded_by (f: nat -> nat) (n: nat) := forall x, f x <= n.
Definition bounded (f: nat -> nat) := exists n, bounded_by f n.
