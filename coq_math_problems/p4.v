Require Import Fun.

Fixpoint Fin(n : nat) : Set :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Theorem inj_to_surj(n : nat) : forall f : Fin n -> Fin n, inj f -> surj f.
Admitted.

Theorem surj_to_inj(n : nat) : forall f : Fin n -> Fin n, surj f -> inj f.
Admitted.
