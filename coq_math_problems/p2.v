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

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
Admitted.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Proof.
  unfold LPO.
  intros.
Admitted.
