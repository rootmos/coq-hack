Require Import CMP.Decr.

Definition translation(f g:nat -> nat)(n: nat) := forall x, f (x + n) = g x.

Lemma translate: forall f n, exists g, translation f g n.
Proof.
  intros f n.
  refine (ex_intro _ (fun x => f (x + n)) _).
  intro x.
  trivial.
Qed.

Lemma decr_translation: forall f g n, decr f -> translation f g n -> decr g.
Proof.
  intros f g n D tr x.
  unfold decr.
  rewrite <- (tr (S x)).
  rewrite <- (tr x).
  exact (D (x + n)).
Qed.
