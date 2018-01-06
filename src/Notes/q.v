Lemma l0 {X}: forall P: X -> Prop, (exists x, P x) -> {x | P x}.
Proof.
  intros P e. (* destruct e. (* not ok? *) *)
Admitted.

Lemma l1 {X Y}: forall P: X -> Prop, forall Q: Y -> Prop,
  (exists x, P x) -> {y | Q y}.
Proof.
  intros P Q e. (* destruct e. (* not ok? *) *)
Admitted.

Lemma l2 {X Y}: forall P: X -> Prop, forall Q: Y -> Prop,
  (exists x, P x) -> {y | Q y} -> False.
Proof.
  intros P Q e. destruct e. (* ok *)
Admitted.

Lemma l3 {X}: forall P: X -> Prop, {x | P x} -> (exists x, P x).
Proof.
  intros P e. destruct e. exists x. assumption.
Qed.
