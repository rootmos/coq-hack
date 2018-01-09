Definition streamless(X : Set) := forall f : nat -> X,
    {i : nat & {j : nat & i <> j /\ f i = f j}}.

Lemma split_sum {X Y}:
  streamless X -> streamless Y ->
  forall f: nat -> X + Y,
  {g: nat -> ((option X)*(option Y)) &
    forall n, match g n with
      | (Some x, None) => f n = inl x
      | (None, Some y) => f n = inr y
      | _ => False end}.
Proof.
  intros sx sy f.
  exists (fun n => match f n with
    | inl x => (Some x, None)
    | inr y => (None, Some y) end
  ).
  intros n. case (f n); intro; reflexivity.
Qed.

Lemma option_streamless {X}: streamless X -> streamless (option X).
Proof.
  intros s fs.
Admitted.

Lemma product_streamless {X Y}: streamless X -> streamless Y -> streamless (X*Y).
Proof.
  intros sx sy f.
Admitted.

Theorem streamless_sum {X Y}:
  streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros sx sy f.
  destruct (split_sum sx sy f) as [g gp].
  pose (s := product_streamless (option_streamless sx) (option_streamless sy)).
  destruct (s g) as [i [j [ne eq]]].
  case_eq (g i). case_eq (g j). intros.
  pose (gi := gp i). pose (gj := gp j).
  rewrite H0 in gi, eq.
  rewrite H in gj, eq.
  destruct o, o0, o1, o2; try contradiction; try discriminate eq;
  injection eq; destruct 1, gj; exists i, j; split; assumption.
Qed.
